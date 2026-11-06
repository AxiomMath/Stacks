module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionCofinalColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetFromCoversTop
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.Topology.Algebra.AdicTopology.EtaleLiftWeakIdealOfDefinition
public import StacksFrontier.Topology.Algebra.AdicTopology.EtaleModWeakIdeal
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample
import all StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale morphisms of affine formal algebraic spaces are completions of étale algebras

Let `S` be a scheme and let `Y = Spf R` be a McQuillan affine formal algebraic space over `S`,
for a weakly admissible topological ring `R`. **Stacks 0AN8** identifies the affine formal
algebraic spaces `X` with a morphism `X ⟶ Y` which is representable by algebraic spaces and
étale with the formal spectra of the completions `A^∧ = lim A ⧸ JA` of étale `R`-algebras `A`,
`J` running over the weak ideals of definition of `R`. This file proves that correspondence: the
formal spectrum of such a completion is representable étale over `Y`, morphisms over `Y` are
`Spf` of unique continuous `R`-algebra maps (Stacks 0AN0), and every such `X` is, over `Y`, the
formal spectrum of the completion of an étale `R`-algebra. In particular `X` is McQuillan.

## Main results

* `RingHom.Etale.existsUnique_lift_of_isLocallyNilpotent`: unique lifting of an étale ring map
  along a surjection with locally nilpotent kernel.
* `AlgebraicGeometry.existsUnique_etale_lift_of_isThickening`: unique lifting of a morphism to
  an étale affine scheme along a thickening of affine schemes, and its version
  `AlgebraicGeometry.BigFppfOver.existsUnique_etale_lift` in the big fppf site.
* `AlgebraicGeometry.FormalSpace.exists_iso_of_stageBaseChange_iso`: two sheaves whose base changes
  to the stages of a universal colimit of affine schemes along thickenings are affine and étale
  over the stages are isomorphic over the colimit as soon as their base changes to one stage
  are.
* `AlgebraicGeometry.FormalSpace.exists_etale_formalSpectrum_iso_of_isRepresentableEtale`:
  essential surjectivity.
* `AlgebraicGeometry.FormalSpace.isEtaleULift_pullback_of_compact_pullback`: étaleness of a
  morphism of fppf sheaves is detected on the points out of quasi-compact objects of the site.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_formalSpectrumMap_completionOver_of_etale`:
  the formal spectrum of the completion of an étale algebra is representable étale over
  `Spf R`.
* `AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_of_formalSpectrumMap_over`: full
  faithfulness over `Spf R`.
* `AlgebraicGeometry.FormalSpace.etaleFormalSpectrum_correspondence`: **Stacks 0AN8**, the three
  clauses together.

## Implementation notes

The source shows that the étale algebras `A ⧸ JA` and the rings of functions of the base
changes `Spec (R ⧸ J) ×_Y X` are isomorphic for each `J`, compatibly in `J`, by the uniqueness of
étale lifts along `R ⧸ J → R ⧸ J₀` (Stacks 0ALI). Here the same uniqueness is used one level
up, on morphisms: both `X` and `Spf A^∧` are colimits of their base changes to the stages of
`Spf R` (the colimit presenting `Spf R` is universal), each base change is an affine scheme
étale over its stage (Stacks 0AKN for `X`, Stacks 0ANM for `Spf A^∧`), and the transition
morphisms between base changes are thickenings, being base changes of the thickenings between
the stages. A morphism over `Spf R` between the base changes at one stage `J₀` therefore extends
uniquely to every stage, and these extensions glue to a morphism over `Spf R`. Applied to the
isomorphism at `J₀` given by the choice of `A` (Stacks 04D1) and to its inverse this gives
morphisms both ways whose composites are identities by uniqueness.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **Unique lifting of an étale ring map along a locally nilpotent surjection.** Given an étale
ring map `ψ : Q → T`, a surjection `φ : R → R₀` with locally nilpotent kernel and a commutative
square `α ∘ ψ = φ ∘ β`, there is a unique `l : T → R` with `l ∘ ψ = β` and `φ ∘ l = α`. -/
theorem RingHom.Etale.existsUnique_lift_of_isLocallyNilpotent {Q T R R₀ : Type*} [CommRing Q]
    [CommRing T] [CommRing R] [CommRing R₀] {ψ : Q →+* T} (hψ : ψ.Etale) {φ : R →+* R₀}
    (hφ : Function.Surjective φ) (hn : (RingHom.ker φ).IsLocallyNilpotent) (α : T →+* R₀)
    (β : Q →+* R) (h : α.comp ψ = φ.comp β) :
    ∃! l : T →+* R, l.comp ψ = β ∧ φ.comp l = α := by
  let := ψ.toAlgebra
  let := β.toAlgebra
  have : Algebra.Etale Q T := hψ
  let e := RingHom.quotientKerEquivOfSurjective hφ
  have he : ∀ x, e (Ideal.Quotient.mk _ x) = φ x := fun x ↦ rfl
  let g : T →ₐ[Q] R ⧸ RingHom.ker φ :=
    { toRingHom := (e.symm : R₀ →+* _).comp α
      commutes' := fun q ↦ by
        show e.symm (α (ψ q)) = Ideal.Quotient.mk _ (β q)
        rw [show α (ψ q) = φ (β q) from RingHom.congr_fun h q, e.symm_apply_eq, he] }
  obtain ⟨l, hl, hu⟩ := Algebra.Etale.existsUnique_lift_of_isLocallyNilpotent hn g
  have hφl : ∀ t, φ (l t) = α t := fun t ↦ by
    have := congrArg (fun k : T →ₐ[Q] R ⧸ RingHom.ker φ ↦ e (k t)) hl
    simpa [g, he] using this
  refine ⟨l.toRingHom, ⟨RingHom.ext fun q ↦ l.commutes q, RingHom.ext hφl⟩, ?_⟩
  rintro l' ⟨h₁, h₂⟩
  let L : T →ₐ[Q] R := { toRingHom := l', commutes' := fun q ↦ RingHom.congr_fun h₁ q }
  have : L = l := hu L (by
    ext t
    apply e.injective
    show e (Ideal.Quotient.mk _ (l' t)) = e (e.symm (α t))
    rw [he, RingEquiv.apply_symm_apply]
    exact RingHom.congr_fun h₂ t)
  exact congrArg AlgHom.toRingHom this

namespace AlgebraicGeometry

/-- **Unique lifting of a morphism to an étale affine scheme along a nilpotent thickening of
spectra.** Let `q : Z ⟶ V` be an étale morphism of affine schemes and let `φ : R → R₀` be a
surjection with locally nilpotent kernel. A morphism `Spec R ⟶ V` whose restriction to
`Spec R₀` lifts to `Z` has a unique lift `Spec R ⟶ Z` extending the given one. -/
@[sga "4 VII 1.1" "special case"]
theorem existsUnique_etale_lift_spec {Z V : Scheme.{u}} [IsAffine Z] [IsAffine V] (q : Z ⟶ V)
    [Etale q] {R R₀ : CommRingCat.{u}} (φ : R ⟶ R₀) (hφ : Function.Surjective φ)
    (hn : (RingHom.ker φ.hom).IsLocallyNilpotent) (a : Spec R₀ ⟶ Z) (b : Spec R ⟶ V)
    (h : a ≫ q = Spec.map φ ≫ b) :
    ∃! l : Spec R ⟶ Z, Spec.map φ ≫ l = a ∧ l ≫ q = b := by
  have hq : (q.appTop).hom.Etale := HasRingHomProperty.appTop @Etale q ‹_›
  let α := Spec.preimage (a ≫ Z.isoSpec.hom)
  let β := Spec.preimage (b ≫ V.isoSpec.hom)
  have hα : Spec.map α = a ≫ Z.isoSpec.hom := Spec.map_preimage _
  have hβ : Spec.map β = b ≫ V.isoSpec.hom := Spec.map_preimage _
  have hsq : q.appTop ≫ α = β ≫ φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hα, hβ, Category.assoc, Scheme.isoSpec_hom_naturality,
      ← Category.assoc, h, Category.assoc]
  obtain ⟨l₀, ⟨hl₁, hl₂⟩, hu⟩ := hq.existsUnique_lift_of_isLocallyNilpotent hφ hn α.hom β.hom
    (congrArg CommRingCat.Hom.hom hsq)
  have e₁ : CommRingCat.ofHom l₀ ≫ φ = α := CommRingCat.hom_ext hl₂
  have e₂ : q.appTop ≫ CommRingCat.ofHom l₀ = β := CommRingCat.hom_ext hl₁
  refine ⟨Spec.map (CommRingCat.ofHom l₀) ≫ Z.isoSpec.inv, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, e₁, hα, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp, e₂,
      hβ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rintro l' ⟨h₁, h₂⟩
    let P := Spec.preimage (l' ≫ Z.isoSpec.hom)
    have hP : Spec.map P = l' ≫ Z.isoSpec.hom := Spec.map_preimage _
    have f₁ : P ≫ φ = α := by
      apply Spec.map_injective
      rw [Spec.map_comp, hP, hα, ← Category.assoc, h₁]
    have f₂ : q.appTop ≫ P = β := by
      apply Spec.map_injective
      rw [Spec.map_comp, hP, hβ, Category.assoc, Scheme.isoSpec_hom_naturality,
        ← Category.assoc, h₂]
    have hPl : P.hom = l₀ := hu P.hom ⟨congrArg CommRingCat.Hom.hom f₂,
      congrArg CommRingCat.Hom.hom f₁⟩
    have : P = CommRingCat.ofHom l₀ := CommRingCat.hom_ext hPl
    rw [← this, hP, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Unique lifting of a morphism to an étale affine scheme along a thickening of affine
schemes.** Let `q : Z ⟶ V` be an étale morphism of affine schemes and let `i : U₀ ⟶ U` be a
thickening of affine schemes, a closed immersion which is surjective on points. A morphism
`U ⟶ V` whose restriction to `U₀` lifts to `Z` has a unique lift `U ⟶ Z` extending the given
one. -/
@[sga "1 I 5.6" "special case"]
theorem existsUnique_etale_lift_of_isThickening {U₀ U Z V : Scheme.{u}} [IsAffine U₀]
    [IsAffine U] [IsAffine Z] [IsAffine V] (i : U₀ ⟶ U) [IsClosedImmersion i]
    (hi : Function.Surjective i.base) (q : Z ⟶ V) [Etale q] (a : U₀ ⟶ Z) (b : U ⟶ V)
    (h : a ≫ q = i ≫ b) :
    ∃! l : U ⟶ Z, i ≫ l = a ∧ l ≫ q = b := by
  have hφ : Function.Surjective i.appTop := (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hn : (RingHom.ker i.appTop.hom).IsLocallyNilpotent := by
    intro x hx
    rw [Scheme.isNilpotent_iff_basicOpen_eq_bot, eq_bot_iff]
    intro y hy
    obtain ⟨y₀, rfl⟩ := hi y
    have : y₀ ∈ i ⁻¹ᵁ U.basicOpen x := hy
    rwa [Scheme.preimage_basicOpen_top, show i.appTop x = 0 from hx, Scheme.basicOpen_zero] at this
  have hsq : Spec.map i.appTop ≫ U.isoSpec.inv = U₀.isoSpec.inv ≫ i :=
    Scheme.isoSpec_inv_naturality i
  obtain ⟨l, ⟨h₁, h₂⟩, hu⟩ := existsUnique_etale_lift_spec q i.appTop hφ hn
    (U₀.isoSpec.inv ≫ a) (U.isoSpec.inv ≫ b)
    (by rw [Category.assoc, h, ← Category.assoc, ← hsq, Category.assoc])
  refine ⟨U.isoSpec.hom ≫ l, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc, h₁,
      Iso.hom_inv_id_assoc]
  · rw [Category.assoc, h₂, Iso.hom_inv_id_assoc]
  · rintro l' ⟨h₁', h₂'⟩
    have : U.isoSpec.inv ≫ l' = l := hu _ ⟨by rw [← Category.assoc, hsq, Category.assoc, h₁'],
      by rw [Category.assoc, h₂']⟩
    rw [← this, Iso.hom_inv_id_assoc]

/-- A morphism of the site lies over the structure morphisms of its source and target, as
morphisms of the underlying schemes included in the site. -/
private theorem toScheme_map_comp_inclusion_map_hom {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : 𝔅.Contains S} {Z V : BigFppfOver 𝔅 S hS} (q : Z ⟶ V) :
    (BigFppfOver.toScheme 𝔅 S hS).map q ≫ 𝔅.inclusion.map V.hom = 𝔅.inclusion.map Z.hom := by
  show 𝔅.inclusion.map q.left ≫ _ = _
  rw [← 𝔅.inclusion.map_comp, Over.w q]

/-- **Unique lifting along a thickening, in the big fppf site.** The morphisms of the site of
`S` between objects with affine underlying schemes satisfy the lifting property of
`AlgebraicGeometry.existsUnique_etale_lift_of_isThickening`: the lift of underlying schemes is a
morphism over `S` because it lies over the morphism `U ⟶ V` of the site. -/
theorem BigFppfOver.existsUnique_etale_lift (𝔅 : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : 𝔅.Contains S) {U₀ U Z V : BigFppfOver 𝔅 S hS}
    [IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj U₀)]
    [IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj Z)]
    [IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj V)] (i : U₀ ⟶ U)
    [IsClosedImmersion ((BigFppfOver.toScheme 𝔅 S hS).map i)]
    (hi : Function.Surjective ((BigFppfOver.toScheme 𝔅 S hS).map i).base) (q : Z ⟶ V)
    [Etale ((BigFppfOver.toScheme 𝔅 S hS).map q)] (a : U₀ ⟶ Z) (b : U ⟶ V)
    (h : a ≫ q = i ≫ b) :
    ∃! l : U ⟶ Z, i ≫ l = a ∧ l ≫ q = b := by
  let T := BigFppfOver.toScheme 𝔅 S hS
  obtain ⟨l, ⟨h₁, h₂⟩, hu⟩ := existsUnique_etale_lift_of_isThickening (T.map i) hi (T.map q)
    (T.map a) (T.map b) (by rw [← T.map_comp, h, T.map_comp])
  refine ⟨BigFppfOver.homOfCompEq 𝔅 S hS l (by
      rw [← toScheme_map_comp_inclusion_map_hom q, ← Category.assoc, h₂,
        toScheme_map_comp_inclusion_map_hom b]),
    ⟨T.map_injective ?_, T.map_injective ?_⟩, ?_⟩
  · rw [T.map_comp, BigFppfOver.toScheme_map_homOfCompEq, h₁]
  · rw [T.map_comp, BigFppfOver.toScheme_map_homOfCompEq, h₂]
  · rintro l' ⟨h₁', h₂'⟩
    apply T.map_injective
    rw [BigFppfOver.toScheme_map_homOfCompEq]
    exact hu _ ⟨by rw [← T.map_comp, h₁'], by rw [← T.map_comp, h₂']⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}


/-- A pullback square of the site is a pullback square of the underlying schemes. -/
private theorem isPullback_toScheme_map {U₀ U V₀ V : BigFppfOver 𝔅 S hS} {i : U₀ ⟶ U}
    {q₀ : U₀ ⟶ V₀} {q : U ⟶ V} {t : V₀ ⟶ V} (h : IsPullback i q₀ q t) :
    IsPullback ((BigFppfOver.toScheme 𝔅 S hS).map i) ((BigFppfOver.toScheme 𝔅 S hS).map q₀)
      ((BigFppfOver.toScheme 𝔅 S hS).map q) ((BigFppfOver.toScheme 𝔅 S hS).map t) := by
  let _ := 𝔅.hasPullbacks_schemes
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.forget 𝔅 S hS) := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan 𝔅.inclusion := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme 𝔅 S hS) :=
      comp_preservesLimitsOfShape _ _
  exact h.map _

/-- A morphism of the site whose sheafified Yoneda image is a base change of the image of a
thickening is a thickening: the sheafified Yoneda embedding reflects fibre products, the
underlying-scheme functor preserves them, and thickenings are stable under base change. -/
theorem isThickening_toScheme_of_isPullback {U₀ U V₀ V : BigFppfOver 𝔅 S hS} {i : U₀ ⟶ U}
    {q₀ : U₀ ⟶ V₀} {q : U ⟶ V} {t : V₀ ⟶ V}
    (h : IsPullback ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map i)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map q₀) ((Sheaf.sheafifiedYoneda
            (BigFppfOver.topology 𝔅 S hS)).map q) ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅
                S hS)).map t))
    (ht : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme 𝔅 S hS).map t)) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme 𝔅 S hS).map i) := by
  let FF := sheafifiedYonedaFF 𝔅 S hS
  have := FF.full
  have := FF.faithful
  have hw : i ≫ q = q₀ ≫ t := FF.map_injective (by rw [Functor.map_comp, Functor.map_comp, h.w])
  have hsch := isPullback_toScheme_map (IsPullback.of_map _ hw h)
  have : Surjective ((BigFppfOver.toScheme 𝔅 S hS).map t) := ⟨ht.2⟩
  exact ⟨MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsClosedImmersion) hsch.flip ht.1,
    (MorphismProperty.of_isPullback (P := @Surjective) hsch.flip this).surj⟩

variable {I : Type*} [Category* I] {Δ : I ⥤ BigFppfOver 𝔅 S hS}
  (c : Cocone (Δ ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)))

/-- **Unique lifting on the stages of a base change.** Let `c` present a sheaf as a colimit of
represented objects of the site, and let `p : X ⟶ c.pt` and `p' : X' ⟶ c.pt` be morphisms whose
base changes along the legs of `c` are represented by objects of the site, affine and, for `p`,
étale over the corresponding object. Along a transition `f : I₀ ⟶ J` of the diagram whose
underlying morphism of schemes is a thickening, a morphism to `X` over `c.pt` from the base
change of `X'` to `I₀` extends uniquely to the base change of `X'` to `J`. -/
theorem existsUnique_stageBaseChange_lift
    {X X' : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))}
    {p : X ⟶ c.pt} {p' : X' ⟶ c.pt} {I₀ J : I} (f : I₀ ⟶ J)
    (hf : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme 𝔅 S hS).map (Δ.map f))) (hJ :
        IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj (Δ.obj J)))
    {Z : BigFppfOver 𝔅 S hS} {q : Z ⟶ Δ.obj J} {z : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅
        S hS)).obj Z ⟶ X}
    (hz : IsPullback z ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map q) p (c.ι.app J))
    (hZ : IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj Z)) (hq : Etale ((BigFppfOver.toScheme 𝔅 S
        hS).map q)) {Z₀' Z' : BigFppfOver 𝔅 S hS}
    {q₀' : Z₀' ⟶ Δ.obj I₀} {q' : Z' ⟶ Δ.obj J}
    {z₀' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).obj Z₀' ⟶ X'} {z' :
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).obj Z' ⟶ X'}
    (hz₀' : IsPullback z₀' ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map q₀') p'
        (c.ι.app I₀))
    (hz' : IsPullback z' ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map q') p'
        (c.ι.app J))
    (hZ₀' : IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj Z₀')) (hZ' : IsAffine
        ((BigFppfOver.toScheme 𝔅 S hS).obj Z'))
    (tr : pullback (c.ι.app I₀) p' ⟶ pullback (c.ι.app J) p')
    (htr₁ : tr ≫ pullback.fst _ _ = pullback.fst _ _ ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map (Δ.map f))
    (htr₂ : tr ≫ pullback.snd _ _ = pullback.snd _ _)
    (a : pullback (c.ι.app I₀) p' ⟶ X) (ha : a ≫ p = pullback.fst _ _ ≫ c.ι.app I₀) :
    ∃! l : pullback (c.ι.app J) p' ⟶ X, tr ≫ l = a ∧ l ≫ p = pullback.fst _ _ ≫ c.ι.app J := by
  classical
  let FF := sheafifiedYonedaFF 𝔅 S hS
  let t := Δ.map f
  have ht : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map t ≫ c.ι.app J = c.ι.app I₀
      := c.w f
  let e₀ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).obj Z₀' ≅ Limits.pullback
      (c.ι.app I₀) p' := hz₀'.flip.isoPullback
  let e : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).obj Z' ≅ Limits.pullback (c.ι.app
      J) p' := hz'.flip.isoPullback
  have he₀f : e₀.hom ≫ pullback.fst _ _ = (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S
      hS)).map q₀' := hz₀'.flip.isoPullback_hom_fst
  have he₀s : e₀.hom ≫ pullback.snd _ _ = z₀' := hz₀'.flip.isoPullback_hom_snd
  have hef : e.hom ≫ pullback.fst _ _ = (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
      q' := hz'.flip.isoPullback_hom_fst
  have hes : e.hom ≫ pullback.snd _ _ = z' := hz'.flip.isoPullback_hom_snd
  -- the transition between the two representing objects
  let u := FF.preimage (e₀.hom ≫ tr ≫ e.inv)
  have hu : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map u = e₀.hom ≫ tr ≫ e.inv :=
      FF.map_preimage _
  have hu₁ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map u ≫ (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology 𝔅 S hS)).map q' = (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S
          hS)).map q₀' ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map t := by
    rw [hu, Category.assoc, Category.assoc, ← hef, Iso.inv_hom_id_assoc, htr₁,
      ← Category.assoc, he₀f]
  have hu₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map u ≫ z' = z₀' := by
    rw [hu, Category.assoc, Category.assoc, ← hes, Iso.inv_hom_id_assoc, htr₂, he₀s]
  have hpb : IsPullback ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map u)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map q₀') ((Sheaf.sheafifiedYoneda
          (BigFppfOver.topology 𝔅 S hS)).map q') ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S
              hS)).map t) := by
    refine IsPullback.of_right ?_ hu₁ hz'
    rwa [hu₂, ht]
  have hthick := isThickening_toScheme_of_isPullback hpb hf
  have := hthick.1
  -- the morphism to be extended, as a morphism of the site
  have ha' : (e₀.hom ≫ a) ≫ p = (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map (q₀' ≫
      t) ≫ c.ι.app J := by
    rw [Category.assoc, ha, ← Category.assoc, he₀f, Functor.map_comp, Category.assoc, ht]
  have hlift : ∀ {V : BigFppfOver 𝔅 S hS} (v : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology 𝔅 S hS)).obj V ⟶ X) (w : V ⟶ Δ.obj J),
      v ≫ p = (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map w ≫ c.ι.app J →
      ∃ n : V ⟶ Z, (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map n ≫ z = v ∧
        n ≫ q = w :=
    fun v w hv ↦ ⟨FF.preimage (hz.lift v _ hv), by rw [FF.map_preimage]; exact hz.lift_fst _ _ _,
      FF.map_injective (by rw [Functor.map_comp, FF.map_preimage]; exact hz.lift_snd _ _ _)⟩
  obtain ⟨a', ha'₁, ha'₂⟩ := hlift _ _ ha'
  obtain ⟨n, ⟨hn₁, hn₂⟩, hnu⟩ := BigFppfOver.existsUnique_etale_lift 𝔅 S hS u hthick.2 q a' q'
    (FF.map_injective (by rw [Functor.map_comp, Functor.map_comp, hu₁, ← Functor.map_comp,
      ha'₂, Functor.map_comp]))
  refine ⟨e.inv ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map n ≫ z, ⟨?_, ?_⟩, ?_⟩
  · have : tr ≫ e.inv = e₀.inv ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map u := by
      rw [hu, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, this, Category.assoc, ← Category.assoc ((Sheaf.sheafifiedYoneda
        (BigFppfOver.topology 𝔅 S hS)).map u), ← Functor.map_comp,
      hn₁, ha'₁, Iso.inv_hom_id_assoc]
  · rw [Category.assoc, Category.assoc, hz.w, ← Category.assoc ((Sheaf.sheafifiedYoneda
      (BigFppfOver.topology 𝔅 S hS)).map n), ← Functor.map_comp,
      hn₂, ← hef, Category.assoc, Iso.inv_hom_id_assoc]
  · rintro l ⟨hl₁, hl₂⟩
    have hl : (e.hom ≫ l) ≫ p = (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map q' ≫
        c.ι.app J := by
      rw [Category.assoc, hl₂, ← Category.assoc, hef]
    obtain ⟨n', hn'₁, hn'₂⟩ := hlift _ _ hl
    have : n' = n := hnu n' ⟨FF.map_injective (hz.hom_ext (by
        rw [Functor.map_comp, Category.assoc, hn'₁, ha'₁, hu, Category.assoc, Category.assoc,
          Iso.inv_hom_id_assoc, hl₁])
        (by rw [Functor.map_comp, Category.assoc, ← Functor.map_comp _ n', hn'₂, hu₁,
          ← Functor.map_comp, ← ha'₂, Functor.map_comp])),
      hn'₂⟩
    rw [← this, hn'₁, Iso.inv_hom_id_assoc]

/-- The base changes of `x : X ⟶ c.pt` along the legs of `c` are represented by objects of the
site which are affine and étale over the corresponding object of the diagram. -/
abbrev HasAffineEtaleStageBaseChanges {X : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))}
    (x : X ⟶ c.pt) : Prop :=
  ∀ i, ∃ (Z : BigFppfOver 𝔅 S hS) (q : Z ⟶ Δ.obj i) (z : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology 𝔅 S hS)).obj Z ⟶ X),
    IsPullback z ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map q) x (c.ι.app i) ∧
        IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj Z) ∧ Etale ((BigFppfOver.toScheme 𝔅 S hS).map q)

/-- A morphism to `Y` over `c.pt` out of the base change of `x` at `j` restricts along a
transition of base changes to a morphism over `c.pt` out of the base change at `k`. -/
private theorem comp_transition_comp_eq {Y : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))}
    {X : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))} {x : X ⟶ c.pt} {y : Y ⟶ c.pt}
    {k j : I} (f : k ⟶ j) {tr : pullback (c.ι.app k) x ⟶ pullback (c.ι.app j) x}
    (htr₁ : tr ≫ pullback.fst _ _ = pullback.fst _ _ ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map (Δ.map f))
    {l : pullback (c.ι.app j) x ⟶ Y} (hl : l ≫ y = pullback.fst _ _ ≫ c.ι.app j) :
    (tr ≫ l) ≫ y = pullback.fst _ _ ≫ c.ι.app k := by
  rw [Category.assoc, hl, ← Category.assoc, htr₁, Category.assoc]
  exact congrArg (pullback.fst _ _ ≫ ·) (c.w f)

/-- The transition between the base changes of `x` along the legs of `c` at `k` and `j`. -/
private abbrev stageTransition {X : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))}
    (x : X ⟶ c.pt) {k j : I} (f : k ⟶ j) :
    pullback (c.ι.app k) x ⟶ pullback (c.ι.app j) x :=
  (Limits.baseChangeDiagram c x).map f

private theorem stageTransition_fst {X : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))}
    (x : X ⟶ c.pt) {k j : I} (f : k ⟶ j) : stageTransition c x f ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map (Δ.map f) :=
  baseChangeDiagram_map_fst c x f

private theorem stageTransition_snd {X : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))}
    (x : X ⟶ c.pt) {k j : I} (f : k ⟶ j) :
    stageTransition c x f ≫ pullback.snd _ _ = pullback.snd _ _ :=
  baseChangeDiagram_map_snd c x f

/-- Pullbacks of fppf sheaves, found directly (instance search through a preorder index category
otherwise times out). -/
local instance (priority := high) hasPullbacks_sheaf_etaleCompletionSpectrum :
    HasPullbacks (Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))) :=
  inferInstance

/-- Limits of cospans of fppf sheaves, found directly. -/
local instance (priority := high) hasLimit_cospan_sheaf_etaleCompletionSpectrum
    {X Y Z : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Glueing

variable {I : Type*} [Preorder I] {Δ : I ⥤ BigFppfOver 𝔅 S hS}
  {c : Cocone (Δ ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS))}
  (hΔ : ∀ i, IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj (Δ.obj i)))
  (hthick : ∀ ⦃i j : I⦄ (f : i ⟶ j), Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme 𝔅 S
      hS).map (Δ.map f)))
  {X Y : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))} {x : X ⟶ c.pt} {y : Y ⟶ c.pt}
  (hx : HasAffineEtaleStageBaseChanges c x) (hy : HasAffineEtaleStageBaseChanges c y)
include hΔ hthick hx hy

/-- Two morphisms over `c.pt` from the base change of `x` at `j` to `Y` agreeing on the base
change at a smaller index agree. -/
theorem stageBaseChange_hom_ext {k j : I} (f : k ⟶ j)
    (tr : pullback (c.ι.app k) x ⟶ pullback (c.ι.app j) x)
    (htr₁ : tr ≫ pullback.fst _ _ = pullback.fst _ _ ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map (Δ.map f))
    (htr₂ : tr ≫ pullback.snd _ _ = pullback.snd _ _)
    {l₁ l₂ : pullback (c.ι.app j) x ⟶ Y} (h₁ : l₁ ≫ y = pullback.fst _ _ ≫ c.ι.app j)
    (h₂ : l₂ ≫ y = pullback.fst _ _ ≫ c.ι.app j) (h : tr ≫ l₁ = tr ≫ l₂) : l₁ = l₂ := by
  obtain ⟨Z, q, z, hz, hZ, hq⟩ := hy j
  obtain ⟨Z₀', q₀', z₀', hz₀', hZ₀', -⟩ := hx k
  obtain ⟨Z', q', z', hz', hZ', -⟩ := hx j
  exact (existsUnique_stageBaseChange_lift c f (hthick f) (hΔ j) hz hZ hq hz₀' hz' hZ₀' hZ' tr htr₁
    htr₂ _ (comp_transition_comp_eq c f htr₁ h₁)).unique ⟨rfl, h₁⟩ ⟨h.symm, h₂⟩

variable (hlow : ∀ i j : I, ∃ k, k ≤ i ∧ k ≤ j)
include hlow

/-- **Glueing a morphism over `c.pt` from a seed.** A morphism over `c.pt` from the base change
of `x` at `i₀` to `Y` extends to a morphism `X ⟶ Y` over `c.pt`, the transitions of the diagram
being thickenings and `c` a universal colimit. -/
theorem exists_hom_of_stageBaseChange (hc : IsUniversalColimit c) (i₀ : I)
    (σ : pullback (c.ι.app i₀) x ⟶ Y) (hσ : σ ≫ y = pullback.fst _ _ ≫ c.ι.app i₀) :
    ∃ l : X ⟶ Y, l ≫ y = x ∧ pullback.snd (c.ι.app i₀) x ≫ l = σ := by
  classical
  let G := Limits.baseChangeDiagram c x
  let T : ∀ {k j : I}, (k ⟶ j) → (pullback (c.ι.app k) x ⟶ pullback (c.ι.app j) x) :=
    fun f ↦ stageTransition c x f
  have Tc : ∀ {k j m : I} (f : k ⟶ j) (g : j ⟶ m), T (f ≫ g) = T f ≫ T g :=
    fun f g ↦ G.map_comp f g
  have Ti : ∀ k : I, T (𝟙 k) = 𝟙 _ := fun k ↦ G.map_id k
  have hover : ∀ {k j : I} (f : k ⟶ j) (l : pullback (c.ι.app j) x ⟶ Y),
      l ≫ y = pullback.fst _ _ ≫ c.ι.app j → (T f ≫ l) ≫ y = pullback.fst _ _ ≫ c.ι.app k :=
    fun f l hl ↦ comp_transition_comp_eq c f (stageTransition_fst c x f) hl
  choose k hk₁ hk₂ using fun j ↦ hlow j i₀
  have hlift : ∀ j, ∃! l : pullback (c.ι.app j) x ⟶ Y, T (homOfLE (hk₁ j)) ≫ l =
      T (homOfLE (hk₂ j)) ≫ σ ∧ l ≫ y = pullback.fst _ _ ≫ c.ι.app j := fun j ↦ by
    obtain ⟨Z, q, z, hz, hZ, hq⟩ := hy j
    obtain ⟨Z₀', q₀', z₀', hz₀', hZ₀', -⟩ := hx (k j)
    obtain ⟨Z', q', z', hz', hZ', -⟩ := hx j
    exact existsUnique_stageBaseChange_lift c _ (hthick _) (hΔ j) hz hZ hq hz₀' hz' hZ₀' hZ' _
      (stageTransition_fst c x _)
      (stageTransition_snd c x _) _ (hover _ σ hσ)
  choose l hl hlu using hlift
  -- the lifts restrict to the seed on every index below both `j` and `i₀`
  have hseed : ∀ {m j : I} (hmj : m ≤ j) (hmi : m ≤ i₀),
      T (homOfLE hmj) ≫ l j = T (homOfLE hmi) ≫ σ := by
    intro m j hmj hmi
    obtain ⟨n, hn₁, hn₂⟩ := hlow m (k j)
    refine stageBaseChange_hom_ext hΔ hthick hx hy (homOfLE hn₁) _ (stageTransition_fst c x _)
      (stageTransition_snd c x _)
      (hover _ _ (hl j).2) (hover _ _ hσ) ?_
    rw [← Category.assoc, ← Tc, ← Category.assoc, ← Tc,
      show homOfLE hn₁ ≫ homOfLE hmj = homOfLE hn₂ ≫ homOfLE (hk₁ j) from rfl, Tc,
      Category.assoc, (hl j).1, ← Category.assoc, ← Tc]
    rfl
  have hcompat : ∀ {j j' : I} (g : j ⟶ j'), T g ≫ l j' = l j := by
    intro j j' g
    refine stageBaseChange_hom_ext hΔ hthick hx hy (homOfLE (hk₁ j)) _ (stageTransition_fst c x _)
      (stageTransition_snd c x _) (hover g _ (hl j').2) (hl j).2 ?_
    rw [← Category.assoc, ← Tc, (hl j).1]
    exact hseed _ _
  let hcol := isColimitBaseChangeCocone c x hc
  let s : Cocone G := ⟨Y, ⟨fun j ↦ l j, fun j j' g ↦
    (hcompat g).trans (Category.comp_id _).symm⟩⟩
  have hfac : ∀ j, pullback.snd (c.ι.app j) x ≫ hcol.desc s = l j := fun j ↦ hcol.fac s j
  refine ⟨hcol.desc s, ?_, ?_⟩
  · refine hcol.hom_ext fun j ↦ ?_
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ y) (hfac j))).trans
      ((hl j).2.trans pullback.condition)
  · have h := hseed (le_refl i₀) (le_refl i₀)
    rw [show (homOfLE (le_refl i₀) : i₀ ⟶ i₀) = 𝟙 i₀ from rfl, Ti, Category.id_comp,
      Category.id_comp] at h
    exact (hfac i₀).trans h

/-- Two morphisms `X ⟶ Y` over `c.pt` agreeing on the base change of `x` at `i₀` are equal. -/
theorem hom_ext_of_stageBaseChange (hc : IsUniversalColimit c) (i₀ : I) {l₁ l₂ : X ⟶ Y}
    (h₁ : l₁ ≫ y = x) (h₂ : l₂ ≫ y = x)
    (h : pullback.snd (c.ι.app i₀) x ≫ l₁ = pullback.snd (c.ι.app i₀) x ≫ l₂) : l₁ = l₂ := by
  refine (isColimitBaseChangeCocone c x hc).hom_ext fun j ↦ ?_
  show pullback.snd (c.ι.app j) x ≫ l₁ = pullback.snd (c.ι.app j) x ≫ l₂
  obtain ⟨k, hk₁, hk₂⟩ := hlow j i₀
  have hov : ∀ l : X ⟶ Y, l ≫ y = x →
      (pullback.snd (c.ι.app j) x ≫ l) ≫ y = pullback.fst _ _ ≫ c.ι.app j := fun l hl ↦ by
    rw [Category.assoc, hl, ← pullback.condition]
  refine stageBaseChange_hom_ext hΔ hthick hx hy (homOfLE hk₁) (stageTransition c x _)
    (stageTransition_fst c x _) (stageTransition_snd c x _) (hov l₁ h₁) (hov l₂ h₂) ?_
  rw [← Category.assoc, stageTransition_snd, ← Category.assoc, stageTransition_snd,
    ← stageTransition_snd c x (homOfLE hk₂), Category.assoc, h, ← Category.assoc,
    stageTransition_snd]

/-- **Two sheaves affine étale over the stages of a universal colimit are isomorphic over it as
soon as their base changes to a single stage are.** The isomorphism at the stage `i₀` glues to
morphisms in both directions by `AlgebraicGeometry.FormalSpace.exists_hom_of_stageBaseChange`, and
the two composites are identities by `AlgebraicGeometry.FormalSpace.hom_ext_of_stageBaseChange`. -/
theorem exists_iso_of_stageBaseChange_iso (hc : IsUniversalColimit c) (i₀ : I)
    (e₀ : pullback (c.ι.app i₀) x ≅ pullback (c.ι.app i₀) y)
    (he₀ : e₀.hom ≫ pullback.fst _ _ = pullback.fst _ _) :
    ∃ t : X ≅ Y, t.hom ≫ y = x := by
  have he₀' : e₀.inv ≫ pullback.fst _ _ = pullback.fst _ _ := by
    rw [← he₀, Iso.inv_hom_id_assoc]
  obtain ⟨l, hl₁, hl₂⟩ := exists_hom_of_stageBaseChange hΔ hthick hx hy hlow hc i₀
    (e₀.hom ≫ pullback.snd _ _) (by rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      he₀])
  obtain ⟨m, hm₁, hm₂⟩ := exists_hom_of_stageBaseChange hΔ hthick hy hx hlow hc i₀
    (e₀.inv ≫ pullback.snd _ _) (by rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      he₀'])
  refine ⟨⟨l, m, ?_, ?_⟩, hl₁⟩
  · refine hom_ext_of_stageBaseChange hΔ hthick hx hx hlow hc i₀ (by rw [Category.assoc, hm₁, hl₁])
      (Category.id_comp _) ?_
    rw [← Category.assoc, hl₂, Category.assoc, hm₂, Iso.hom_inv_id_assoc, Category.comp_id]
  · refine hom_ext_of_stageBaseChange hΔ hthick hy hy hlow hc i₀ (by rw [Category.assoc, hl₁, hm₁])
      (Category.id_comp _) ?_
    rw [← Category.assoc, hm₂, Category.assoc, hl₂, Iso.inv_hom_id_assoc, Category.comp_id]

end Glueing

/-- An isomorphism of the underlying schemes of two objects of the big fppf site of `S` which
commutes with their structure morphisms is the underlying isomorphism of an isomorphism of the
site. -/
theorem BigFppfOver.exists_iso_of_toScheme_iso {U W : BigFppfOver 𝔅 S hS}
    (e : (BigFppfOver.toScheme 𝔅 S hS).obj U ≅ (BigFppfOver.toScheme 𝔅 S hS).obj W)
    (h : e.hom ≫ 𝔅.inclusion.map W.hom = 𝔅.inclusion.map U.hom) :
    ∃ m : U ≅ W, (BigFppfOver.toScheme 𝔅 S hS).map m.hom = e.hom := by
  have h' : e.inv ≫ 𝔅.inclusion.map U.hom = 𝔅.inclusion.map W.hom := by
    rw [← h, Iso.inv_hom_id_assoc]
  let T := BigFppfOver.toScheme 𝔅 S hS
  refine ⟨⟨BigFppfOver.homOfCompEq 𝔅 S hS e.hom h, BigFppfOver.homOfCompEq 𝔅 S hS e.inv h',
    T.map_injective ?_, T.map_injective ?_⟩, BigFppfOver.toScheme_map_homOfCompEq 𝔅 S hS e.hom h⟩
  · rw [T.map_comp, BigFppfOver.toScheme_map_homOfCompEq, BigFppfOver.toScheme_map_homOfCompEq,
      Iso.hom_inv_id, T.map_id]
  · rw [T.map_comp, BigFppfOver.toScheme_map_homOfCompEq, BigFppfOver.toScheme_map_homOfCompEq,
      Iso.inv_hom_id, T.map_id]

section Main

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R]

/-- The sum of two weak ideals of definition of a linearly topologized ring is a weak ideal of
definition. -/
theorem _root_.TopologicalRing.isWeakIdealOfDefinition_sup {I J : Ideal R}
    (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    (hJ : TopologicalRing.IsWeakIdealOfDefinition J) :
    TopologicalRing.IsWeakIdealOfDefinition (I ⊔ J) := by
  refine ⟨Submodule.isOpen_mono le_sup_left hI.1, fun x hx ↦ ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  exact (hI.2 a ha).add (hJ.2 b hb)

/-- The map of quotients induced by a ring map equal to the canonical map to the completion of an
étale algebra is étale. -/
private theorem etale_quotientMap_of_eq_canonicalMap {A : Type u} [CommRing A] {f : R →+* A}
    (hf : f.Etale) {φ : R →+* TopologicalRing.CompletionOver f}
    (hφ : φ = TopologicalRing.CompletionOver.canonicalMap f)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex R)
    (h : J.1 ≤ Ideal.comap φ (kerProjectionIdeal f J).1) :
    (Ideal.quotientMap (kerProjectionIdeal f J).1 φ h).Etale := by
  subst hφ
  exact TopologicalRing.CompletionOver.etale_quotientMap_canonicalMap hf J

variable (𝔅 S hS)

/-- **Stacks 0AN8**, essential surjectivity. Let `R` be a weakly admissible topological ring
over `S` and let `p : X ⟶ Spf R` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces and étale. Then there is an étale ring map
`R → A` such that, over `Spf R`, `X` is the formal spectrum of the completion
`A^∧ = lim A ⧸ JA` over the weak ideals of definition `J` of `R`.

Following the source: the base change of `p` to a stage `Spec (R ⧸ J₀)` is an affine scheme
étale over it (Stacks 0AKN), whose ring of functions lifts to an étale `R`-algebra `A`
(Stacks 04D1). The base changes of `Spf A^∧ ⟶ Spf R` to the stages are the spectra of the
`A ⧸ JA` (Stacks 0ANM), and both `X` and `Spf A^∧` are glued from their stagewise base changes
along thickenings, over which morphisms to étale schemes lift uniquely (Stacks 0ALI). -/
theorem exists_etale_formalSpectrum_iso_of_isRepresentableEtale
    (hR : TopologicalRing.IsWeaklyAdmissible R) (D : QuotientSystem 𝔅 S hS R)
    (hY : IsAffineFormalAlgebraicSpace 𝔅 S hS (formalSpectrum D))
    {X : FppfSheaf 𝔅 S hS} (hX : IsAffineFormalAlgebraicSpace 𝔅 S hS X)
    (p : X ⟶ formalSpectrum D) (hp : IsRepresentableEtale 𝔅 S hS p) :
    ∃ (A : Type u) (_ : CommRing A) (f : R →+* A), f.Etale ∧
      ∃ (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
        (g : ContinuousHom D E), g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f ∧
          ∃ i : X ≅ formalSpectrum E, p = i.hom ≫ formalSpectrumMap hR g := by
  classical
  let Yo := Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)
  let T := BigFppfOver.toScheme 𝔅 S hS
  let ι := BigAffineFppf.inclusion 𝔅 S hS
  let c : Cocone ((D.diagram ⋙ ι) ⋙ Yo) := colimit.cocone (formalSpectrumDiagram D)
  have hc : IsUniversalColimit c := isUniversalColimit_formalSpectrumDiagram hR.1 D
  have hΔ : ∀ i, IsAffine (T.obj ((D.diagram ⋙ ι).obj i)) := fun i ↦ (D.diagram.obj i).property
  have hthick : ∀ ⦃i j : WeakIdeals R⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening (T.map ((D.diagram ⋙ ι).map f)) :=
    fun _ _ f ↦ D.isThickening_map_diagram f
  have hlow : ∀ i j : WeakIdeals R, ∃ k, k ≤ i ∧ k ≤ j := fun i j ↦
    ⟨OrderDual.toDual ⟨(OrderDual.ofDual i).1 ⊔ (OrderDual.ofDual j).1,
      TopologicalRing.isWeakIdealOfDefinition_sup (OrderDual.ofDual i).2
        (OrderDual.ofDual j).2⟩,
      (le_sup_left : (OrderDual.ofDual i).1 ≤ _), (le_sup_right : (OrderDual.ofDual j).1 ≤ _)⟩
  let chart : AffineEtaleFormalCharts 𝔅 S hS (formalSpectrum D) := ⟨Over.mk p, hX, hp⟩
  have hxp : HasAffineEtaleStageBaseChanges c p := fun i ↦ by
    obtain ⟨d⟩ := nonempty_affineEtaleBaseChange 𝔅 S hS hY (ι.obj (D.diagram.obj i))
      (D.diagram.obj i).property (formalSpectrumInclusion D i) chart
    exact ⟨d.obj, d.proj, d.fst, d.isPullback, d.isAffine, d.etale⟩
  obtain ⟨I₀, hI₀⟩ := hR.1
  let J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R := ⟨I₀, hI₀⟩
  let i₀ : WeakIdeals R := OrderDual.toDual J₀
  -- the base change of `p` to the stage `Spec (R ⧸ I₀)`: an affine scheme étale over it
  obtain ⟨W, π, w, hw, hW, hπ⟩ := hxp i₀
  let Z₀ := T.obj W
  have : IsAffine Z₀ := hW
  let q₀ : Z₀ ⟶ Spec (.of (R ⧸ I₀)) := T.map π
  have : Etale q₀ := hπ
  -- the étale `R ⧸ I₀`-algebra of functions on it, and its lift to an étale `R`-algebra
  let f₀ : R ⧸ I₀ →+* Γ(Z₀, ⊤) := q₀.appTop.hom.comp (Scheme.ΓSpecIso (.of (R ⧸ I₀))).inv.hom
  have hf₀ : f₀.Etale := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of (R ⧸ I₀))).inv))
    (HasRingHomProperty.appTop @Etale q₀ ‹_›)
  let : Algebra (R ⧸ I₀) Γ(Z₀, ⊤) := f₀.toAlgebra
  let : Algebra R Γ(Z₀, ⊤) := (f₀.comp (Ideal.Quotient.mk I₀)).toAlgebra
  have : IsScalarTower R (R ⧸ I₀) Γ(Z₀, ⊤) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale (R ⧸ I₀) Γ(Z₀, ⊤) := hf₀
  obtain ⟨A, _, _, hA, ψ, hψ, hker⟩ :=
    etale_lift_along_surjection R (R ⧸ I₀) Γ(Z₀, ⊤) Ideal.Quotient.mk_surjective
  let f : R →+* A := algebraMap R A
  have hf : f.Etale := RingHom.etale_algebraMap.mpr hA
  obtain ⟨E, g, hg⟩ := exists_completionOver_quotientSystem_of_finiteType 𝔅 S hS f
    (RingHom.finiteType_algebraMap.mpr inferInstance) hR D
  refine ⟨A, inferInstance, f, hf, E, g, hg, ?_⟩
  -- the base changes of `Spf A^∧ ⟶ Spf R` to the stages are the spectra of the `A ⧸ JA`
  let K : WeakIdeals R → WeakIdeals (TopologicalRing.CompletionOver f) :=
    fun i ↦ OrderDual.toDual (kerProjectionIdeal f (OrderDual.ofDual i))
  have hle : ∀ i : WeakIdeals R,
      (OrderDual.ofDual i).1 ≤ Ideal.comap g.toRingHom (OrderDual.ofDual (K i)).1 :=
    fun i ↦ le_comap_kerProjectionIdeal f g hg _
  have hxg : HasAffineEtaleStageBaseChanges c (formalSpectrumMap hR g) := fun i ↦
    ⟨ι.obj (E.diagram.obj (K i)), ι.map (g.stageMap _ _ (hle i)),
      formalSpectrumInclusion E (K i),
      (isPullback_formalSpectrumMap_kerProjection f hR g hg _ (hle i)).flip,
      (E.diagram.obj (K i)).property,
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
        (etale_quotientMap_of_eq_canonicalMap hf hg _ (hle i))⟩
  -- the identification of the two base changes to `Spec (R ⧸ I₀)`
  let C := TopologicalRing.CompletionOver f
  let K₀ : Ideal C := (OrderDual.ofDual (K i₀)).1
  have hker' : RingHom.ker (ψ : A →+* Γ(Z₀, ⊤)) = TopologicalRing.extendedIdeal f J₀ := by
    rw [hker, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  let e₁ : A ⧸ TopologicalRing.extendedIdeal f J₀ ≃+* Γ(Z₀, ⊤) :=
    (Ideal.quotEquivOfEq hker'.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)
  let θ : Γ(Z₀, ⊤) ≃+* C ⧸ K₀ := e₁.symm.trans (quotientKerProjectionRingEquiv f J₀).symm
  have hθ : θ.toRingHom.comp f₀ = Ideal.quotientMap K₀ g.toRingHom (hle i₀) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ ?_)
    show (quotientKerProjectionRingEquiv f J₀).symm (e₁.symm (algebraMap R Γ(Z₀, ⊤) r)) =
      Ideal.Quotient.mk (kerProjectionIdeal f J₀).1 (g.toRingHom r)
    rw [RingEquiv.symm_apply_eq, quotientKerProjectionRingEquiv_mk, hg,
      TopologicalRing.CompletionOver.projection_canonicalMap, RingEquiv.symm_apply_eq,
      ← ψ.commutes r]
    rfl
  let es : Spec (.of (C ⧸ K₀)) ≅ Z₀ :=
    Scheme.Spec.mapIso θ.toCommRingCatIso.op ≪≫ Z₀.isoSpec.symm
  have hes : es.hom ≫ q₀ = Spec.map (CommRingCat.ofHom (Ideal.quotientMap K₀ g.toRingHom
      (hle i₀))) := by
    show (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ Z₀.isoSpec.inv) ≫ q₀ = _
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp, ← Spec.map_comp, ← hθ]
    rfl
  let V := ι.obj (D.diagram.obj i₀)
  let Z' := ι.obj (E.diagram.obj (K i₀))
  let st : Z' ⟶ V := ι.map (g.stageMap J₀ _ (hle i₀))
  obtain ⟨m, hm⟩ := BigFppfOver.exists_iso_of_toScheme_iso (U := Z') (W := W) es (by
    rw [← toScheme_map_comp_inclusion_map_hom π, ← Category.assoc]
    exact (congrArg (· ≫ 𝔅.inclusion.map V.hom) hes).trans
      (toScheme_map_comp_inclusion_map_hom st))
  have hmπ : m.hom ≫ π = st := T.map_injective (by rwa [T.map_comp, hm])
  have hzg : IsPullback (formalSpectrumInclusion E (K i₀)) (Yo.map st) (formalSpectrumMap hR g)
      (c.ι.app i₀) := (isPullback_formalSpectrumMap_kerProjection f hR g hg _ (hle i₀)).flip
  let e₀ : pullback (c.ι.app i₀) (formalSpectrumMap hR g) ≅ pullback (c.ι.app i₀) p :=
    hzg.flip.isoPullback.symm ≪≫ Yo.mapIso m ≪≫ hw.flip.isoPullback
  have he₀ : e₀.hom ≫ pullback.fst _ _ = pullback.fst _ _ := by
    show (hzg.flip.isoPullback.inv ≫ Yo.map m.hom ≫ hw.flip.isoPullback.hom) ≫
      pullback.fst _ _ = _
    rw [Category.assoc, Category.assoc, hw.flip.isoPullback_hom_fst, ← Functor.map_comp, hmπ,
      hzg.flip.isoPullback_inv_fst]
    rfl
  obtain ⟨t, ht⟩ := exists_iso_of_stageBaseChange_iso hΔ hthick hxg hxp hlow hc i₀ e₀ he₀
  exact ⟨t.symm, (Iso.inv_hom_id_assoc t p).symm.trans (congrArg (t.inv ≫ ·) ht)⟩

end Main

section Forward

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R]

/-- **Étaleness is detected on the quasi-compact points of the target.** A morphism of fppf
sheaves whose base change along every point out of a quasi-compact object of the site is
represented by an object of the site, étale over that object, is étale after base change along
every scheme-valued point. -/
theorem isEtaleULift_pullback_of_compact_pullback {X Y : FppfSheaf 𝔅 S hS} (Φ : X ⟶ Y)
    (h : CompactPullbackRepresentable 𝔅 S hS Φ)
    (het : ∀ (U : BigFppfOver 𝔅 S hS), CompactSpace ((BigFppfOver.toScheme 𝔅 S hS).obj U) →
      ∀ (ξ : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj U ⟶ Y)
        (W : BigFppfOver 𝔅 S hS) (p : W ⟶ U)
        (r : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj W ⟶ X),
        IsPullback r ((BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.map p) Φ ξ →
        Etale ((BigFppfOver.toScheme 𝔅 S hS).map p))
    (T : BigFppfOver 𝔅 S hS) (ξp : (uliftYoneda.{u + 1}).obj T ⟶ Y.obj) :
    Space.IsEtaleULift.{u + 1} 𝔅 S hS (pullback.fst ξp Φ.hom) := by
  classical
  let := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
  have hsize : CompactPullbackRepresentableOfSizeLe 𝔅 S hS @Etale.{u} Φ := fun U hU ξ ↦ by
    obtain ⟨W, p, r, hpb, -, hsz⟩ :=
      compactPullbackRepresentableOfSizeLe_of_compactPullbackRepresentable 𝔅 S hS h U hU ξ
    exact ⟨W, p, r, hpb, het U hU ξ W p r hpb, hsz⟩
  obtain ⟨V, V', q, k, r, hqsurj, hqet, hket, hsq⟩ :=
    exists_surjective_etale_cover_isPullback_of_compact_pullback 𝔅 S hS @Etale.{u} Φ hsize T ⟨ξp⟩
  have hpre := hsq.map (sheafToPresheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1)))
  have hcond : ((uliftYoneda.{u + 1}).map k ≫ (uliftYoneda.{u + 1}).map q) ≫ ξp =
      r.hom ≫ Φ.hom := by
    rw [Category.assoc]
    exact hpre.w.symm
  let a : (uliftYoneda.{u + 1}).obj V' ⟶ pullback ξp Φ.hom :=
    pullback.lift ((uliftYoneda.{u + 1}).map k ≫ (uliftYoneda.{u + 1}).map q) r.hom hcond
  have hafst : a ≫ pullback.fst ξp Φ.hom =
      (uliftYoneda.{u + 1}).map k ≫ (uliftYoneda.{u + 1}).map q := pullback.lift_fst _ _ _
  have hasnd : a ≫ pullback.snd ξp Φ.hom = r.hom := pullback.lift_snd _ _ _
  have htop : IsPullback a ((uliftYoneda.{u + 1}).map k) (pullback.fst ξp Φ.hom)
      ((uliftYoneda.{u + 1}).map q) := by
    refine IsPullback.of_right ?_ hafst (IsPullback.of_hasPullback ξp Φ.hom).flip
    rwa [hasnd]
  refine isEtaleULift_of_targetChart 𝔅 S hS (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1}
    𝔅 S hS T) _ V ((uliftYoneda.{u + 1}).map q)
    (Space.relative_uliftYoneda_map 𝔅 S hS (@Surjective.{u}) q hqsurj)
    (Space.relative_uliftYoneda_map 𝔅 S hS (@Etale.{u}) q hqet) ?_
  have e : pullback.fst ((uliftYoneda.{u + 1}).map q) (pullback.fst ξp Φ.hom) =
      htop.flip.isoPullback.inv ≫ (uliftYoneda.{u + 1}).map k :=
    (Iso.inv_hom_id_assoc htop.flip.isoPullback _).symm.trans
      (congrArg (htop.flip.isoPullback.inv ≫ ·) htop.flip.isoPullback_hom_fst)
  rw [e]
  exact isEtaleULift_precomp_iso 𝔅 S hS htop.flip.isoPullback.symm _
    ((Space.isEtaleULift_uliftYoneda_map_iff 𝔅 S hS k).mpr hket)

variable (𝔅 S hS)

/-- Two objects of the site representing the base change of `Φ` along the same point are
isomorphic over that point. -/
theorem exists_iso_of_isPullback_uliftYoneda {X Y : FppfSheaf 𝔅 S hS} {Φ : X ⟶ Y}
    {U W W' : BigFppfOver 𝔅 S hS} {ξ : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj U ⟶ Y}
    {p : W ⟶ U} {p' : W' ⟶ U}
    {r : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj W ⟶ X}
    {r' : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj W' ⟶ X}
    (h : IsPullback r ((BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.map p) Φ ξ)
    (h' : IsPullback r' ((BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.map p') Φ ξ) :
    ∃ e : W ≅ W', (BigFppfOver.toScheme 𝔅 S hS).map e.hom ≫
      (BigFppfOver.toScheme 𝔅 S hS).map p' = (BigFppfOver.toScheme 𝔅 S hS).map p := by
  let _ : (BigFppfOver.topology 𝔅 S hS).Subcanonical := bigFppfOver_subcanonical 𝔅 S hS
  let FF := GrothendieckTopology.fullyFaithfulUliftYoneda.{u + 1} (BigFppfOver.topology 𝔅 S hS)
  refine ⟨FF.preimageIso (h.isoIsPullback _ _ h'), ?_⟩
  rw [← Functor.map_comp]
  congr 1
  apply FF.map_injective
  rw [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom, FF.map_preimage]
  exact h.isoIsPullback_hom_snd _ _ h'

/-- **Stacks 0AN8**, the functor: for an étale ring map `f : R → A` out of a weakly admissible
topological ring over `S`, the morphism `Spf A^∧ ⟶ Spf R` induced by the canonical map to the
completion is representable by algebraic spaces and étale. The source's argument: `R ⧸ J → A ⧸ JA`
is étale for every weak ideal of definition `J`, and the base change of `Spf A^∧ ⟶ Spf R` along a
point out of a quasi-compact scheme is a base change of `Spec (A ⧸ JA) ⟶ Spec (R ⧸ J)`
(Stacks 0AIA, 0ANM); étaleness at an arbitrary point follows by covering it with affine opens. -/
theorem isRepresentableEtale_formalSpectrumMap_completionOver_of_etale
    (hR : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem 𝔅 S hS R) {A : Type u} [CommRing A] (f : R →+* A) (hf : f.Etale)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f)) (g : ContinuousHom D E)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f) :
    IsRepresentableEtale 𝔅 S hS (formalSpectrumMap hR g) := by
  classical
  have hft : f.FiniteType := by
    let := f.toAlgebra
    have : Algebra.Etale R A := hf
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  let J := BigFppfOver.topology 𝔅 S hS
  let Yo := Sheaf.sheafifiedYoneda J
  let T := BigFppfOver.toScheme 𝔅 S hS
  let ι := BigAffineFppf.inclusion 𝔅 S hS
  refine ⟨isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_completionOver f hR hft D E g
    hg, fun U ξ ↦ isEtaleULift_pullback_of_compact_pullback _
      (compactPullbackRepresentable_formalSpectrumMap_completionOver f hR hft D E g hg) ?_ U ξ⟩
  intro U hU ξ W p r hpb
  let _ : J.Subcanonical := bigFppfOver_subcanonical 𝔅 S hS
  let η := Sheaf.uliftYonedaIsoSheafifiedYoneda J
  obtain ⟨I, p₀, hp₀⟩ := exists_factorsThroughStage_of_compactSpace hR.1 D U hU ((η.app U).inv ≫ ξ)
  have hJK := le_comap_kerProjectionIdeal f g hg I
  let sm := ι.map (g.stageMap I (kerProjectionIdeal f I) hJK)
  have hsm : Etale (T.map sm) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (etale_quotientMap_of_eq_canonicalMap hf hg _ hJK)
  -- the base change, as a fibre product of the site
  let _ : PreservesLimitsOfShape WalkingCospan Yo :=
    have := Sheaf.preservesFiniteLimits_sheafifiedYoneda J
    inferInstance
  have hsy := (IsPullback.of_hasPullback p₀ sm).map Yo
  have h0 := isPullback_formalSpectrumMap_kerProjection f hR g hg I hJK
  have hmain := hsy.flip.paste_horiz h0.flip
  have hnat : (η.app (pullback p₀ sm)).hom ≫ Yo.map (pullback.fst p₀ sm) =
      J.uliftYoneda.{u + 1}.map (pullback.fst p₀ sm) ≫ (η.app U).hom :=
    (η.hom.naturality _).symm
  have hleft : IsPullback (η.app (pullback p₀ sm)).hom (J.uliftYoneda.{u + 1}.map
      (pullback.fst p₀ sm)) (Yo.map (pullback.fst p₀ sm)) (η.app U).hom :=
    IsPullback.of_horiz_isIso ⟨hnat⟩
  have hmine := hleft.paste_horiz hmain
  have hξ : (η.app U).hom ≫ Yo.map p₀ ≫ formalSpectrumInclusion D (OrderDual.toDual I) = ξ :=
    (congrArg ((η.app U).hom ≫ ·) hp₀).trans (Iso.hom_inv_id_assoc _ _)
  rw [hξ] at hmine
  obtain ⟨e, he⟩ := exists_iso_of_isPullback_uliftYoneda 𝔅 S hS hpb hmine
  have hfst : Etale (T.map (pullback.fst p₀ sm)) :=
    MorphismProperty.of_isPullback (P := @Etale)
      (isPullback_toScheme_map (IsPullback.of_hasPullback p₀ sm)).flip hsm
  rw [← he]
  infer_instance

/-- **Stacks 0AN8**, full faithfulness, from Stacks 0AN0: a morphism `Spf A₁^∧ ⟶ Spf A₂^∧` over
`Spf R` between formal spectra of completions of `R`-algebras is `Spf` of a unique continuous ring
map `A₂^∧ → A₁^∧`, and that map is an `R`-algebra map. -/
theorem existsUnique_continuousHom_of_formalSpectrumMap_over
    (hR : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem 𝔅 S hS R) {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    {f₁ : R →+* A₁} {f₂ : R →+* A₂}
    {E₁ : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f₁)}
    {E₂ : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f₂)}
    (g₁ : ContinuousHom D E₁) (g₂ : ContinuousHom D E₂)
    (φ : formalSpectrum E₁ ⟶ formalSpectrum E₂)
    (hφ : φ ≫ formalSpectrumMap hR g₂ = formalSpectrumMap hR g₁) :
    ∃! h : ContinuousHom E₂ E₁, formalSpectrumMap
      (TopologicalRing.completionOver_isWeaklyAdmissible f₂ hR) h = φ ∧
        h.toRingHom.comp g₂.toRingHom = g₁.toRingHom := by
  have hw₁ := TopologicalRing.completionOver_isWeaklyAdmissible f₁ hR
  have hw₂ := TopologicalRing.completionOver_isWeaklyAdmissible f₂ hR
  obtain ⟨h, hh, hu⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hw₂ hw₁ φ
  refine ⟨h, ⟨hh, ?_⟩, fun h' hh' ↦ hu h' hh'.1⟩
  have := (existsUnique_continuousHom_formalSpectrumMap_eq hR hw₁ (formalSpectrumMap hR g₁)).unique
    (y₁ := ContinuousHom.comp hw₂ hR h g₂) (y₂ := g₁)
    (by rw [← formalSpectrumMap_comp_eq, hh, hφ]) rfl
  exact congrArg ContinuousHom.toRingHom this

/-- **Stacks 0AN8.** Let `Y = Spf R` be a McQuillan affine formal algebraic space over `S`, for a
weakly admissible topological ring `R`. Sending the completion `A^∧ = lim A ⧸ JA` of an étale
`R`-algebra `A` to `Spf A^∧ ⟶ Y` is an equivalence between the opposite of the category of such
completions and the category of morphisms `X ⟶ Y` of affine formal algebraic spaces which are
representable by algebraic spaces and étale:

1. the functor is well defined: `Spf A^∧ ⟶ Spf R` is representable by algebraic spaces and
   étale;
2. it is fully faithful: a morphism `Spf A₁^∧ ⟶ Spf A₂^∧` over `Spf R` is `Spf` of a unique
   continuous `R`-algebra map `A₂^∧ → A₁^∧`;
3. it is essentially surjective: every affine formal algebraic space `X` with a morphism
   `X ⟶ Spf R` representable by algebraic spaces and étale is, over `Spf R`, the formal spectrum
   of the completion of an étale `R`-algebra; in particular `X` is McQuillan.

The hypothesis that `Spf R` is an affine formal algebraic space is part of `Y` being a McQuillan
affine formal algebraic space; only the third clause uses it. -/
@[stacks 0AN8]
theorem etaleFormalSpectrum_correspondence (hR : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem 𝔅 S hS R)
    (hY : IsAffineFormalAlgebraicSpace 𝔅 S hS (formalSpectrum D)) :
    (∀ {A : Type u} [CommRing A] (f : R →+* A), f.Etale →
      ∀ (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f)) (g : ContinuousHom D E),
        g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f →
          IsRepresentableEtale 𝔅 S hS (formalSpectrumMap hR g)) ∧
    (∀ {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂] {f₁ : R →+* A₁} {f₂ : R →+* A₂}
      {E₁ : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f₁)}
      {E₂ : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f₂)}
      (g₁ : ContinuousHom D E₁) (g₂ : ContinuousHom D E₂)
      (φ : formalSpectrum E₁ ⟶ formalSpectrum E₂),
        φ ≫ formalSpectrumMap hR g₂ = formalSpectrumMap hR g₁ →
          ∃! h : ContinuousHom E₂ E₁, formalSpectrumMap
            (TopologicalRing.completionOver_isWeaklyAdmissible f₂ hR) h = φ ∧
              h.toRingHom.comp g₂.toRingHom = g₁.toRingHom) ∧
    (∀ {X : FppfSheaf 𝔅 S hS}, IsAffineFormalAlgebraicSpace 𝔅 S hS X →
      ∀ p : X ⟶ formalSpectrum D, IsRepresentableEtale 𝔅 S hS p →
        ∃ (A : Type u) (_ : CommRing A) (f : R →+* A), f.Etale ∧
          ∃ (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
            (g : ContinuousHom D E), g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f ∧
              ∃ i : X ≅ formalSpectrum E, p = i.hom ≫ formalSpectrumMap hR g) :=
  ⟨fun f hf E g hg ↦
      isRepresentableEtale_formalSpectrumMap_completionOver_of_etale 𝔅 S hS hR D f hf E g hg,
    fun g₁ g₂ φ hφ ↦ existsUnique_continuousHom_of_formalSpectrumMap_over 𝔅 S hS hR D g₁ g₂ φ hφ,
    fun hX p hp ↦ exists_etale_formalSpectrum_iso_of_isRepresentableEtale 𝔅 S hS hR D hY hX p hp⟩

end Forward

end AlgebraicGeometry.FormalSpace

end
