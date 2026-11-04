module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianAdicStages
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionAlongIdeal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentCartesianEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.DiscretePresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.OfPresheaf
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits

/-!
# Quasi-coherent modules on the completion of an affine scheme along an ideal

Let `X = Spec A` be an affine scheme of a big fppf site over `S` and let `I ⊆ A` be a finitely
generated ideal. The completion `X^∧ = colim Spec(A ⧸ Iⁿ⁺¹)` of `X` along `V(I)` is the formal
spectrum `Spf(A^∧)` (Stacks 0GXX), and its category fibred in groupoids `𝒳` carries the
category `QCoh(𝒪_𝒳)` of quasi-coherent modules of Stacks 06WG. This file proves

`QCoh(𝒪_𝒳) ≌ {I-adically complete A-modules}`,

which is the identification made in Stacks, Examples, Section 0ALF for `Spf(ℤ_p)`: a
quasi-coherent module on `𝒳` is a system `(Mₙ)` of modules over the stages with
`Mₙ = Mₙ₊₁ ⧸ Iⁿ Mₙ₊₁`, and such systems are the complete modules (Stacks 09B8).

## Main definitions

* `AlgebraicGeometry.FormalSpace.completionFibred`: the category fibred in groupoids of the
  completion.
* `AlgebraicGeometry.FormalSpace.completionAdicStages`: the stages `Spec(A ⧸ Iⁿ)` of the
  completion, as an adic stage system of its affine subcategory.
* `AlgebraicGeometry.FormalSpace.quasicoherentModulesCompletionEquiv`: the equivalence between
  the quasi-coherent modules on the completion and the `I`-adically complete `A`-modules.

## Implementation notes

The equivalence is the composite of two. Restriction to the affine subcategory identifies
quasi-coherent modules with cartesian presheaves of modules there (Stacks 0H0C and 0H0E,
`AlgebraicGeometry.Stack.AffineCategory.quasicoherentEquivCartesian`). The affine subcategory of
the completion has the stages `xₙ = Spec(A ⧸ Iⁿ)` as an adic stage system: an affine scheme over
the completion factors through a stage because it is quasi-compact (Stacks 0738 (3)), and through
each stage at most once because the stages are monomorphisms into the colimit, the transition
maps being closed immersions. For such a system cartesian presheaves of modules are complete
modules (`Stacks.PresheafOfModules.AdicStages.cartesianEquivalenceComplete`).

## References

* [Stacks Project, Tag 0ALF](https://stacks.math.columbia.edu/tag/0ALF)
* [Stacks Project, Tag 0ALG](https://stacks.math.columbia.edu/tag/0ALG)
* [Stacks Project, Tag 0GXX](https://stacks.math.columbia.edu/tag/0GXX)
* [Stacks Project, Tag 09B8](https://stacks.math.columbia.edu/tag/09B8)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
  (I : Ideal A)

/-- The category fibred in groupoids attached to the completion of `Spec A` along `V(I)`: the
category of Stacks 0049 of the sheaf of sets `colim Spec(A ⧸ Iⁿ⁺¹)`, with discrete fibres. -/
abbrev completionFibred : BasedCategory (BigFppfOver B S hS) :=
  presheafOfGroupoids ((completionAlongIdeal B S hS f hA I).obj ⋙ typeToGrpd)

/-- The category attached to the completion is fibred in groupoids (Stacks 0049). -/
theorem isFiberedInGroupoids_completionFibred :
    (completionFibred B S hS f hA I).p.IsFiberedInGroupoids :=
  isFiberedInGroupoids_presheafOfGroupoids _

namespace CompletionStages

/-- The diagram of represented stages whose colimit is the completion. -/
abbrev diagram : ULift.{u + 1} ℕ ⥤ FppfSheaf B S hS :=
  infinitesimalNeighbourhoodDiagram B S hS f hA I ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)

/-- The stage `Spec(A ⧸ Iⁿ)`, as an object of the big fppf site over `S`. -/
abbrev stageOver (n : ℕ) : BigFppfOver B S hS :=
  (quotientOver B S hS f hA (I ^ n)).obj

/-- The closed immersion `Spec(A ⧸ Iⁿ) ⟶ Spec(A ⧸ Iⁿ⁺¹)`. -/
abbrev j (n : ℕ) : stageOver B S hS f hA I n ⟶ stageOver B S hS f hA I (n + 1) :=
  (quotientOverTransition B S hS f hA (Ideal.pow_le_pow_right (Nat.le_succ n))).hom

/-- The tautological point of the completion over the stage `Spec(A ⧸ Iⁿ⁺¹)` of the colimit. -/
def σ (n : ℕ) :
    (completionAlongIdeal B S hS f hA I).obj.obj (op (stageOver B S hS f hA I (n + 1))) :=
  Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (colimit.ι (diagram B S hS f hA I) ⟨n⟩)

/-- The point of the completion over `Spec(A ⧸ Iⁿ)`. -/
def ξ (n : ℕ) : (completionAlongIdeal B S hS f hA I).obj.obj (op (stageOver B S hS f hA I n)) :=
  (completionAlongIdeal B S hS f hA I).obj.map (j B S hS f hA I n).op (σ B S hS f hA I n)

/-- The point of the completion over `Spec(A ⧸ Iⁿ⁺¹)` is the tautological point `σ n`. -/
theorem ξ_succ (n : ℕ) : ξ B S hS f hA I (n + 1) = σ B S hS f hA I n := by
  have hw := colimit.w (diagram B S hS f hA I)
    (homOfLE (show (⟨n⟩ : ULift.{u + 1} ℕ) ≤ ⟨n + 1⟩ from Nat.le_succ n))
  have h2 := Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS)
    ((BigAffineFppf.inclusion B S hS).map ((infinitesimalNeighbourhoodDiagram B S hS f hA I).map
      (homOfLE (show (⟨n⟩ : ULift.{u + 1} ℕ) ≤ ⟨n + 1⟩ from Nat.le_succ n))))
    (colimit.ι (diagram B S hS f hA I) ⟨n + 1⟩)
  exact h2.symm.trans (congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) hw)

/-- The stage `Spec(A ⧸ Iⁿ)` with its point of the completion, as an object of the affine
subcategory of the completion. -/
def stage (n : ℕ) : Stack.AffineCategory B S hS (completionFibred B S hS f hA I).p :=
  ⟨⟨stageOver B S hS f hA I n, Discrete.mk (ξ B S hS f hA I n)⟩,
    (quotientOver B S hS f hA (I ^ n)).property⟩

/-- The closed immersion `Spec(A ⧸ Iⁿ) ⟶ Spec(A ⧸ Iⁿ⁺¹)`, as a morphism of stages. -/
def stageHom (n : ℕ) : stage B S hS f hA I n ⟶ stage B S hS f hA I (n + 1) :=
  ObjectProperty.homMk
    { base := j B S hS f hA I n
      fiber := Discrete.eqToHom
        (congrArg ((completionAlongIdeal B S hS f hA I).obj.map (j B S hS f hA I n).op)
          (ξ_succ B S hS f hA I n)).symm }

/-- The tower of stages of the completion. -/
abbrev tower : ℕ ⥤ Stack.AffineCategory B S hS (completionFibred B S hS f hA I).p :=
  Functor.ofSequence (stageHom B S hS f hA I)

/-- The structure presheaf of the affine subcategory of the completion. -/
abbrev rings :=
  Stack.AffineCategory.structureRings B S hS (completionFibred B S hS f hA I).p

/-- The ring map `A ⟶ Γ(Spec(A ⧸ Iⁿ), 𝒪)`. -/
def α (n : ℕ) : A →+* (rings B S hS f hA I).obj (op ((tower B S hS f hA I).obj n)) :=
  (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I ^ n))).inv.hom.comp (Ideal.Quotient.mk (I ^ n))

/-- The ring map `A ⟶ Γ(Spec(A ⧸ Iⁿ), 𝒪)` is surjective. -/
theorem surjective_α (n : ℕ) : Function.Surjective (α B S hS f hA I n) :=
  (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I ^ n))).symm.commRingCatIsoToRingEquiv.surjective.comp
    Ideal.Quotient.mk_surjective

/-- The kernel of the ring map `A ⟶ Γ(Spec(A ⧸ Iⁿ), 𝒪)` is `Iⁿ`. -/
theorem ker_α (n : ℕ) : RingHom.ker (α B S hS f hA I n) = I ^ n :=
  (RingHom.ker_comp_of_injective (Ideal.Quotient.mk (I ^ n))
    (f := (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I ^ n))).inv.hom)
    (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I ^ n))).symm.commRingCatIsoToRingEquiv.injective).trans
    Ideal.mk_ker

/-- The ring maps `α` are compatible with the transition maps of the tower: restricting
`α (n + 1)` along `Spec(A ⧸ Iⁿ) ⟶ Spec(A ⧸ Iⁿ⁺¹)` gives `α n`. -/
theorem map_comp_α (n : ℕ) :
    ((rings B S hS f hA I).map ((tower B S hS f hA I).map (homOfLE (Nat.le_succ n))).op).hom.comp
      (α B S hS f hA I (n + 1)) = α B S hS f hA I n := by
  rw [Functor.ofSequence_map_homOfLE_succ]
  let φ := CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n))
  exact RingHom.ext fun a => (congrArg (fun g => g.hom (Ideal.Quotient.mk (I ^ (n + 1)) a))
    (Scheme.ΓSpecIso_inv_naturality φ)).symm

/-- The transition maps of the diagram of represented stages are monomorphisms: they are the
represented closed immersions `Spec(A ⧸ Iᵐ⁺¹) ⟶ Spec(A ⧸ Iⁿ⁺¹)`. -/
theorem mono_diagram_map {i i' : ULift.{u + 1} ℕ} (g : i ⟶ i') :
    Mono ((diagram B S hS f hA I).map g) := by
  have hclosed : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map
        ((infinitesimalNeighbourhoodDiagram B S hS f hA I).map g))) := by
    have hle : i ≤ i' := leOfHom g
    have hI : I ^ (i'.down + 1) ≤ I ^ (i.down + 1) :=
      Ideal.pow_le_pow_right (Nat.add_le_add_right (show i.down ≤ i'.down from hle) 1)
    show IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)))
    exact IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective hI)
  have : (BigFppfOver.toScheme B S hS).Faithful := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  have : Mono ((BigAffineFppf.inclusion B S hS).map
      ((infinitesimalNeighbourhoodDiagram B S hS f hA I).map g)) :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have : PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) := by
    dsimp [Sheaf.sheafifiedYoneda]
    infer_instance
  exact (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_mono _

/-- The closed immersion `Spec(A ⧸ Iⁿ) ⟶ Spec(A ⧸ Iⁿ⁺¹)` is a monomorphism of the big fppf site. -/
theorem mono_j (n : ℕ) : Mono (j B S hS f hA I n) := by
  have hclosed : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (j B S hS f hA I n)) := by
    have hI : I ^ (n + 1) ≤ I ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
    show IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)))
    exact IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective hI)
  have : (BigFppfOver.toScheme B S hS).Faithful := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  exact (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance

/-- The stages include into the completion as monomorphisms. -/
theorem mono_ι (n : ℕ) : Mono (colimit.ι (diagram B S hS f hA I) ⟨n⟩) :=
  Sheaf.mono_colimit_ι_of_mono_transition (diagram B S hS f hA I)
    (fun _ _ g => mono_diagram_map B S hS f hA I g) ⟨n⟩

/-- Two maps to the stage `Spec(A ⧸ Iⁿ⁺¹)` naming the same point of the completion are equal. -/
theorem eq_of_map_σ {n : ℕ} {T : BigFppfOver B S hS} {g g' : T ⟶ stageOver B S hS f hA I (n + 1)}
    (h : (completionAlongIdeal B S hS f hA I).obj.map g.op (σ B S hS f hA I n) =
      (completionAlongIdeal B S hS f hA I).obj.map g'.op (σ B S hS f hA I n)) : g = g' := by
  have h2 : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
        colimit.ι (diagram B S hS f hA I) ⟨n⟩ =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g' ≫
        colimit.ι (diagram B S hS f hA I) ⟨n⟩ :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective <|
      (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) g
        (colimit.ι (diagram B S hS f hA I) ⟨n⟩)).trans (h.trans
          (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) g'
            (colimit.ι (diagram B S hS f hA I) ⟨n⟩)).symm)
  have := mono_ι B S hS f hA I n
  exact (sheafifiedYonedaFF B S hS).map_injective
    ((cancel_mono (colimit.ι (diagram B S hS f hA I) ⟨n⟩)).1 h2)

/-- **An affine scheme over the completion factors through a stage**: being quasi-compact, its
point of the colimit comes from a stage (Stacks 0738 (3)). -/
theorem exists_hom_stage (c : Stack.AffineCategory B S hS (completionFibred B S hS f hA I).p) :
    ∃ n, Nonempty (c ⟶ (tower B S hS f hA I).obj n) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj c.obj.base) := c.property
  have hqc := isQuasiCompactObject_over_of_compact_scheme B S hS c.obj.base
  obtain ⟨i, g, hg⟩ := compact_map_factors_through_filtered_colimit (diagram B S hS f hA I)
    (fun _ _ g => mono_diagram_map B S hS f hA I g) c.obj.base hqc
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm c.obj.fiber.as)
  let g₀ := (sheafifiedYonedaFF B S hS).preimage g
  have hg₀ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g₀ = g :=
    (sheafifiedYonedaFF B S hS).map_preimage g
  have h : (completionAlongIdeal B S hS f hA I).obj.map g₀.op (σ B S hS f hA I i.down) =
      c.obj.fiber.as :=
    (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) g₀
      (colimit.ι (diagram B S hS f hA I) i)).symm.trans
      ((congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS))
        ((congrArg (· ≫ colimit.ι (diagram B S hS f hA I) i) hg₀).trans hg)).trans
        (Equiv.apply_symm_apply _ _))
  exact ⟨i.down + 1, ⟨ObjectProperty.homMk
    { base := g₀
      fiber := Discrete.eqToHom (h.symm.trans
        (congrArg ((completionAlongIdeal B S hS f hA I).obj.map g₀.op)
          (ξ_succ B S hS f hA I i.down).symm)) }⟩⟩

/-- **An affine scheme over the completion maps to a stage in at most one way**: the stages are
monomorphisms into the completion. -/
theorem subsingleton_hom_stage
    (c : Stack.AffineCategory B S hS (completionFibred B S hS f hA I).p) (n : ℕ) :
    Subsingleton (c ⟶ (tower B S hS f hA I).obj n) := by
  refine ⟨fun φ ψ => ?_⟩
  let X := completionAlongIdeal B S hS f hA I
  have hφ : c.obj.fiber.as = X.obj.map φ.hom.base.op (ξ B S hS f hA I n) :=
    Discrete.eq_of_hom φ.hom.fiber
  have hψ : c.obj.fiber.as = X.obj.map ψ.hom.base.op (ξ B S hS f hA I n) :=
    Discrete.eq_of_hom ψ.hom.fiber
  have hbase : φ.hom.base = ψ.hom.base := by
    have h1 : X.obj.map (φ.hom.base ≫ j B S hS f hA I n).op (σ B S hS f hA I n) =
        X.obj.map (ψ.hom.base ≫ j B S hS f hA I n).op (σ B S hS f hA I n) :=
      (FunctorToTypes.map_comp_apply X.obj (j B S hS f hA I n).op φ.hom.base.op
        (σ B S hS f hA I n)).trans ((hφ.symm.trans hψ).trans
        (FunctorToTypes.map_comp_apply X.obj (j B S hS f hA I n).op ψ.hom.base.op
          (σ B S hS f hA I n)).symm)
    have := mono_j B S hS f hA I n
    exact (cancel_mono (j B S hS f hA I n)).1 (eq_of_map_σ B S hS f hA I h1)
  exact ObjectProperty.hom_ext _
    (Pseudofunctor.CoGrothendieck.Hom.ext _ _ hbase Discrete.hom_eq)

/-- **The stages `Spec(A ⧸ Iⁿ)` of the completion form an adic stage system** of its affine
subcategory. -/
def completionAdicStages : Stacks.PresheafOfModules.AdicStages (rings B S hS f hA I) I where
  x := tower B S hS f hA I
  α := α B S hS f hA I
  surjective_α := surjective_α B S hS f hA I
  ker_α := ker_α B S hS f hA I
  map_comp_α := map_comp_α B S hS f hA I
  exists_hom := exists_hom_stage B S hS f hA I
  subsingleton_hom := subsingleton_hom_stage B S hS f hA I

end CompletionStages

open CompletionStages

/-- **Quasi-coherent modules on the completion of `Spec A` along `V(I)` are the `I`-adically
complete `A`-modules**, for `I` finitely generated. This is the identification of Stacks,
Examples, Section 0ALF: the composite of the restriction to the affine subcategory (Stacks 0H0C,
0H0E) and of the description of cartesian modules over the stages `Spec(A ⧸ Iⁿ)` by complete
modules (Stacks 09B8). -/
def quasicoherentModulesCompletionEquiv (hI : I.FG) :
    FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} B S hS (completionFibred B S hS f hA I).p
        (isFiberedInGroupoids_completionFibred B S hS f hA I) ≌
      Stacks.Examples.IAdicallyCompleteModuleCat.{u} A I :=
  (Stack.AffineCategory.quasicoherentEquivCartesian B S hS (completionFibred B S hS f hA I).p
    (isFiberedInGroupoids_completionFibred B S hS f hA I)).trans
    ((completionAdicStages B S hS f hA I).cartesianEquivalenceComplete hI)

end AlgebraicGeometry.FormalSpace

end
