module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPullbackHomProducts
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumCompletedSections
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemModuleCat
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.CategoryTheory.Triangulated.HomBijectiveFiveLemma
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryB.InverseLimitAsDerivedLimit
import all StacksFrontier.Topology.Sheaves.Cohomology.RecoveryB.InverseLimitAsDerivedLimit

/-!
# The canonical map `O_X ⊗_R lim Mₙ ⟶ lim (O_X ⊗_R Mₙ)` on perfect objects

Let `f : X ⟶ Spec R` be proper, flat and of finite presentation and let `(Mₙ)` be an inverse
system of `R`-modules with surjective transition maps. This file proves that the canonical map
`O_X ⊗_R lim Mₙ ⟶ lim (O_X ⊗_R Mₙ)` induces a bijection on morphisms out of every perfect object
of `D(𝒪_X)`, which is the perfect case of [Stacks, Tag 0D2Q].

The two short exact sequences `0 → lim → ∏ → ∏ → 0`, of `R`-modules pulled back to `X` and of
the `O_X ⊗_R Mₙ`, give distinguished triangles and a morphism between them. On the product terms
the morphism is the comparison `O_X ⊗_R ∏ Mₙ ⟶ ∏ (O_X ⊗_R Mₙ)`, which induces bijections on
morphisms out of perfect objects by `ProperFlatPullbackHomProducts` and the fact that a product
of quasi-coherent modules is a product in `D(𝒪_X)` (their higher cohomology vanishes on affine
opens). The five lemma concludes. The second sequence is exact because the towers of sections
over affine opens are surjective, so Mittag-Leffler.

## Main results

* `Stacks.ProperFlatPullbackLimit.shortExact_inverseLimitSequence_moduleCat`: `0 → lim → ∏ → ∏ → 0`
  is exact for a tower of modules with surjective transition maps.
* `Stacks.ProperFlatPullbackLimit.bijective_comp_singleFunctor_map_limitPost_of_isPerfect`: the
  perfect case of [Stacks, Tag 0D2Q], at the standard model.

## References

* [Stacks Project, Tag 0D2Q](https://stacks.math.columbia.edu/tag/0D2Q)
* [Stacks Project, Tag 0A0J](https://stacks.math.columbia.edu/tag/0A0J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v₁ v₂ u₁ u₂

namespace Stacks.ProperFlatPullbackLimit

/-- If the successive transition maps of an inverse system indexed by `ℕ` are epimorphisms,
then all of its transition maps are. -/
lemma epi_map_of_epi_succ {C : Type*} [Category C] (M : ℕᵒᵖ ⥤ C)
    (h : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op)) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    Epi (M.map f) := by
  have htrans (a b : ℕ) (hab : b ≤ a) : Epi (M.map (homOfLE hab).op) := by
    induction a, hab using Nat.le_induction with
    | base => simpa using (show Epi (𝟙 (M.obj (op b))) from inferInstance)
    | @succ a hab ih =>
      rw [show (homOfLE (hab.trans (Nat.le_succ a))).op =
        (homOfLE (Nat.le_succ a)).op ≫ (homOfLE hab).op from Subsingleton.elim _ _, M.map_comp]
      exact epi_comp' (h a) ih
  rw [show f = (homOfLE f.unop.le).op from Subsingleton.elim _ _]
  exact htrans _ _ _

/-- An inverse system of modules with surjective transition maps gives a short exact sequence
`0 → lim Mₙ → ∏ Mₙ → ∏ Mₙ → 0`. -/
theorem shortExact_inverseLimitSequence_moduleCat {R : CommRingCat.{u}}
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} R) (hsurj : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op)) :
    (inverseLimitSequence M).ShortExact := by
  obtain ⟨hex, hmono⟩ := inverseLimitSequence_exact_and_mono M
  have : Epi (inverseLimitSequence M).g :=
    Stacks.Algebraization.epi_milnorDifference_of_isMittagLefflerCategorical M
      (isMittagLefflerCategorical_of_isMittagLeffler_forget M
        (Functor.isMittagLeffler_of_surjective _ fun _ _ f =>
          (ModuleCat.epi_iff_surjective _).1 (epi_map_of_epi_succ M hsurj f)))
  exact ⟨hex⟩

/-- The comparison of `0 → lim Fₙ → ∏ Fₙ → ∏ Fₙ → 0` mapped along an additive functor `G` with
the same sequence for `F ⋙ G`: the canonical maps `G (lim Fₙ) ⟶ lim G Fₙ` and
`G (∏ Fₙ) ⟶ ∏ G Fₙ`. -/
def inverseLimitSequenceMapComparison {A : Type u₁} {B : Type u₂} [Category.{v₁} A]
    [Category.{v₂} B] [Preadditive A]
    [Preadditive B] (F : ℕᵒᵖ ⥤ A) (G : A ⥤ B) [G.Additive] [HasLimit F]
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] [HasLimit (F ⋙ G)]
    [HasProduct fun n : ℕ => (F ⋙ G).obj ⟨n⟩] :
    (inverseLimitSequence F).map G ⟶ inverseLimitSequence (F ⋙ G) where
  τ₁ := limit.post F G
  τ₂ := Pi.lift fun n : ℕ => G.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) n)
  τ₃ := Pi.lift fun n : ℕ => G.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) n)
  comm₁₂ := by
    refine Pi.hom_ext _ _ fun n => ?_
    simp [inverseLimitSequence, inverseSystemLimitKernelFork, ← G.map_comp]
  comm₂₃ := by
    refine Pi.hom_ext _ _ fun n => ?_
    have hF : (inverseLimitSequence F).g ≫ Pi.π (fun n : ℕ => F.obj ⟨n⟩) n =
        Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op :=
      Pi.lift_π _ _
    have hFG : (inverseLimitSequence (F ⋙ G)).g ≫ Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) n =
        Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) (n + 1) ≫
            (F ⋙ G).map (homOfLE (Nat.le_succ n)).op :=
      Pi.lift_π _ _
    have hL : ((Pi.lift fun n : ℕ => G.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) n) :
        G.obj (∏ᶜ fun n : ℕ => F.obj ⟨n⟩) ⟶ ∏ᶜ fun n : ℕ => (F ⋙ G).obj ⟨n⟩) ≫
        (inverseLimitSequence (F ⋙ G)).g) ≫ Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) n =
        G.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) n) -
          G.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1)) ≫
            G.map (F.map (homOfLE (Nat.le_succ n)).op) :=
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFG).trans
        ((Preadditive.comp_sub _ _ _).trans (congrArg₂ (· - ·) (Pi.lift_π _ _)
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Pi.lift_π _ _))))))
    have hR : (G.map (inverseLimitSequence F).g ≫
        (Pi.lift fun n : ℕ => G.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) n) :
          G.obj (∏ᶜ fun n : ℕ => F.obj ⟨n⟩) ⟶ ∏ᶜ fun n : ℕ => (F ⋙ G).obj ⟨n⟩)) ≫
          Pi.π (fun n : ℕ => (F ⋙ G).obj ⟨n⟩) n =
        G.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) n) -
          G.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1)) ≫
            G.map (F.map (homOfLE (Nat.le_succ n)).op) :=
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Pi.lift_π _ _)).trans
        ((G.map_comp _ _).symm.trans ((congrArg G.map hF).trans
          (G.map_sub.trans (congrArg (_ - ·) (G.map_comp _ _))))))
    exact hL.trans hR.symm

section Pullback

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- The pullback to `X` of the quasi-coherent module `M̃ₙ` is quasi-coherent. -/
private theorem isQuasicoherent_pullback_tilde_obj (M : ℕᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ) :
    ((M ⋙ tilde.functor R ⋙ Scheme.Modules.pullback f).obj ⟨n⟩).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pullback _ _ inferInstance

/-- Morphisms out of a perfect object into `O_X ⊗_R ∏ Mₙ` are morphisms into the product of the
`O_X ⊗_R Mₙ` of `𝒪_X`-modules, along the canonical comparison map. -/
theorem bijective_comp_singleFunctor_map_piLift_of_isPerfect [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (M : ℕᵒᵖ ⥤ ModuleCat.{u} R) :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard (StrictlyPerfect.OXMod X.toRingedSpace)
    ∀ (E : DerivedCategory X.Modules),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
    Function.Bijective (fun x : E ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj
        ((tilde.functor R ⋙ Scheme.Modules.pullback f).obj (∏ᶜ fun n : ℕ => M.obj ⟨n⟩)) =>
      x ≫ (DerivedCategory.singleFunctor X.Modules 0).map
        (Pi.lift fun n : ℕ => (tilde.functor R ⋙ Scheme.Modules.pullback f).map
          (Pi.π (fun n : ℕ => M.obj ⟨n⟩) n) :
          _ ⟶ ∏ᶜ fun n : ℕ => (M ⋙ tilde.functor R ⋙ Scheme.Modules.pullback f).obj ⟨n⟩)) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  intro E hE
  have : PreservesLimit
      (Discrete.functor fun n : ℕ => (M ⋙ tilde.functor R ⋙ Scheme.Modules.pullback f).obj ⟨n⟩)
      (DerivedCategory.singleFunctor X.Modules 0) :=
    Stacks.Cohomology.SpaceInverseLimits.preservesProduct_single_of_isBasis X.toRingedSpace
      (fun n : ℕ => (M ⋙ tilde.functor R ⋙ Scheme.Modules.pullback f).obj ⟨n⟩) X.affineOpens
      X.isBasis_affineOpens fun U hU n p hp =>
        have := isQuasicoherent_pullback_tilde_obj f M n
        Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X _ U hU p hp
  refine (Function.Bijective.of_comp_iff' (bijective_comp_map_π_of_preservesLimit
    (DerivedCategory.singleFunctor X.Modules 0)
    (fun n : ℕ => (M ⋙ tilde.functor R ⋙ Scheme.Modules.pullback f).obj ⟨n⟩) E) _).1 ?_
  have heq : (fun φ : E ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj
        (∏ᶜ fun n : ℕ => (M ⋙ tilde.functor R ⋙ Scheme.Modules.pullback f).obj ⟨n⟩) =>
      fun i => φ ≫ (DerivedCategory.singleFunctor X.Modules 0).map (Pi.π _ i)) ∘
      (fun x : E ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj
        ((tilde.functor R ⋙ Scheme.Modules.pullback f).obj (∏ᶜ fun n : ℕ => M.obj ⟨n⟩)) =>
      x ≫ (DerivedCategory.singleFunctor X.Modules 0).map
        (Pi.lift fun n : ℕ => (tilde.functor R ⋙ Scheme.Modules.pullback f).map
          (Pi.π (fun n : ℕ => M.obj ⟨n⟩) n) :
          _ ⟶ ∏ᶜ fun n : ℕ => (M ⋙ tilde.functor R ⋙ Scheme.Modules.pullback f).obj ⟨n⟩)) =
      (fun φ : E ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj
        ((tilde.functor R ⋙ Scheme.Modules.pullback f).obj (∏ᶜ fun n : ℕ => M.obj ⟨n⟩)) =>
      fun n => φ ≫ (DerivedCategory.singleFunctor X.Modules 0).map
        ((tilde.functor R ⋙ Scheme.Modules.pullback f).map (Pi.π (fun n : ℕ => M.obj ⟨n⟩) n))) := by
    funext x n
    simp only [Function.comp_apply, Category.assoc, ← Functor.map_comp, Pi.lift_π]
  rw [heq]
  exact bijective_comp_singleFunctor_pullback_map_π f (fun n : ℕ => M.obj ⟨n⟩) E hE

/-- **[Stacks, Tag 0D2Q] for a perfect object.** For `f : X ⟶ Spec R` proper, flat and of finite
presentation and an inverse system `(Mₙ)` of `R`-modules with surjective transition maps, the
canonical map `O_X ⊗_R lim Mₙ ⟶ lim (O_X ⊗_R Mₙ)` induces a bijection on morphisms out of every
perfect object of `D(𝒪_X)`, at the standard model of the derived category. -/
theorem bijective_comp_singleFunctor_map_limitPost_of_isPerfect [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (M : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (hsurj : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op)) :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard (StrictlyPerfect.OXMod X.toRingedSpace)
    ∀ (E : DerivedCategory X.Modules),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
    Function.Bijective (fun φ : E ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj
        ((tilde.functor R ⋙ Scheme.Modules.pullback f).obj (limit M)) =>
      φ ≫ (DerivedCategory.singleFunctor X.Modules 0).map
        (limit.post M (tilde.functor R ⋙ Scheme.Modules.pullback f))) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  intro E hE
  have : AlgebraicGeometry.IsFlat f.toLRSHom.toShHom := fun x => Flat.stalkMap f x
  have := AlgebraicGeometry.preservesFiniteLimits_pullback_of_flat f
  have := AlgebraicGeometry.tilde.preservesFiniteLimits R
  let Φ := tilde.functor R ⋙ Scheme.Modules.pullback f
  let F := M ⋙ Φ
  have hS₁ := (shortExact_inverseLimitSequence_moduleCat M hsurj).map_of_exact Φ
  have hepi : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op) := fun n =>
    Φ.map_epi (M.map (homOfLE (Nat.le_succ n)).op)
  have hS₂ : (inverseLimitSequence F).ShortExact :=
    Stacks.Cohomology.SpaceInverseLimits.inverseLimitSequence_shortExact_of_isBasis
      X.toRingedSpace F X.affineOpens X.isBasis_affineOpens fun U hU =>
        Stacks.Cohomology.SpaceInverseLimits.epi_inverseLimitDifference_of_surjective _ fun n =>
          have := hepi n
          have := isQuasicoherent_pullback_tilde_obj f M n
          have := isQuasicoherent_pullback_tilde_obj f M (n + 1)
          Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
            (F.map (homOfLE (Nat.le_succ n)).op) U hU
  have hb := bijective_comp_singleFunctor_map_piLift_of_isPerfect f M
  exact CategoryTheory.Pretriangulated.bijective_comp_hom₁
    (ShortComplex.ShortExact.singleTriangle.map hS₁ hS₂
      (inverseLimitSequenceMapComparison M Φ :
        (inverseLimitSequence M).map Φ ⟶ inverseLimitSequence F))
    hS₁.singleTriangle_distinguished hS₂.singleTriangle_distinguished
    (fun E' => Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E')
    (fun E' n hE' => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hE' n)
    hb hb E hE

end Pullback

end Stacks.ProperFlatPullbackLimit
