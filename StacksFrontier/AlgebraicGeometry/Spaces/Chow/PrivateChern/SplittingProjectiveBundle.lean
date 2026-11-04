module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SplittingInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged

/-!
# Projective bundle towers and the splitting step

A *projective bundle projection* is a morphism of algebraic spaces isomorphic over its target to
the projection `π : 𝐏(ℰ) ⟶ X` of the projective bundle of a finite locally free module `ℰ` of
constant positive rank, and a *projective bundle tower* is a finite composite of such
projections. For a module `ℰ` of rank `s + 1` on a good algebraic space `X/B` in Situation 0EDT
the projective bundle `π : P = 𝐏(ℰ) ⟶ X` is flat of relative dimension `s`, and the kernel of
the tautological quotient `π^*ℰ ⟶ 𝒪_P(1)` has rank `s` with invertible cokernel; so once the
flat pullback along `π` is known to be injective on Chow groups after every base change
(Stacks 0ERV), `π` is a splitting step in the sense of
`AlgebraicGeometry.Space.PrivateChern.HasSplittingStep`, and the induction of the splitting
principle (Stacks 0ESC) runs with projective bundle towers.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.IsProjectiveBundleProjection`: the projective bundle
  projections.
* `AlgebraicGeometry.Space.PrivateChern.IsProjectiveBundleTower`: their finite composites.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.isProjectiveBundleProjection_projectiveBundleDatum_proj`:
  the projection of the projective bundle of a module of rank `s + 1` is one.
* `AlgebraicGeometry.Space.PrivateChern.hasSplittingStep_projectiveBundle`: the projective
  bundle is a splitting step, given the injectivity of its flat pullback after base change.
* `AlgebraicGeometry.Space.PrivateChern.exists_projectiveBundleTower_filtration`: the conclusion
  of Stacks 0ESC for projective bundle towers, given that injectivity for every projective
  bundle of a module of positive rank on a good algebraic space.

## Implementation notes

Stacks 0ESC asks for a *projective* morphism `π : P ⟶ X`, and projective morphisms of algebraic
spaces are not defined in the source. The morphism its proof constructs is a finite composite of
projective bundle projections, and this is the class used here. The bundles are those of
`AlgebraicGeometry.Space.projectiveBundle`; a projection is any morphism
isomorphic to one of them over the target, so that the class does not depend on the chosen
construction of `𝐏(ℰ)`.

## References

* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space.PrivateChern

section Tower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The projective bundle projections**: the morphisms `π : P ⟶ X` of presheaves on the big
fppf site with `X` an algebraic space, for which there are a finite locally free `𝒪_X`-module
`ℰ` of constant rank `s + 1` and an isomorphism `P ≅ 𝐏(ℰ)` over `X`. -/
def IsProjectiveBundleProjection : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  fun P X π => ∃ (hX : IsAlgebraicSpace B S hS X) (E : Modules.{u, u} B S hS X hX) (s : ℕ)
    (_ : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X hX) E (s + 1))
    (hqc : E.IsQuasicoherentOnSite) (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
    (e : P ≅ (@projectiveBundle B S hS ⟨X, hX⟩ E hqc hfree).1),
      e.hom ≫ (@projectiveBundleProj B S hS ⟨X, hX⟩ E hqc hfree).hom = π

/-- **The projective bundle towers**: the finite composites of projective bundle projections,
the identities included. -/
abbrev IsProjectiveBundleTower : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  IsProjectiveBundleProjection.multiplicativeClosure

/-- A projective bundle projection is a projective bundle tower. -/
theorem IsProjectiveBundleProjection.isProjectiveBundleTower {P X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {π : P ⟶ X} (h : IsProjectiveBundleProjection π) : IsProjectiveBundleTower π :=
  .of π h

end Tower

section Step

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- The projection of the projective bundle of a module of rank `s + 1` on a good space is a
projective bundle projection. -/
theorem isProjectiveBundleProjection_projectiveBundleDatum_proj
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : ℕ)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E (s + 1)) :
    @IsProjectiveBundleProjection D.site D.base D.base_mem _ _
      (projectiveBundleDatum E s hE).proj := by
  let := isQuasicoherentOnSite_of_rank E hE
  have key : ∃ (e : (projectiveBundleDatum E s hE).space ≅
      (projectiveBundle (X := goodSpace hX) E (isFiniteLocallyFreeOnSite_of_rank E hE)).1),
      e.hom ≫ (projectiveBundleProj (X := goodSpace hX) E
        (isFiniteLocallyFreeOnSite_of_rank E hE)).hom = (projectiveBundleDatum E s hE).proj :=
    ⟨Iso.refl _, Category.id_comp _⟩
  exact ⟨hX.1, E, s, hE, isQuasicoherentOnSite_of_rank E hE,
    isFiniteLocallyFreeOnSite_of_rank E hE, key⟩

/-- **A splitting step from a quotient of rank one**, for a morphism of algebraic spaces
`π : Z ⟶ X`: the form of `AlgebraicGeometry.Space.PrivateChern.hasSplittingStep_of_epi` in which
the inverse image is taken along `π` itself. -/
theorem hasSplittingStep_of_epi_of_algebraicSpace
    (Q : MorphismProperty ((BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u))
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : ℕ)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E (s + 1))
    {Z : AlgebraicSpaces D.site D.base D.base_mem} (sZ : Z.1 ⟶ D.space) (hZ : D.IsGood sZ)
    (π : Z ⟶ goodSpace hX) (hπ : π.hom ≫ sX = sZ) (d : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π.hom)
    (hd : HasRelativeDimension d D.site D.base D.base_mem π.hom) (hQ : Q π.hom)
    (hinj : HasInjectiveChowBaseChange.{v} D sX π.hom d)
    (L : Modules.{u, u} D.site D.base D.base_mem Z.1 Z.2)
    (τ : (modulePullback D.site D.base D.base_mem π).obj E ⟶ L) [Epi τ]
    (hLinv : IsInvertibleModule Z L) :
    HasSplittingStep.{v} D Q sX hX E s :=
  have : Stacks.SheafOfModules.IsInvertible
      (smallEtaleRingedSite D.site D.base D.base_mem Z.1 Z.2).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite D.site D.base D.base_mem Z.1 Z.2).O).property L := hLinv
  hasSplittingStep_of_epi D Q sX hX E s hE sZ hZ π.hom hπ d hflat hd hQ hinj L τ
    (RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible' _ _
      (smallEtaleRingedSite_isLocallyRinged D.site D.base D.base_mem Z.1 Z.2)) hLinv

/-- **The projective bundle is a splitting step.** For a module `ℰ` of rank `s + 1` on a good
algebraic space `X/B`, the projective bundle `π : 𝐏(ℰ) ⟶ X`, flat of relative dimension `s`,
with the kernel of the tautological quotient `π^*ℰ ⟶ 𝒪_P(1)`, is a splitting step for `ℰ` within
the projective bundle towers, as soon as the flat pullback along `π` is injective on Chow groups
after every base change. -/
theorem hasSplittingStep_projectiveBundle
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : ℕ)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E (s + 1))
    (hinj : HasInjectiveChowBaseChange.{v} D sX (projectiveBundleDatum E s hE).proj s) :
    HasSplittingStep.{v} D IsProjectiveBundleTower sX hX E s :=
  let := isQuasicoherentOnSite_of_rank E hE
  hasSplittingStep_of_epi_of_algebraicSpace D IsProjectiveBundleTower E s hE
    (projectiveBundleDatum E s hE).toBase (projectiveBundleDatum E s hE).isGood
    (projectiveBundleProj (X := goodSpace hX) E (isFiniteLocallyFreeOnSite_of_rank E hE))
    (projectiveBundleDatum E s hE).proj_comp s
    (projectiveBundleDatum E s hE).isFlat (projectiveBundleDatum E s hE).hasRelativeDimension
    (isProjectiveBundleProjection_projectiveBundleDatum_proj D E s hE).isProjectiveBundleTower
    hinj _ (projectiveBundleTautological (X := goodSpace hX) E
      (isFiniteLocallyFreeOnSite_of_rank E hE)).hom
    (isInvertibleModule_projectiveBundleTwist (X := goodSpace hX) E
      (isFiniteLocallyFreeOnSite_of_rank E hE))

attribute [local instance 10000] smallEtaleModulesAbelian abelian_modules hasZeroObject_modules
  hasInitial_modules initialMonoClass_modules hasCokernels_modules in
/-- **The splitting principle for projective bundle towers, from Stacks 0ERV.** Suppose that
for every module `ℰ` of rank `s + 1` on a good algebraic space over `B` the flat pullback along
the projective bundle `𝐏(ℰ) ⟶ X` is injective on Chow groups after every base change. Then for
every finite family of locally free modules `ℰ_i` of ranks `r_i` on a good algebraic space
`X/B` there is a projective bundle tower `π : P ⟶ X` of good algebraic spaces over `B`, flat of
some relative dimension `d`, such that for every morphism `f : Y ⟶ X` of good algebraic spaces
over `B` and every fibre product `Y ×_X P` the flat pullback `CH_k(Y) ⟶ CH_{k+d}(Y ×_X P)` is
injective, and such that every `π^*ℰ_i` has a filtration `0 = F_0 ⊂ ⋯ ⊂ F_{r_i} = π^*ℰ_i` by
subobjects whose successive quotients are invertible. -/
theorem exists_projectiveBundleTower_filtration
    (h0ERV : ∀ {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
      (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : ℕ)
      (hE : IsFiniteLocallyFreeOfRank D sX hX E (s + 1)),
      HasInjectiveChowBaseChange.{v} D sX (projectiveBundleDatum E s hE).proj s)
    {ι : Type*} [Finite ι] (X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (E : ι → Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ι → ℕ)
    (hE : ∀ i, IsFiniteLocallyFreeOfRank D sX hX (E i) (r i)) :
    ∃ (P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u) (sP : P ⟶ D.space) (hP : D.IsGood sP)
      (π : P ⟶ X) (hπ : π ≫ sX = sP) (d : ℕ) (hflat : IsFlat D.site D.base D.base_mem π)
      (hd : HasRelativeDimension d D.site D.base D.base_mem π),
      IsProjectiveBundleTower π ∧ HasInjectiveChowPullbacks.{v} D sX hX sP hP π hπ d hflat hd ∧
        ∀ i, ∃ (F : Fin (r i + 1) → Subobject ((spaceModulePullback D hX.1 hP.1 π).obj (E i)))
          (hF : Monotone F), F 0 = ⊥ ∧ F (Fin.last (r i)) = ⊤ ∧
            ∀ j : Fin (r i), IsInvertibleModule ⟨P, hP.1⟩
              (cokernel (Subobject.ofLE (F j.castSucc) (F j.succ) (hF j.castSucc_le_succ))) :=
  (isSplitting_of_hasSplittingStep.{v} D IsProjectiveBundleTower
    (fun sX hX E s hE => hasSplittingStep_projectiveBundle D E s hE (h0ERV sX hX E s hE))
    sX hX E r hE).exists_subobject_filtration D

end Step

end AlgebraicGeometry.Space.PrivateChern

end
