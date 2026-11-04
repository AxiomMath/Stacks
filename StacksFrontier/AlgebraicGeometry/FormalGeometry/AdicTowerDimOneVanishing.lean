module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAnnihilation
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.CechAffineCover
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.ClosedImmersionSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerTransitionKernel
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.GlobalSheafCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# First cohomology on a tower of thickenings of dimension at most one

The second paragraph of the proof of Grothendieck's algebraization theorem [Stacks, Tag 089A]
needs the vanishing, in a degree `d` independent of `n`, of `H¹(Xₙ₊₁, 𝓘ₙ ⊗ ℒₙ₊₁ ^⊗ d)`, where
`𝓘ₙ` is the ideal sheaf of `Xₙ` in `Xₙ₊₁`. In general the source gets it from
[Stacks, Tag 0897] part (2). When the tower has dimension at most one — the situation of
[Stacks, Tag 0E7R] — there is a direct argument: on a Noetherian space of dimension at most one
the second cohomology of every sheaf vanishes ([Stacks, Tag 02UZ]), so `H¹` turns epimorphisms
into epimorphisms, and the twisted ideal sheaf is a quotient of a sheaf whose `H¹` vanishes.

This file supplies the two topological inputs of that argument.

## Main results

* `Stacks.AdicTowerDimOne.isZero_rightDerived_one_of_epi`: on a scheme whose underlying space is
  Noetherian of dimension at most one, `H¹` of a quotient of a module with vanishing `H¹`
  vanishes.
* `Stacks.AdicTowerDimOne.isZero_rightDerived_one_of_epi_of_smul_eq_zero`: the same for a
  quotient annihilated by the ideal of a closed subscheme, with the vanishing asked only of the
  restriction of the source to that subscheme.
* `Stacks.AdicTowerDimOne.noetherianSpace_level` and
  `Stacks.AdicTowerDimOne.topologicalKrullDim_level`: every member of a cartesian tower over the
  adic thickenings has the Noetherian underlying space and the dimension of its closed member.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AdicTowerDimOne

/-- **`H¹` is right exact in dimension at most one.** Let `X` be a scheme whose underlying space
is Noetherian of topological Krull dimension at most one, and let `p : E ⟶ G` be an epimorphism
of `𝒪_X`-modules. If `H¹(X, E) = 0` then `H¹(X, G) = 0`.

The kernel of `p` has vanishing `H²` by Grothendieck's theorem ([Stacks, Tag 02UZ]), read in
the module-valued spelling through the comparisons of the library, and the long exact sequence
of the short exact sequence `0 ⟶ Ker p ⟶ E ⟶ G ⟶ 0` gives the claim. -/
theorem isZero_rightDerived_one_of_epi {X : Scheme.{u}} [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞)) {E G : X.Modules} (p : E ⟶ G)
    [Epi p] (hE : IsZero (((moduleGlobalSections X).rightDerived 1).obj E)) :
    IsZero (((moduleGlobalSections X).rightDerived 1).obj G) := by
  have hS : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p))
      inferInstance inferInstance
  have h2 : IsZero (((moduleGlobalSections X).rightDerived (1 + 1)).obj (kernel p)) := by
    refine Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup
      X.ringCatSheaf ⊤ 2 _ ?_
    rw [Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH]
    exact Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
      hdim (by norm_num) _
  exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃ hS
    (moduleGlobalSections X) 1 hE h2

/-- **`H¹` of a module living on a closed subscheme, from a surjection upstairs.** Let
`j : Z ⟶ X` be a closed immersion into a scheme whose underlying space is Noetherian of dimension
at most one, let `p : E ⟶ G` be an epimorphism of `𝒪_X`-modules, and suppose the ideal of `Z`
annihilates `G`. If `H¹(Z, j^* E) = 0` then `H¹(X, G) = 0`.

Since `G` is annihilated by the ideal of `Z`, the unit `G ⟶ j_* j^* G` is an isomorphism
([Stacks, Tag 08KS]); composing `j_* j^* p` with its inverse gives an epimorphism
`j_* j^* E ⟶ G`, whose source has vanishing `H¹` because cohomology does not change along a
closed immersion. Then `isZero_rightDerived_one_of_epi` applies. -/
theorem isZero_rightDerived_one_of_epi_of_smul_eq_zero {Z X : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞)) {E G : X.Modules} (p : E ⟶ G)
    [Epi p] (hG : ∀ (U : X.Opens) (a : Γ(X, U)), (j.app U).hom a = 0 → ∀ m : Γ(G, U), a • m = 0)
    (hE : IsZero (((moduleGlobalSections Z).rightDerived 1).obj
      ((Scheme.Modules.pullback j).obj E))) :
    IsZero (((moduleGlobalSections X).rightDerived 1).obj G) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction j
  have := Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero j G hG
  let g := (Scheme.Modules.pushforward j).map ((Scheme.Modules.pullback j).map p) ≫
    inv (adj.unit.app G)
  have hcomp : adj.unit.app E ≫ g = p := by
    rw [← Category.assoc, ← Functor.comp_map, ← adj.unit.naturality p, Functor.id_map,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have : Epi (adj.unit.app E ≫ g) := hcomp ▸ inferInstance
  have : Epi g := epi_of_epi (adj.unit.app E) g
  exact isZero_rightDerived_one_of_epi hdim g
    (Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_one_sectionsFunctor_pushforward j _ hE)

variable {A : Type u} [CommRing A] {I : Ideal A} {Xn : ℕ → Scheme.{u}}
  (q : ∀ n, Xn n ⟶ adicThickening A I n) (t : ∀ n, Xn n ⟶ Xn (n + 1))
  (hcart : ∀ n, IsPullback (t n) (q n) (q (n + 1)) (adicThickeningSucc A I n))

include hcart in
/-- **The composite inclusion `X₀ ⟶ Xₙ` of the tower is surjective**, being a base change of the
surjective `S₀ ⟶ Sₙ`. -/
theorem surjective_incl (n : ℕ) : Surjective (Stacks.AdicTower.incl t n) := by
  induction n with
  | zero => exact inferInstanceAs (Surjective (𝟙 _))
  | succ n ih =>
    have : Surjective (t n) :=
      MorphismProperty.of_isPullback (hcart n).flip (surjective_adicThickeningSucc A I n)
    exact inferInstanceAs (Surjective (Stacks.AdicTower.incl t n ≫ t n))

include hcart in
/-- **Every member of the tower is homeomorphic to its closed member.** -/
theorem isHomeomorph_incl (n : ℕ) : IsHomeomorph (Stacks.AdicTower.incl t n) := by
  have := Stacks.AdicTower.isClosedImmersion_incl q t hcart n
  have := surjective_incl q t hcart n
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(Stacks.AdicTower.incl t n).isClosedEmbedding.isEmbedding,
      (Stacks.AdicTower.incl t n).surjective⟩

include hcart in
/-- **Every member of the tower has a Noetherian underlying space** when the closed member
does. -/
theorem noetherianSpace_level [NoetherianSpace (Xn 0)] (n : ℕ) : NoetherianSpace (Xn n) :=
  TopologicalSpace.noetherianSpace_of_surjective _ (isHomeomorph_incl q t hcart n).continuous
    (isHomeomorph_incl q t hcart n).surjective

include hcart in
/-- **Every member of the tower has the dimension of its closed member.** -/
theorem topologicalKrullDim_level (n : ℕ) :
    topologicalKrullDim (Xn n) = topologicalKrullDim (Xn 0) :=
  (isHomeomorph_incl q t hcart n).topologicalKrullDim_eq.symm

include hcart in
/-- **The ideal of `X₀` annihilates the ideal sheaf of `Xₙ` in `Xₙ₊₁`.** This is
`Stacks.AdicTower.smul_transitionIdeal_eq_zero`, read at the spelling
`Stacks.ClosedImmersion.idealSheaf` of the ideal sheaf. -/
theorem smul_idealSheaf_eq_zero (n : ℕ) (U : (Xn (n + 1)).Opens) (a : Γ(Xn (n + 1), U))
    (ha : ((Stacks.AdicTower.incl t (n + 1)).app U).hom a = 0)
    (m : (Stacks.ClosedImmersion.idealSheaf (t n).toLRSHom.toShHom).val.obj (op U)) :
    a • m = 0 :=
  Stacks.AdicTower.smul_transitionIdeal_eq_zero q t hcart n U a ha m

include hcart in
/-- **The ideal of `X₀` annihilates every twist of the ideal sheaf of `Xₙ` in `Xₙ₊₁`.** The
braiding exchanges the two factors of `𝓘ₙ ⊗ M`, and a section of the structure sheaf killing the
right-hand factor kills the tensor product sheaf
(`Stacks.SheafOfModules.smul_tensorSheafBifunctor_eq_zero`). -/
theorem smul_idealSheafTensor_eq_zero (n : ℕ) (M : (Xn (n + 1)).Modules)
    (U : (Xn (n + 1)).Opens) (a : Γ(Xn (n + 1), U))
    (ha : ((Stacks.AdicTower.incl t (n + 1)).app U).hom a = 0)
    (m : Γ((show (Xn (n + 1)).Modules from ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Xn (n + 1)).toRingedSpace).presheaf, ((Xn (n + 1)).toRingedSpace).IsSheaf⟩).obj
          (Stacks.ClosedImmersion.idealSheaf (t n).toLRSHom.toShHom)).obj M), U)) :
    a • m = 0 := by
  let e := ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding
    ⟨((Xn (n + 1)).toRingedSpace).presheaf, ((Xn (n + 1)).toRingedSpace).IsSheaf⟩).app
      (Stacks.ClosedImmersion.idealSheaf (t n).toLRSHom.toShHom)).app M
  have hinj : Function.Injective (e.hom.val.app (op U)) := by
    intro x y h
    have := congrArg (e.inv.val.app (op U)) h
    rwa [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
      ← SheafOfModules.comp_val, e.hom_inv_id, SheafOfModules.id_val,
      PresheafOfModules.id_app] at this
  apply hinj
  refine ((e.hom.val.app (op U)).hom.map_smul a m).trans (Eq.trans ?_ (map_zero _).symm)
  refine Stacks.SheafOfModules.smul_tensorSheafBifunctor_eq_zero
    (Opens.grothendieckTopology (Xn (n + 1))) M _ (op U) a (fun {V} g y => ?_) _
  exact smul_idealSheaf_eq_zero q t hcart n V.unop _
    (by
      have h := congrArg (fun φ => φ.hom a) ((Stacks.AdicTower.incl t (n + 1)).naturality g)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero] at h
      exact h)
    y

end Stacks.AdicTowerDimOne

end
