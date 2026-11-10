module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxFreeGraded
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.GradedFiniteTypeTotalSections
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# The global degree bound for a graded module of finite type on affine opens

`Stacks.Coherent.IsFiniteTypeOnAffine` says that a graded module `N` over a sheaf of graded
algebras `𝓟` is generated, over *each* affine open separately, by finitely many homogeneous
sections — with degrees that may vary from one affine open to the next. The presentation that
part (2) of [Stacks, Tag 0897] asks for needs a **single** finite set of degrees `J`, because the
presenting module is `⨁_{j ∈ J} (…) ⊗ 𝓟(-j)` and the direct sum has to be finite.

This file produces that set on a quasi-compact scheme, and with it the first of the two
constructions `Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_epi_over_polyAlgebra` is
waiting for: the canonical homomorphism

  `⨁_{j ∈ J} N_j ⊗_{𝒪_X} 𝓟(-j) ⟶ N`

is an epimorphism in every homogeneous degree.

## The two steps

**Generation over one affine open spreads to a neighbourhood of each of its points.** The
generators found over an affine open `U` generate the sections of `N_n` over `U` only; a section
over a small open inside `U` need not be the restriction of one over `U`. What saves the argument
is quasi-coherence: over a basic open `D(a) ⊆ U` the sections of a quasi-coherent module are the
localization of the sections over `U` away from `a`
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`), so a section
over `D(a)` becomes one coming from `U` after multiplication by a power of `a`, and `a` restricts
to a unit on `D(a)`. This is
isolated as `AlgebraicGeometry.epi_of_forall_exists_surjective_app_affineOpen`, which needs
nothing graded: a morphism into a quasi-coherent module is an epimorphism as soon as it is
surjective on the sections over *one* affine open around each point.

**Quasi-compactness turns finitely many affine opens into one finite set of degrees.** The affine
opens cover `X`, so a quasi-compact `X` is covered by finitely many of them; the union of the
degree sets of their generating families is a finite set `J`, and every point has an affine open
from that cover in which `N` is generated in the degrees of `J`.

## Main results

* `AlgebraicGeometry.epi_of_forall_exists_surjective_app_affineOpen` — **a morphism of
  `𝒪_X`-modules with quasi-coherent target which is surjective on the sections over an affine
  open around each point is an epimorphism.**
* `Stacks.Coherent.degreePresentationHom` — the canonical homomorphism
  `⨁_{j ∈ J} N_j ⊗ 𝓟(-j) ⟶ N`, assembled from the universal property
  `Stacks.Coherent.freeGradedModuleOnDesc` of the summands and the coproduct of graded modules.
* `Stacks.Coherent.surjective_degreePresentationHom_app` — it is surjective on the sections over
  an affine open in whose generating degrees `J` is contained.
* `Stacks.Coherent.exists_finset_degrees_generating_cover` — **the global degree bound.**
* `Stacks.Coherent.exists_finset_epi_degreePresentationHom` — **the canonical homomorphism is a
  degreewise epimorphism for a suitable finite `J`.**

## Implementation notes

The index type of the direct sum is `ULift.{u} {j : ℤ // j ∈ J}`: the summands of
`SheafOfModules.GradedModule.directSum` are indexed by a type in the universe of the sheaves of
modules, and a subtype of `ℤ` lives in `Type 0`.

The degrees in which `N` is generated are recorded by `Stacks.Coherent.degreeGeneratedSet`, which
is `Stacks.Coherent.generatedSet` with the finite set of generators replaced by the condition
that the degree lie in `J` and the generator be an arbitrary section in that degree. That is the
shape the surjectivity proof wants: every product of an arbitrary section of `N_j` with a section
of `𝓟` is literally the image of a pure tensor, so no lifting of the generators is involved, and
the inclusion of the set of `Stacks.Coherent.IsFiniteTypeOnAffine` into it is immediate.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace AlgebraicGeometry

/-- **A morphism into a quasi-coherent module which is surjective on the sections over an affine
open around each point is an epimorphism.**

Surjectivity over the affine open `U` does not by itself place a section over a smaller open in
the image, and that is the whole difficulty: it is quasi-coherence of the target that repairs it.
Over a basic open `D(a) ⊆ U` the sections of `N` are the localization of `Γ(N, U)` away from `a`
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`), so some power
of `a` times the given section
is the restriction of a section over `U`, hence of an image; and `a` restricts to a unit on
`D(a)`, so dividing by that power keeps the section in the image. Shrinking the given open to a
basic open of `U` around the point is
`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`, and the conclusion is then
`Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections`.

The source is arbitrary: nothing is assumed of `M`. -/
public theorem epi_of_forall_exists_surjective_app_affineOpen {X : Scheme.{u}} {M N : X.Modules}
    [N.IsQuasicoherent] (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ t : Γ(N, U), ∃ s : Γ(M, U), φ.app U s = t) :
    Epi φ := by
  refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections φ ?_
  intro W t x hxW
  obtain ⟨U, hU, hxU, hsurj⟩ := h x
  obtain ⟨a, hab, hxa⟩ := hU.exists_basicOpen_le (⟨x, ⟨hxW, hxU⟩⟩ : (W ⊓ U : X.Opens)) hxU
  have haU : X.basicOpen a ≤ U := X.basicOpen_le a
  have hbW : X.basicOpen a ≤ W := hab.trans inf_le_left
  let := moduleOfLE N haU
  have hsmul : ∀ (r : Γ(X, U)) (z : Γ(N, X.basicOpen a)),
      r • z = (X.presheaf.map (homOfLE haU).op r) • z := fun _ _ => rfl
  have hloc : IsLocalizedModule.Away a (restrictₗ N haU) :=
    isLocalizedModule_restrictₗ N hU a rfl haU
  obtain ⟨⟨y, b⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers a) (restrictₗ N haU)
    (N.presheaf.map (homOfLE hbW).op t)
  obtain ⟨k, hk⟩ := b.2
  have hk' : a ^ k = (b : Γ(X, U)) := hk
  obtain ⟨s₀, hs₀⟩ := hsurj y
  have hrk : IsUnit (X.presheaf.map (homOfLE haU).op ((b : Γ(X, U)))) := by
    rw [← hk', map_pow]
    exact (X.toRingedSpace.isUnit_res_basicOpen a).pow k
  obtain ⟨v, hv⟩ := hrk
  have hres : N.presheaf.map (homOfLE haU).op y
      = φ.app (X.basicOpen a) (M.presheaf.map (homOfLE haU).op s₀) := by
    rw [← hs₀]
    have hnat := ConcreteCategory.congr_hom
      (φ.mapPresheaf.naturality (homOfLE haU).op) s₀
    simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hnat
    exact hnat.symm
  have key : (↑v : Γ(X, X.basicOpen a)) • N.presheaf.map (homOfLE hbW).op t
      = φ.app (X.basicOpen a) (M.presheaf.map (homOfLE haU).op s₀) := by
    rw [hv, ← hres, ← hsmul]
    exact hy
  refine ⟨X.basicOpen a, hbW, hxa,
    (↑v⁻¹ : Γ(X, X.basicOpen a)) • M.presheaf.map (homOfLE haU).op s₀, ?_⟩
  change φ.app (X.basicOpen a) ((↑v⁻¹ : Γ(X, X.basicOpen a)) •
    M.presheaf.map (homOfLE haU).op s₀) = N.presheaf.map (homOfLE hbW).op t
  rw [Scheme.Modules.Hom.app_smul, ← key, smul_smul, Units.inv_mul, one_smul]

end AlgebraicGeometry

namespace Stacks.Coherent

variable {X : Scheme.{u}} {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-! ### The presentation in the degrees of a finite set -/

/-- The summand `N_j ⊗ 𝓟(-j)` of the presentation of `N` in the degrees of `J`. -/
public abbrev degreeSummand (N : SheafOfModules.GradedModule P) (J : Finset ℤ)
    (k : ULift.{u} {j : ℤ // j ∈ J}) : SheafOfModules.GradedModule P :=
  freeGradedModuleOn (N.piece k.down.1) P k.down.1

/-- **`⨁_{j ∈ J} N_j ⊗ 𝓟(-j)`**, the free graded `𝓟`-module on the homogeneous pieces of `N` in
the degrees of `J`. -/
public abbrev degreePresentation (N : SheafOfModules.GradedModule P) (J : Finset ℤ) :
    SheafOfModules.GradedModule P :=
  SheafOfModules.GradedModule.directSum (degreeSummand N J)

/-- **The canonical homomorphism `⨁_{j ∈ J} N_j ⊗ 𝓟(-j) ⟶ N`**, whose summand in degree `j` is
the extension of the identity of `N_j` along the universal property of `N_j ⊗ 𝓟(-j)`. On a pure
tensor it is the action of `𝓟` on `N`. -/
public def degreePresentationHom (N : SheafOfModules.GradedModule P) (J : Finset ℤ) :
    degreePresentation N J ⟶ N :=
  Cofan.IsColimit.desc (SheafOfModules.GradedModule.directSumIsColimit (degreeSummand N J))
    fun k => freeGradedModuleOnDesc (N.piece k.down.1) (𝟙 (N.piece k.down.1))

/-- The defining property of `Stacks.Coherent.degreePresentationHom` on the summand of degree
`j`. -/
public theorem degreePresentationHom_app_directSumι (N : SheafOfModules.GradedModule P)
    (J : Finset ℤ) (k : ULift.{u} {j : ℤ // j ∈ J}) :
    SheafOfModules.GradedModule.directSumι (degreeSummand N J) k ≫ degreePresentationHom N J
      = freeGradedModuleOnDesc (N.piece k.down.1) (𝟙 (N.piece k.down.1)) := by
  have h := Cofan.IsColimit.fac
    (SheafOfModules.GradedModule.directSumIsColimit (degreeSummand N J))
    (fun k : ULift.{u} {j : ℤ // j ∈ J} =>
      freeGradedModuleOnDesc (N.piece k.down.1) (𝟙 (N.piece k.down.1))) k
  simpa [degreePresentationHom] using h

/-! ### Generation in the degrees of a finite set -/

/-- The set of products of a homogeneous section of `N` of degree in `J` with a homogeneous
section of the algebra, in degree `n`, over the open `U`.

This is `Stacks.Coherent.generatedSet` with the finite set of generators replaced by the pair of
conditions that the degree lie in `J` and the section be arbitrary; the generated set of
`Stacks.Coherent.IsFiniteTypeOnAffine` is contained in it as soon as `J` contains the degrees of
the generators. -/
public def degreeGeneratedSet (N : SheafOfModules.GradedModule P) (J : Finset ℤ) (U : X.Opens)
    (n : ℤ) : Set ((N.piece n).val.obj (op U)) :=
  { t | ∃ j : ℤ, j ∈ J ∧ ∃ (g : (N.piece j).val.obj (op U)) (m : ℤ)
      (a : (P.piece m).val.obj (op U)) (h : j + m = n),
      t = h ▸ N.smul j m (op U) g a }

/-- `degreeGeneratedSet N J U n` is monotone in the set of degrees `J`. -/
public theorem degreeGeneratedSet_mono (N : SheafOfModules.GradedModule P) {J J' : Finset ℤ}
    (hJ : J ⊆ J') (U : X.Opens) (n : ℤ) :
    degreeGeneratedSet N J U n ⊆ degreeGeneratedSet N J' U n := by
  rintro t ⟨j, hj, g, m, a, hh, rfl⟩
  exact ⟨j, hJ hj, g, m, a, hh, rfl⟩

/-- **`⨁_{j ∈ J} N_j ⊗ 𝓟(-j) ⟶ N` is surjective on the sections over an open in whose
generating degrees `J` is contained.**

No lifting is involved: a product `g · a` of an arbitrary homogeneous section `g` of `N_j` with a
homogeneous section `a` of `𝓟` is the image of the pure tensor `g ⊗ a` in the summand of degree
`j`, by `Stacks.Coherent.freeGradedModuleOnDesc_app_tmul`, and the image of a morphism of modules
is an additive subgroup, so it contains the additive closure the hypothesis says is
everything. -/
public theorem surjective_degreePresentationHom_app (N : SheafOfModules.GradedModule P)
    (J : Finset ℤ) (U : X.Opens) (n : ℤ)
    (hgen : AddSubgroup.closure (degreeGeneratedSet N J U n) = ⊤) :
    Function.Surjective (((degreePresentationHom N J).app n).val.app (op U)) := by
  classical
  set ρ : ((degreePresentation N J).piece n).val.obj (op U) →+ (N.piece n).val.obj (op U) :=
    (((degreePresentationHom N J).app n).val.app (op U)).hom.toAddMonoidHom with hρ
  have hle : AddSubgroup.closure (degreeGeneratedSet N J U n) ≤ ρ.range := by
    rw [AddSubgroup.closure_le]
    rintro s ⟨j, hj, g, m, a, h, rfl⟩
    obtain rfl : m = n + -j := by omega
    refine ⟨((SheafOfModules.GradedModule.directSumι (degreeSummand N J)
        (ULift.up ⟨j, hj⟩)).app n).val.app (op U)
      (freeGradedMk (N.piece j) j n (op U) (g ⊗ₜ a)), ?_⟩
    have hcomp : ((SheafOfModules.GradedModule.directSumι (degreeSummand N J)
          (ULift.up ⟨j, hj⟩) ≫ degreePresentationHom N J).app n).val.app (op U)
        (freeGradedMk (N.piece j) j n (op U) (g ⊗ₜ a))
        = ρ (((SheafOfModules.GradedModule.directSumι (degreeSummand N J)
            (ULift.up ⟨j, hj⟩)).app n).val.app (op U)
          (freeGradedMk (N.piece j) j n (op U) (g ⊗ₜ a))) := rfl
    rw [← hcomp, degreePresentationHom_app_directSumι]
    refine (freeGradedModuleOnDesc_app_tmul (N.piece j) (𝟙 (N.piece j)) n (op U) g a).trans ?_
    exact (Stacks.degCast_eq_of_heq (F := fun k => ((N.piece k).val.obj (op U) : Type u)) h
      (SheafOfModules.heq_castHom N.piece (show j + (n + -j) = n by omega) (op U)
        (N.smul j (n + -j) (op U) g a)).symm).symm
  intro t
  have ht : t ∈ AddSubgroup.closure (degreeGeneratedSet N J U n) := by
    rw [hgen]; exact AddSubgroup.mem_top t
  exact hle ht

/-- **A graded module of finite type on affine opens is generated, over each affine open, in
finitely many degrees.** The degrees are those of the finite generating family that
`Stacks.Coherent.IsFiniteTypeOnAffine` supplies over that affine open. -/
public theorem exists_finset_degrees_generating (N : SheafOfModules.GradedModule P)
    (hft : IsFiniteTypeOnAffine N) (U : X.affineOpens) :
    ∃ J : Finset ℤ, ∀ n : ℤ, AddSubgroup.closure (degreeGeneratedSet N J U.1 n) = ⊤ := by
  classical
  obtain ⟨G, hG⟩ := hft U
  refine ⟨G.image Sigma.fst, fun n => eq_top_mono (AddSubgroup.closure_mono ?_) (hG n)⟩
  rintro t ⟨s, hs, m, a, hh, rfl⟩
  exact ⟨s.1, Finset.mem_image_of_mem _ hs, s.2, m, a, hh, rfl⟩

/-- **The global degree bound.** On a quasi-compact scheme one finite set of degrees serves every
point: a graded module of finite type on affine opens is generated, over an affine open around
each point, by its homogeneous pieces in the degrees of a single finite set `J`.

The affine opens cover `X`, so finitely many of them do; `J` is the union of the degree sets of
their generating families, which is where quasi-compactness is the whole content. The affine open
produced for a point is a member of that finite cover, not an arbitrary small neighbourhood —
which is why the passage to a neighbourhood has to be made separately, by
`AlgebraicGeometry.epi_of_forall_exists_surjective_app_affineOpen`. -/
public theorem exists_finset_degrees_generating_cover [CompactSpace X]
    (N : SheafOfModules.GradedModule P) (hft : IsFiniteTypeOnAffine N) :
    ∃ J : Finset ℤ, ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∀ n : ℤ, AddSubgroup.closure (degreeGeneratedSet N J U.1 n) = ⊤ := by
  classical
  choose JU hJU using exists_finset_degrees_generating N hft
  have hcov : TopologicalSpace.IsOpenCover (fun U : X.affineOpens => (U : X.Opens)) :=
    TopologicalSpace.IsOpenCover.mk (AlgebraicGeometry.iSup_affineOpens_eq_top X)
  obtain ⟨σ, hσ⟩ := hcov.exists_finite_of_compactSpace
  refine ⟨σ.biUnion fun U => JU U, fun x => ?_⟩
  obtain ⟨i, hi⟩ := hσ.exists_mem x
  exact ⟨i.1, hi, fun n => eq_top_mono (AddSubgroup.closure_mono (degreeGeneratedSet_mono N
    (fun z hz => Finset.mem_biUnion.2 ⟨i.1, i.2, hz⟩) i.1.1 n)) (hJU i.1 n)⟩

/-- **The canonical homomorphism `⨁_{j ∈ J} N_j ⊗ 𝓟(-j) ⟶ N` is an epimorphism in every
homogeneous degree**, for one finite set of degrees `J`, as soon as `X` is quasi-compact and `N`
is a quasi-coherent graded module of finite type on affine opens.

This is the degreewise epimorphism that part (2) of [Stacks, Tag 0897] asks for, with the
*tautological* middle term: the homogeneous pieces of `N` themselves rather than sums of twists
of an ample invertible module. Replacing `N_j` by such a sum is the remaining step, and the
replacement is a degreewise epimorphism onto this one. -/
public theorem exists_finset_epi_degreePresentationHom [CompactSpace X]
    (N : SheafOfModules.GradedModule P) (hqc : ∀ n : ℤ, (N.piece n).IsQuasicoherent)
    (hft : IsFiniteTypeOnAffine N) :
    ∃ J : Finset ℤ, ∀ n : ℤ,
      Epi (C := X.Modules) ((degreePresentationHom N J).app n) := by
  obtain ⟨J, hJ⟩ := exists_finset_degrees_generating_cover N hft
  refine ⟨J, fun n => ?_⟩
  have := hqc n
  refine AlgebraicGeometry.epi_of_forall_exists_surjective_app_affineOpen _ fun x => ?_
  obtain ⟨U, hxU, hU⟩ := hJ x
  exact ⟨U.1, U.2, hxU, fun t => surjective_degreePresentationHom_app N J U.1 n (hU n) t⟩

end Stacks.Coherent

end
