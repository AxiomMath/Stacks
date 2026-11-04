module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionDirectImageOffSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleStalkLargeFiber
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport

/-!
# Modules annihilated by the ideal of a closed immersion vanish off the closed subspace

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `ℐ = ker(i♯) ⊆ 𝒪_X` be the ideal cutting out `Z`. This file records that
an `𝒪_X`-module annihilated by `ℐ` has exactly one section over every étale chart of `X` whose
points avoid the point set of `Z`.

## Main results

* `AlgebraicGeometry.Space.one_mem_kerIdeal_structureSharp_of_isEmpty`: over a chart whose base
  change along `i` has empty underlying scheme, the unit section of `𝒪_X` lies in `ℐ`.
* `AlgebraicGeometry.Space.subsingleton_sections_of_annihilatedByKerIdeal_of_isEmpty` and
  `…_of_chartPreimage_eq_empty`: hence an `ℐ`-annihilated module has at most one section there.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' u' u v

namespace Stacks.SheafOfModules

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{w}}

/-- A sheaf of `R`-modules whose sections over `U` are killed by the unit section of `R` has at
most one section over `U`: the unit acts as the identity. -/
theorem subsingleton_obj_of_one_smul_eq_zero (M : SheafOfModules.{w} R) (U : Dᵒᵖ)
    (h : ∀ m : M.val.obj U, (1 : R.obj.obj U) • m = 0) : Subsingleton (M.val.obj U) :=
  ⟨fun m m' ↦ by rw [← one_smul (R.obj.obj U) m, ← one_smul (R.obj.obj U) m', h m, h m']⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- Over an étale chart of `X` whose base change along `i` has empty underlying scheme, the unit
section of `𝒪_X` lies in the ideal `ℐ = ker(i♯)` cutting out the closed subspace: the sections of
`i_*𝒪_Z` over such a chart form the zero ring, so every section of `𝒪_X` is killed by `i♯`. -/
theorem one_mem_kerIdeal_structureSharp_of_isEmpty (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom) (V : SmallEtale B S hS X.1)
    (hV : IsEmpty ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Z.1).obj ((smallBaseChange B S hS i hi).obj V)))) :
    (1 : (structureRingSheaf B S hS X).obj.obj (op V)) ∈
      (SheafOfModules.kerIdeal (structureSharp B S hS i)).obj (op V) := by
  have := subsingleton_structureRingSheafDirectImage_of_isEmpty B S hS i hi V hV
  rw [SheafOfModules.mem_kerIdeal, RingHom.mem_ker]
  exact Subsingleton.elim _ _

/-- An `𝒪_X`-module annihilated by the ideal cutting out the closed subspace has at most one
section over an étale chart of `X` whose base change along `i` has empty underlying scheme.

The unit section of `𝒪_X` lies in the ideal there, and it acts as the identity. -/
theorem subsingleton_sections_of_annihilatedByKerIdeal_of_isEmpty (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : AnnihilatedByKerIdeal B S hS i M) (V : SmallEtale B S hS X.1)
    (hV : IsEmpty ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Z.1).obj ((smallBaseChange B S hS i hi).obj V)))) :
    Subsingleton (M.val.obj (op V)) := by
  have h1 := one_mem_kerIdeal_structureSharp_of_isEmpty B S hS i hi V hV
  exact Stacks.SheafOfModules.subsingleton_obj_of_one_smul_eq_zero M (op V)
    fun m ↦ hM (op V) 1 h1 m

/-- The geometric form: an `𝒪_X`-module annihilated by the ideal cutting out the closed subspace
has at most one section over an étale chart of `X` whose points avoid the point set of `Z`. -/
theorem subsingleton_sections_of_annihilatedByKerIdeal_of_chartPreimage_eq_empty (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : AnnihilatedByKerIdeal B S hS i M) (V : SmallEtale B S hS X.1)
    (hV : chartPreimage B S hS i V = ∅) :
    Subsingleton (M.val.obj (op V)) :=
  subsingleton_sections_of_annihilatedByKerIdeal_of_isEmpty B S hS i hi M hM V
    (isEmpty_smallBaseChange_of_disjoint_range B S hS i hi V hV)

/-! ### The support of such a module -/

attribute [local instance] pointTopology

/-- **The support of an abelian sheaf vanishing off the closed subspace.** An abelian sheaf on
the small étale site of `X` with at most one section over every chart whose points avoid the
point set of `Z` has support contained in the point set of `Z`.

By part (6) of Stacks 04KB the support of a sheaf is the union of the images of the supports of
its sections, and the complement of the preimage of the point set of `Z` is an open — the
preimage is closed for a closed immersion — on which every section restricts to zero, hence is
contained in the largest open zero locus of that section. -/
theorem supportOfSheaf_subset_range_of_subsingleton_sections (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{v})
    (hF : ∀ W : SmallEtale B S hS X.1, chartPreimage B S hS i W = ∅ →
      Subsingleton (F.obj.obj (op W))) :
    supportOfSheaf B S hS X.1 F ⊆ Set.range (pointsMap B S hS Z.1 i.hom) := by
  rw [supportOfSheaf_eq_iUnion_image_supportOfSection B S hS X.1 X.property]
  simp only [Set.iUnion_subset_iff]
  intro V σ y hy
  obtain ⟨v, hv, rfl⟩ := hy
  by_contra hmem
  refine hv ((largestOpenZeroLocus_maximal B S hS X.1 F V σ
    ⟨(chartPreimage B S hS i V)ᶜ, (isClosed_chartPreimage B S hS i hi V).isOpen_compl⟩
    fun W f hf ↦ ?_) hmem)
  have hW : chartPreimage B S hS i W = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun y hy ↦
      hf y (chartPreimage_subset_preimage B S hS i f hy)
  have := hF W hW
  exact Subsingleton.elim _ _

/-- **A module annihilated by the ideal cutting out a closed subspace is supported on it.** For
a closed immersion `i : Z ⟶ X` of algebraic spaces, the support of the abelian sheaf underlying
an `𝒪_X`-module annihilated by `ℐ = ker(i♯)` is contained in the point set of `Z`.

Over a chart whose points avoid the point set of `Z` the unit section of `𝒪_X` lies in `ℐ`, so
the module has no nonzero section there. -/
theorem supportOfSheaf_subset_of_annihilatedByKerIdeal (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : AnnihilatedByKerIdeal B S hS i M) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ⊆
      Set.range (pointsMap B S hS Z.1 i.hom) :=
  supportOfSheaf_subset_range_of_subsingleton_sections B S hS i hi _ fun W hW ↦
    subsingleton_sections_of_annihilatedByKerIdeal_of_chartPreimage_eq_empty B S hS i hi.rep M
      hM W hW

/-- **The geometric stalks of such a module vanish off the closed subspace.** For a closed
immersion `i : Z ⟶ X` of algebraic spaces, the geometric stalk of an `𝒪_X`-module annihilated
by `ℐ = ker(i♯)` is zero at every geometric point of `X` whose image misses the point set
of `Z`.

A nonzero geometric stalk puts the point it lies over in the support of the underlying abelian
sheaf (Stacks 04KA), which the previous statement confines to the point set of `Z`. -/
theorem subsingleton_geometricModuleStalk_of_annihilatedByKerIdeal_of_notMem (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : AnnihilatedByKerIdeal B S hS i M) (x : GeometricPoint B S hS X.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Z.1 i.hom)) :
    Subsingleton (geometricModuleStalk B S hS X x M) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  exact hx (supportOfSheaf_subset_of_annihilatedByKerIdeal B S hS i hi M hM
    ((mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X M x.image).mpr
      ⟨x, rfl, hnt⟩))

/-- **The fibre at a point of the small étale site of such a module vanishes off the closed
subspace.** For a closed immersion `i : Z ⟶ X` of algebraic spaces, the fibre at the point of
Stacks 04K0 determined by a geometric point `x̄` of `X` whose image misses the point set of `Z`
of an `𝒪_X`-module annihilated by `ℐ = ker(i♯)` has at most one element.

This is the previous statement read through the two comparisons of the geometric stalk with the
fibre: `AlgebraicGeometry.Space.geometricModuleStalkAddEquiv` and
`Stacks.moduleStalkLargeFiberAddEquiv`. It is the form the conservativity of
`AlgebraicGeometry.Space.isIso_of_isIso_geometricModuleStalk` consumes. -/
theorem subsingleton_sheafModuleFiber_of_annihilatedByKerIdeal_of_notMem (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : AnnihilatedByKerIdeal B S hS i M) (x : GeometricPoint B S hS X.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Z.1 i.hom)) :
    Subsingleton ((Stacks.sheafModuleFiber (etaleSitePoint B S hS X.1 x X.2)
      (structureRingSheaf B S hS X)).obj M) := by
  have hzero := subsingleton_geometricModuleStalk_of_annihilatedByKerIdeal_of_notMem
    B S hS i hi M hM x hx
  refine ⟨fun c c' ↦ ?_⟩
  refine (Stacks.moduleStalkLargeFiberAddEquiv (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O M).symm.injective ?_
  refine (geometricModuleStalkAddEquiv B S hS X x M).injective ?_
  exact hzero.elim _ _

end AlgebraicGeometry.Space

end
