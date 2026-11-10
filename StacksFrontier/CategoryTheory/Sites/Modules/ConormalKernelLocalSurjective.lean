module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationsKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalClassRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalKernelComparison
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonArrow

/-!
# The map on the kernels of two conormal maps, read on local sections

Let `φ₁ : A₁ ⟶ B` and `φ₂ : A₂ ⟶ B` be two presentations of a sheaf of commutative rings on a
site, both locally surjective, and let `ψ : A₁ ⟶ A₂` be a factorisation over the base.  The
induced map `Ker(I₁/I₁² ⟶ B ⊗[A₁] Ω[A₁/R]) ⟶ Ker(I₂/I₂² ⟶ B ⊗[A₂] Ω[A₂/R])` of
`Stacks.Sites.Conormal.kernelMapOfFac` is a map of sheaves of `B`-modules, so whether it is an
isomorphism is a local question; and the sections of a kernel over an object are exactly the
sections of the source killed by the map.  This file reduces the local surjectivity of that map to
a statement about local sections of the kernel ideal.

## Main definitions

* `Stacks.Sites.Conormal.conormalKernelLiftSieve`: the arrows along which a local section of the
  conormal sheaf of the second presentation is the image of the conormal class of a section of
  the kernel ideal of the first whose universal differential vanishes.

## Main results

* `Stacks.Sites.Conormal.exists_covering_conormalClass_eq_tensorDifferential_eq_zero`: a local
  section of the conormal sheaf killed by the conormal map is, on a covering sieve, the conormal
  class of a section of the kernel ideal whose universal differential vanishes.
* `Stacks.Sites.Conormal.isLocallySurjective_kernelMapOfFac`: if that lifting sieve is covering
  for every local section killed by the conormal map, then the map on kernels is locally
  surjective.

## Implementation notes

The lifting condition is packaged as a `CategoryTheory.Sieve` rather than as an existential
statement about some covering sieve, because the proof that it is covering composes several
coverings with `CategoryTheory.GrothendieckTopology.transitive`, which needs the sieve it
concludes about to be named in advance.  It is a sieve — the condition is stable under
precomposition — exactly because the conormal class and the universal differential are
compatible with restriction, which is
`Stacks.Sites.Conormal.conormalClass_map` and `Stacks.Sites.Conormal.tensorDifferential_map`.

Two spellings of the first term of a conormal sequence, as `Stacks.Sites.Conormal.conormalSheaf`
and as the first term of `Stacks.Sites.Conormal.conormalSequence`, are definitionally equal only
at default transparency, so a goal mentioning both is not type-correct at the transparency `rw`
and `simp` check their motives at.  Every step below is therefore composed with `Eq.trans` and
`congrArg`, and the two spellings are crossed by `exact`, which is defeq-tolerant.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), part (2), the homotopy
  that makes the map on kernels independent of the factorisation.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of the
  naive cotangent complex from the presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w z

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- On an essentially small site, sheafification of presheaves of abelian groups exists. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- On an essentially small site, the morphisms of presheaves of abelian groups inverted by
sheafification are exactly the locally bijective ones. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-! ### Lifting one local section of the conormal sheaf -/

section OnePresentation

variable (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective J φ.hom]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A local section of the conormal sheaf killed by the conormal map is locally the conormal
class of a section of the kernel ideal whose universal differential vanishes.**  For a section
`c` of the conormal sheaf over `X` with vanishing image under the conormal map, there is a covering
sieve of `X` on each arrow `g : Y ⟶ X` of which the restriction of `c` is the conormal class of a
section of the kernel ideal over `Y` whose universal differential is zero. -/
theorem exists_covering_conormalClass_eq_tensorDifferential_eq_zero (X : C)
    (c : (conormalSequence.{v, u, w, z} J R A B a φ).X₁.val.obj (op X))
    (hc : (conormalSequence.{v, u, w, z} J R A B a φ).f.val.app (op X) c = 0) :
    ∃ S : Sieve X, S ∈ J X ∧ ∀ (Y : C) (g : Y ⟶ X), S g →
      ∃ x : kernelIdeal φ.hom (op Y),
        conormalClass.{v, u, w, z} J R A B a φ (op Y) x =
            (conormalSequence.{v, u, w, z} J R A B a φ).X₁.val.map g.op c ∧
          tensorDifferential.{v, u, w, z} J R A B a φ (op Y) (x : A.obj.obj (op Y)) = 0 := by
  obtain ⟨S, hS, hlift⟩ := exists_covering_conormalClass_eq.{v, u, w, z} J R A B a φ X c
  refine ⟨S, hS, fun Y g hg ↦ ?_⟩
  obtain ⟨x, hx⟩ := hlift Y g hg
  refine ⟨x, hx, ?_⟩
  have hclass := conormalSequence_f_class.{v, u, w, z} J R A B a φ (op Y) x
  have hnat := PresheafOfModules.naturality_apply
    (conormalSequence.{v, u, w, z} J R A B a φ).f.val g.op c
  have hzero : (conormalSequence.{v, u, w, z} J R A B a φ).X₂.val.map g.op
      ((conormalSequence.{v, u, w, z} J R A B a φ).f.val.app (op X) c) = 0 :=
    (congrArg _ hc).trans (map_zero _)
  refine Eq.trans hclass.symm ?_
  refine Eq.trans (congrArg
    ((conormalSequence.{v, u, w, z} J R A B a φ).f.val.app (op Y)) hx) ?_
  exact hnat.trans hzero

end OnePresentation

/-! ### The lifting sieve of a factorisation -/

section Fac

variable (R B A₁ A₂ : Sheaf J CommRingCat.{w}) (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂)
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (ψ : A₁ ⟶ A₂)
  (hψ : ψ ≫ φ₂ = φ₁) (ha : a₁ ≫ ψ = a₂)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

include hψ in
/-- The arrows `g : Y ⟶ X` along which a local section `c` of the conormal sheaf of the second
presentation is the image, under the map of conormal sheaves of the factorisation, of the
conormal class of a section of the kernel ideal of the first presentation whose universal
differential vanishes. -/
def conormalKernelLiftSieve {X : C}
    (c : (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).X₁.val.obj (op X)) : Sieve X where
  arrows Y g := ∃ y : kernelIdeal φ₁.hom (op Y),
    tensorDifferential.{v, u, w, z} J R A₁ B a₁ φ₁ (op Y) (y : A₁.obj.obj (op Y)) = 0 ∧
      (conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).val.app (op Y)
          (conormalClass.{v, u, w, z} J R A₁ B a₁ φ₁ (op Y) y) =
        (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).X₁.val.map g.op c
  downward_closed := by
    rintro Y Z g ⟨y, hyd, hyc⟩ k
    refine ⟨⟨A₁.obj.map k.op (y : A₁.obj.obj (op Y)), map_kernel φ₁.hom k.op y.2⟩, ?_, ?_⟩
    · refine Eq.trans (tensorDifferential_map.{v, u, w, z} J R A₁ B a₁ φ₁ k.op
        (y : A₁.obj.obj (op Y))) ?_
      refine Eq.trans (congrArg
        ((conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).X₂.val.map k.op) hyd) ?_
      exact map_zero ((conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).X₂.val.map k.op).hom
    · have hmap := conormalClass_map.{u, v, w, z} J R A₁ B a₁ φ₁ k.op y
        ⟨A₁.obj.map k.op (y : A₁.obj.obj (op Y)), map_kernel φ₁.hom k.op y.2⟩ rfl
      have hnat := PresheafOfModules.naturality_apply
        (conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).val k.op
        (conormalClass.{v, u, w, z} J R A₁ B a₁ φ₁ (op Y) y)
      refine Eq.trans (congrArg
        ((conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).val.app (op Z)) hmap) ?_
      refine Eq.trans hnat ?_
      refine Eq.trans (congrArg
        ((conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).X₁.val.map k.op) hyc) ?_
      exact ((conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).X₁.val.map_comp_apply g.op k.op c).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include ha in
/-- **Local surjectivity of the map on kernels.**  If, for every local section `c` of the conormal
sheaf of the second presentation killed by the conormal map, the sieve `conormalKernelLiftSieve`
of `c` is covering, then the map `kernelMapOfFac` from the kernel of the first conormal map to the
kernel of the second is locally surjective. -/
theorem isLocallySurjective_kernelMapOfFac
    (hlift : ∀ (X : C) (c : (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).X₁.val.obj (op X)),
      (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f.val.app (op X) c = 0 →
      conormalKernelLiftSieve.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ c ∈ J X) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
        (kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).val) where
  imageSieve_mem := by
    intro X c'
    have hc0 : (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f.val.app (op X)
        ((kernel.ι (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f).val.app (op X) c') = 0 := by
      have hcond : ((kernel.ι (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f ≫
          (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f).val.app (op X)) c' = 0 := by
        refine Eq.trans (congrArg
          (fun t : kernel (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f ⟶
              (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).X₂ ↦ t.val.app (op X) c')
          (kernel.condition (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f)) ?_
        rfl
      exact hcond
    refine J.superset_covering ?_ (hlift X _ hc0)
    intro Y g hg
    obtain ⟨y, hyd, hyc⟩ := hg
    have hfy : (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f.val.app (op Y)
        (conormalClass.{v, u, w, z} J R A₁ B a₁ φ₁ (op Y) y) = 0 :=
      (conormalSequence_f_class.{v, u, w, z} J R A₁ B a₁ φ₁ (op Y) y).trans hyd
    obtain ⟨k, hk⟩ := Stacks.SheafOfModules.exists_kernel_section
      (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f (op Y) _ hfy
    refine ⟨k, Stacks.SheafOfModules.injective_app_kernel_ι
      (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f (op Y) ?_⟩
    have hfac : (kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
        kernel.ι (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f).val.app (op Y) k =
        (kernel.ι (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f ≫
          conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).val.app (op Y) k :=
      congrArg (fun t : kernel (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f ⟶
          conormalSheaf.{v, u, w, z} J A₂ B φ₂ ↦ t.val.app (op Y) k)
        (kernelMapOfFac_comp_ι.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)
    refine Eq.trans hfac ?_
    refine Eq.trans (congrArg
      ((conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).val.app (op Y)) hk) ?_
    refine Eq.trans hyc ?_
    exact (PresheafOfModules.naturality_apply
      (kernel.ι (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f).val g.op c').symm

end Fac

end Stacks.Sites.Conormal

end
