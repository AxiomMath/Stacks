module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationsKernel
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalClassLocal
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalKernelComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalLocallyBijective

/-!
# The map on the kernels of two conormal maps, read on local sections: the injective half

Let `φ₁ : A₁ ⟶ B` and `φ₂ : A₂ ⟶ B` be two presentations of a sheaf of commutative rings on a
site, both locally surjective, and let `ψ : A₁ ⟶ A₂` be a factorisation over the base.  The
induced map `Ker(I₁/I₁² ⟶ B ⊗[A₁] Ω[A₁/R]) ⟶ Ker(I₂/I₂² ⟶ B ⊗[A₂] Ω[A₂/R])` of
`Stacks.Sites.Conormal.kernelMapOfFac` is a map of sheaves of `B`-modules, so whether it is an
isomorphism is a local question.  This file reduces the local injectivity of that map to a single
statement about the local vanishing of a section of the conormal sheaf.

## Main results

* `Stacks.Sites.Conormal.exists_covering_mem_ker_sq_of_conormalClass_eq_zero`: a section of the
  kernel ideal whose conormal class vanishes lies, on a covering sieve, in the square of the
  kernel ideal.
* `Stacks.Sites.Conormal.isLocallyInjective_kernelMapOfFac`: if the vanishing sieve of a local
  section of the first conormal sheaf is covering whenever that section is killed both by the
  first conormal map and by the map of conormal sheaves of the factorisation, then the map on
  kernels is locally injective.

## Implementation notes

The first statement is local injectivity of the module sheafification unit, read on one
section.  The unit's underlying morphism of presheaves of abelian groups is
`CategoryTheory.toSheafify` on the nose, so its local injectivity is the Mathlib instance for
that morphism, quoted through `inferInstanceAs` rather than re-derived, exactly as
`Stacks.Sites.Conormal.exists_covering_conormalClass_eq` quotes local surjectivity.

The second statement is reduced to the difference of the two sections, through two lemmas about
the sections of a kernel in a category of sheaves of modules: a section of the kernel is killed
by the morphism, and two sections of the kernel agree after restriction as soon as the
restriction of the image of their difference vanishes.  Both are stated for an arbitrary
morphism of sheaves of modules, where no spelling of a conormal sheaf is in play.

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

/-- On an essentially `z`-small site, presheaves of abelian groups in universe `z` admit
sheafification. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- On an essentially `z`-small site, a morphism of presheaves of abelian groups in universe `z`
becomes an isomorphism after sheafification exactly when it is locally bijective. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-! ### Sections of a kernel of sheaves of modules -/

section KernelSections

variable {Rg : Sheaf J RingCat.{w}} {N P : _root_.SheafOfModules.{max w u v z} Rg} (g : N ⟶ P)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The image of a section of `kernel g` under the inclusion is killed by `g`: the composite
`kernel.ι g ≫ g` is the zero morphism, and a composite of morphisms of sheaves of modules is
computed on sections. -/
theorem val_app_kernel_ι_eq_zero (X : Cᵒᵖ) (k : (kernel g).val.obj X) :
    g.val.app X ((kernel.ι g).val.app X k) = 0 := by
  have hcond : ((kernel.ι g ≫ g).val.app X) k = 0 := by
    refine Eq.trans (congrArg (fun t : kernel g ⟶ P ↦ t.val.app X k) (kernel.condition g)) ?_
    rfl
  exact hcond

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Two sections of `kernel g` over an object agree after restriction along an arrow as soon as
the image of their difference restricts to zero in the source of `g`: the inclusion of a kernel
commutes with the restriction maps and is injective on sections. -/
theorem map_eq_of_ι_sub_map_eq_zero {X Y : C} (q : Y ⟶ X)
    (k₁ k₂ : (kernel g).val.obj (op X))
    (h : N.val.map q.op ((kernel.ι g).val.app (op X) (k₁ - k₂)) = 0) :
    (kernel g).val.map q.op k₁ = (kernel g).val.map q.op k₂ := by
  have hnat := PresheafOfModules.naturality_apply (kernel.ι g).val q.op (k₁ - k₂)
  have hsub : (kernel g).val.map q.op (k₁ - k₂) = 0 :=
    Stacks.SheafOfModules.injective_app_kernel_ι g (op Y)
      ((hnat.trans h).trans (map_zero ((kernel.ι g).val.app (op Y)).hom).symm)
  refine sub_eq_zero.mp ?_
  exact (map_sub ((kernel g).val.map q.op).hom k₁ k₂).symm.trans hsub

end KernelSections

/-! ### A vanishing conormal class is locally a member of the square -/

section OnePresentation

variable (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective J φ.hom]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A section of the kernel ideal whose conormal class vanishes lies locally in the square of
the kernel ideal.**  The conormal sheaf is the associated sheaf of `U ↦ I(U)/I(U)²` and the
sheafification unit is locally injective, so the class `f mod I²` is, on a covering sieve,
already zero in `I(U)/I(U)²`; and a class of `I(U)/I(U)²` vanishes exactly when its
representative lies in `I(U)²`. -/
theorem exists_covering_mem_ker_sq_of_conormalClass_eq_zero (X : C)
    (x : kernelIdeal φ.hom (op X))
    (hx : conormalClass.{v, u, w, z} J R A B a φ (op X) x = 0) :
    ∃ S : Sieve X, S ∈ J X ∧ ∀ (Y : C) (g : Y ⟶ X),
      S g → A.obj.map g.op (x : A.obj.obj (op X)) ∈ kernelIdeal φ.hom (op Y) ^ 2 := by
  have hli : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction.{max w u v z}
        (quotientToRingSheaf J A B φ)).unit.app
        ((liftModules.{v, u, w, z} _).obj (conormalPresheaf φ.hom)))) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J
      ((liftModules.{v, u, w, z} _).obj (conormalPresheaf φ.hom)).presheaf))
  refine ⟨_, Presheaf.equalizerSieve_mem J ((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction.{max w u v z}
        (quotientToRingSheaf J A B φ)).unit.app
        ((liftModules.{v, u, w, z} _).obj (conormalPresheaf φ.hom))))
      (ULift.up ((kernelIdeal φ.hom (op X)).toCotangent x)) 0 ?_, fun Y g hg ↦ ?_⟩
  · exact hx.trans (map_zero (AddCommGrpCat.Hom.hom _)).symm
  have hgd : (conormalPresheaf φ.hom).map g.op ((kernelIdeal φ.hom (op X)).toCotangent x) = 0 :=
    (congrArg ULift.down hg).trans (map_zero ((conormalPresheaf φ.hom).map g.op).hom)
  refine (Ideal.toCotangent_eq_zero (kernelIdeal φ.hom (op Y))
    ⟨A.obj.map g.op (x : A.obj.obj (op X)), map_kernel φ.hom g.op x.2⟩).mp ?_
  exact hgd

end OnePresentation

/-! ### Local injectivity of the map on kernels -/

section Fac

variable (R B A₁ A₂ : Sheaf J CommRingCat.{w}) (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂)
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (ψ : A₁ ⟶ A₂)
  (hψ : ψ ≫ φ₂ = φ₁) (ha : a₁ ≫ ψ = a₂)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]
  [hsh : HasSheafify J AddCommGrpCat.{max w u v z}]

include hψ ha in
omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
omit hsh in
/-- **Local injectivity of the map on kernels, from the local vanishing of a section of the
first conormal sheaf.**  Two sections of the kernel of the first conormal map with the same
image differ by a section whose image in the first conormal sheaf is killed by the first
conormal map and by the map of conormal sheaves of the factorisation, because the map on
kernels is the restriction of the latter; so the hypothesis makes that image restrict to zero
on a covering sieve, and the inclusion of a kernel is injective on sections. -/
theorem isLocallyInjective_kernelMapOfFac
    (hvan : ∀ (X : C) (y : (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).X₁.val.obj (op X)),
      (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f.val.app (op X) y = 0 →
      (conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).val.app (op X) y = 0 →
      vanishingSieve (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).X₁.val y ∈ J X) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
        (kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).val) where
  equalizerSieve_mem := by
    intro X k₁ k₂ h
    have hk : (kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).val.app X
        (k₁ - k₂) = 0 := by
      refine Eq.trans (map_sub ((kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ
        ha).val.app X).hom k₁ k₂) ?_
      exact sub_eq_zero.mpr h
    have h1 : (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f.val.app X
        ((kernel.ι (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f).val.app X (k₁ - k₂)) = 0 :=
      val_app_kernel_ι_eq_zero J
        (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f X (k₁ - k₂)
    have hfac : (kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
        kernel.ι (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f).val.app X (k₁ - k₂) =
        (kernel.ι (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f ≫
          conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).val.app X (k₁ - k₂) :=
      congrArg (fun t : kernel (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f ⟶
          conormalSheaf.{v, u, w, z} J A₂ B φ₂ ↦ t.val.app X (k₁ - k₂))
        (kernelMapOfFac_comp_ι.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)
    have h2 : (conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).val.app X
        ((kernel.ι (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f).val.app X
          (k₁ - k₂)) = 0 := by
      refine Eq.trans hfac.symm ?_
      refine Eq.trans (congrArg
        ((kernel.ι (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f).val.app X) hk) ?_
      exact map_zero
        ((kernel.ι (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f).val.app X).hom
    refine J.superset_covering ?_ (hvan X.unop
      ((kernel.ι (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f).val.app X (k₁ - k₂)) h1 h2)
    intro Y q hq
    exact map_eq_of_ι_sub_map_eq_zero J
      (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f q k₁ k₂ hq

end Fac

end Stacks.Sites.Conormal

end
