module

public import StacksFrontier.AlgebraicGeometry.ReflexiveStalk.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Stacks, Tag 0AY3: reflexivity is checked on stalks, and on closed-point stalks

Let `X` be a locally Noetherian scheme and `F` a coherent `𝒪_X`-module.  The following are
equivalent: `F` is reflexive; every stalk of `F` is a reflexive module over the local ring at
that point; the stalks of `F` at the *closed* points are reflexive modules.  That is
[Stacks, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3).

## Main results

* `isZero_of_forall_closedPoint_modStalk_eq_zero`: a module of finite type whose stalks vanish
  at every closed point of a locally Noetherian scheme is zero.  This is the geometric input:
  the support of a module of finite type is closed (Tag 056J), and a nonempty closed subset of a
  locally Noetherian scheme contains a closed point (Tag 02IL).
* `isReflexive_of_forall_closedPoint_modStalk`: the implication (3) ⟹ (1).
* `isReflexive_tfae`: **Tag 0AY3**, the three equivalent conditions.

## Implementation notes

The equivalence of (1) and (2) is
`Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_iff_forall_modStalk`, whose
finite-presentation hypotheses are supplied here from coherence of `F` on a locally Noetherian
scheme: `F` itself by Tag 01XZ, and its dual by
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_dualSheaf`, the internal-Hom clause of
Tag 01Y2 at `𝒢 = 𝒪_X`.

(3) ⟹ (1) is the Stacks Project's argument.  Writing `j = toDoubleDual F`, the stalk of `j` is
bijective at every closed point, so the stalks of `kernel j` and `cokernel j` vanish there; both
are coherent by Tag 01BY, hence of finite type, so their supports are closed and, being disjoint
from the closed points, empty.  A module with empty support has vanishing stalks everywhere, so
its zero endomorphism is an isomorphism and the module is zero; then `j` is both a monomorphism
and an epimorphism in the abelian category of `𝒪_X`-modules, hence an isomorphism.

Both stalk-vanishing steps go through the exactness criterion of Tag 01AG,
`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`, applied to the two-term
complexes that say `kernel.ι j` is a monomorphism and `cokernel.π j` an epimorphism: that is what
makes the induced maps of abelian-group stalks a monomorphism and an epimorphism respectively.
`stalkHom` is identified with the underlying map of that stalk functor by
`stalkFunctor_map_apply`.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 02IL](https://stacks.math.columbia.edu/tag/02IL)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X : Scheme.{u}}

/-! ### Stalks of a kernel and of a cokernel

The stalk functor used here is the one Tag 01AG's exactness criterion is stated for; its
underlying map on elements is `stalkHom`.
-/

/-- The functor sending an `𝒪_X`-module to the abelian group underlying its stalk at `x`, in
the spelling of Tag 01AG. -/
private noncomputable abbrev abStalk (X : Scheme.{u}) (x : X) : X.Modules ⥤ AddCommGrpCat.{u} :=
  _root_.AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor (structureSheaf X.sheaf) x

/-- The stalk functor carries the zero morphism to the zero morphism. -/
private theorem abStalk_map_zero (X : Scheme.{u}) (x : X) (A B : X.Modules) :
    (abStalk X x).map (0 : A ⟶ B) = 0 :=
  (_root_.AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor_preservesZeroMorphisms
    (structureSheaf X.sheaf) x).map_zero A B

/-- The underlying map of the stalk functor of Tag 01AG is `stalkHom`. -/
private theorem abStalk_map_apply {F G : X.Modules} (f : F ⟶ G) (x : X) (m : modStalk F x) :
    ConcreteCategory.hom ((abStalk X x).map f) m = stalkHom f x m :=
  stalkFunctor_map_apply f x m

/-- The stalk of the inclusion of a kernel is a monomorphism, by the exactness criterion of
Tag 01AG applied to the complex `0 ⟶ ker f ⟶ F`. -/
private theorem mono_abStalk_map_kernel_ι {F G : X.Modules} (f : F ⟶ G) (x : X) :
    Mono ((abStalk X x).map (kernel.ι f)) := by
  set S : ShortComplex X.Modules :=
    ShortComplex.mk (0 : kernel f ⟶ kernel f) (kernel.ι f) (by simp) with hS
  have hSexact : S.Exact := (S.exact_iff_mono rfl).2 inferInstance
  have hSx := (_root_.AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    (structureSheaf X.sheaf) S).mp hSexact x
  have hf : (_root_.AlgebraicGeometry.SheafOfModules.stalkShortComplex
      (structureSheaf X.sheaf) S x).f = 0 := abStalk_map_zero X x _ _
  exact ((_root_.AlgebraicGeometry.SheafOfModules.stalkShortComplex
    (structureSheaf X.sheaf) S x).exact_iff_mono hf).1 hSx

/-- The stalk of the projection to a cokernel is an epimorphism, by the exactness criterion of
Tag 01AG applied to the complex `G ⟶ coker f ⟶ 0`. -/
private theorem epi_abStalk_map_cokernel_π {F G : X.Modules} (f : F ⟶ G) (x : X) :
    Epi ((abStalk X x).map (cokernel.π f)) := by
  set S : ShortComplex X.Modules :=
    ShortComplex.mk (cokernel.π f) (0 : cokernel f ⟶ cokernel f) (by simp) with hS
  have hSexact : S.Exact := (S.exact_iff_epi rfl).2 inferInstance
  have hSx := (_root_.AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    (structureSheaf X.sheaf) S).mp hSexact x
  have hg : (_root_.AlgebraicGeometry.SheafOfModules.stalkShortComplex
      (structureSheaf X.sheaf) S x).g = 0 := abStalk_map_zero X x _ _
  exact ((_root_.AlgebraicGeometry.SheafOfModules.stalkShortComplex
    (structureSheaf X.sheaf) S x).exact_iff_epi hg).1 hSx

/-- Every element of a zero stalk vanishes. -/
private theorem modStalk_eq_zero_of_isZero (G : X.Modules) (x : X)
    (h : IsZero ((abStalk X x).obj G)) (a : modStalk G x) : a = 0 :=
  (AddCommGrpCat.isZero_iff_subsingleton.mp h).elim a 0

/-- **The stalk of the kernel vanishes where the stalk map is injective.** -/
private theorem modStalk_kernel_eq_zero {F G : X.Modules} (f : F ⟶ G) (x : X)
    (hinj : Function.Injective (stalkHom f x)) (a : modStalk (kernel f) x) : a = 0 := by
  have hfmono : Mono ((abStalk X x).map f) :=
    (AddCommGrpCat.mono_iff_injective ((abStalk X x).map f)).2 fun b c hbc =>
      hinj ((abStalk_map_apply f x b).symm.trans (hbc.trans (abStalk_map_apply f x c)))
  have hcomp : (abStalk X x).map (kernel.ι f) ≫ (abStalk X x).map f = 0 :=
    ((abStalk X x).map_comp (kernel.ι f) f).symm.trans
      ((congrArg (abStalk X x).map (kernel.condition f)).trans (abStalk_map_zero X x _ _))
  have hzero : (abStalk X x).map (kernel.ι f) = 0 :=
    (cancel_mono ((abStalk X x).map f)).1 (hcomp.trans zero_comp.symm)
  have := mono_abStalk_map_kernel_ι f x
  exact modStalk_eq_zero_of_isZero (kernel f) x (.of_mono_eq_zero _ hzero) a

/-- **The stalk of the cokernel vanishes where the stalk map is surjective.** -/
private theorem modStalk_cokernel_eq_zero {F G : X.Modules} (f : F ⟶ G) (x : X)
    (hsurj : Function.Surjective (stalkHom f x)) (a : modStalk (cokernel f) x) : a = 0 := by
  have hfepi : Epi ((abStalk X x).map f) :=
    (AddCommGrpCat.epi_iff_surjective ((abStalk X x).map f)).2 fun n => by
      obtain ⟨m, hm⟩ := hsurj n
      exact ⟨m, (abStalk_map_apply f x m).trans hm⟩
  have hcomp : (abStalk X x).map f ≫ (abStalk X x).map (cokernel.π f) = 0 :=
    ((abStalk X x).map_comp f (cokernel.π f)).symm.trans
      ((congrArg (abStalk X x).map (cokernel.condition f)).trans (abStalk_map_zero X x _ _))
  have hzero : (abStalk X x).map (cokernel.π f) = 0 :=
    (cancel_epi ((abStalk X x).map f)).1 (hcomp.trans comp_zero.symm)
  have := epi_abStalk_map_cokernel_π f x
  exact modStalk_eq_zero_of_isZero (cokernel f) x (.of_epi_eq_zero _ hzero) a

/-! ### A module of finite type with no stalks at the closed points is zero -/

/-- **A module of finite type whose stalks vanish at the closed points is zero.**  Its support
is closed because it is of finite type (Tag 056J), and a nonempty closed subset of a locally
Noetherian scheme meets the closed points (Tag 02IL), so the support is empty; a module with
empty support has vanishing stalks everywhere, and then its zero endomorphism is bijective on
every stalk, hence an isomorphism. -/
public theorem isZero_of_forall_closedPoint_modStalk_eq_zero (X : Scheme.{u})
    [IsLocallyNoetherian X] (G : X.Modules) [G.IsFiniteType]
    (hG : ∀ y : X, y ∈ closedPoints X → ∀ a : modStalk G y, a = 0) :
    IsZero G := by
  have hsupp : _root_.SheafOfModules.supp G = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    obtain ⟨y, hyG, hyclosed⟩ :=
      _root_.AlgebraicGeometry.nonempty_inter_closedPoints_of_isClosed X ⟨z, hz⟩
        (_root_.SheafOfModules.isClosed_supp G)
    obtain ⟨a, ha⟩ := hyG
    exact ha (hG y hyclosed a)
  have hstalk : ∀ (y : X) (a : modStalk G y), a = 0 := by
    intro y a
    by_contra hne
    have hmem : y ∈ _root_.SheafOfModules.supp G := ⟨a, hne⟩
    rw [hsupp] at hmem
    exact hmem
  have hiso : IsIso (0 : G ⟶ G) :=
    isIso_of_bijective_stalkHom _ fun y =>
      ⟨fun a b _ => (hstalk y a).trans (hstalk y b).symm,
        fun n => ⟨0, (hstalk y _).trans (hstalk y n).symm⟩⟩
  refine (IsZero.iff_id_eq_zero G).2 ?_
  calc (𝟙 G) = inv (0 : G ⟶ G) ≫ (0 : G ⟶ G) := (IsIso.inv_hom_id (0 : G ⟶ G)).symm
    _ = 0 := comp_zero

/-! ### Tag 0AY3 -/

/-- **The implication (3) ⟹ (1) of Stacks, Tag 0AY3.**  A coherent module on a locally
Noetherian scheme whose stalks at the closed points are reflexive modules is reflexive. -/
public theorem isReflexive_of_forall_closedPoint_modStalk (X : Scheme.{u})
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (h : ∀ x : X, x ∈ closedPoints X →
      Module.IsReflexive (ringStalk X.sheaf x) (modStalk F x)) :
    IsReflexive F := by
  have hfp : F.IsFinitePresentation :=
    _root_.Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent' F
  have hdfp : (dualSheaf F).IsFinitePresentation :=
    isFinitePresentation_dualSheaf F
  have hdcoh : (dualSheaf F).IsCoherent := ReflexiveEquivalence.isCoherent_dualSheaf F
  have hddcoh : (dualSheaf (dualSheaf F)).IsCoherent :=
    ReflexiveEquivalence.isCoherent_dualSheaf (dualSheaf F)
  have hbij : ∀ y : X, y ∈ closedPoints X →
      Function.Bijective (stalkHom (toDoubleDual F) y) := fun y hy =>
    (bijective_stalkHom_toDoubleDual_iff F y).mpr (h y hy)
  have hKc : (kernel (toDoubleDual F)).IsCoherent :=
    _root_.SheafOfModules.kernel_isCoherent (toDoubleDual F)
  have hCc : (cokernel (toDoubleDual F)).IsCoherent :=
    _root_.SheafOfModules.cokernel_isCoherent (toDoubleDual F)
  have hKft : (kernel (toDoubleDual F)).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
  have hCft : (cokernel (toDoubleDual F)).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
  have hK : IsZero (kernel (toDoubleDual F)) :=
    isZero_of_forall_closedPoint_modStalk_eq_zero X (kernel (toDoubleDual F))
      fun y hy a => modStalk_kernel_eq_zero (toDoubleDual F) y (hbij y hy).1 a
  have hC : IsZero (cokernel (toDoubleDual F)) :=
    isZero_of_forall_closedPoint_modStalk_eq_zero X (cokernel (toDoubleDual F))
      fun y hy a => modStalk_cokernel_eq_zero (toDoubleDual F) y (hbij y hy).2 a
  have hmono : Mono (toDoubleDual F) :=
    (CategoryTheory.Preadditive.mono_iff_isZero_kernel (toDoubleDual F)).2 hK
  have hepi : Epi (toDoubleDual F) :=
    (CategoryTheory.Preadditive.epi_iff_isZero_cokernel (toDoubleDual F)).2 hC
  exact isIso_of_mono_of_epi (toDoubleDual F)

/-- **Stacks Project, Tag 0AY3.**  For a coherent module `F` on a locally Noetherian scheme
`X`, the following are equivalent:

1. `F` is reflexive, that is, the canonical map `F ⟶ F^∨∨` is an isomorphism;
2. for every point `x` of `X` the stalk `F_x` is a reflexive `𝒪_{X,x}`-module;
3. the same for every *closed* point `x` of `X`.

Integrality of `X` is not needed: reflexivity of a module of finite presentation is detected on
stalks over an arbitrary commutative local ring. -/
@[stacks 0AY3]
public theorem isReflexive_tfae (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] :
    [IsReflexive F,
      ∀ x : X, Module.IsReflexive (ringStalk X.sheaf x) (modStalk F x),
      ∀ x : X, x ∈ closedPoints X →
        Module.IsReflexive (ringStalk X.sheaf x) (modStalk F x)].TFAE := by
  have hfp : F.IsFinitePresentation :=
    _root_.Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent' F
  have hdfp : (dualSheaf F).IsFinitePresentation :=
    isFinitePresentation_dualSheaf F
  tfae_have 1 → 2 := fun hF => module_isReflexive_modStalk F hF
  tfae_have 2 → 3 := fun h x _ => h x
  tfae_have 3 → 1 := fun h => isReflexive_of_forall_closedPoint_modStalk X F h
  tfae_finish

end Stacks.AlgebraicGeometry.ReflexiveModules

end
