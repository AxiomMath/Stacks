module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodModules

/-!
# Stability of the sections comparison of a tower under biproducts and kernels

Let `T` be an `Stacks.Algebraization.InfinitesimalTower` over a scheme `Z`, and recall the
comparison

`colim_W Γ(E, W) ⟶ lim_n Γ((T.obj n)^* E, ⊤)`

of `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete`, where `W` runs over the opens of
`Z` containing the support of the tower. This file shows that the class of modules for which the
comparison is an isomorphism is closed under finite biproducts, and that it contains the kernel of
a morphism between two of its members once the kernel inclusion stays injective on the terms of
the tower.

These are the two closure properties the source of [Stacks, Tag 0EK2] uses to pass from condition
(2) of that tag to condition (3): a finite locally free module `ℰ` is placed in a universally
exact sequence `0 → ℰ → (L^{⊗ p})^{⊕ r} → (L^{⊗ q})^{⊕ s}`, and the comparison for `ℰ` is deduced
from the comparison for the powers of the ample module `L`.

## Main results

* `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.bicone` and
  `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.bicone_of_fintype` — the comparison
  holds at the vertex of a bilimit bicone of finitely many modules at which it holds. This is the
  shape the ample-characterisation lemmas of this repository produce.
* `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.biproduct` and
  `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.biprod` — the same statement for
  `⨁ M` and for a binary biproduct `E ⊞ F`.
* `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.of_kernel` — the comparison holds
  at `kernel β` when it holds at the source of `β`, the second clause of the comparison holds at
  the target of `β`, and the pullback of `kernel.ι β` to each term of the tower is injective on
  global sections.
* `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.of_kernel_of_target` and
  `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.of_isLimit_kernelFork` — the same
  statement with the hypothesis on the target packaged as the full comparison, and for an abstract
  kernel fork in place of `kernel β`.

## Implementation notes

Both proofs reduce an assertion about a biproduct or a kernel to the same assertion about the
summands or about the source of the morphism, and the reduction happens on *sections*. Two
ingredients make that possible.

First, acting on a fixed section is additive in the morphism of modules: this is packaged as the
additive maps `Stacks.Algebraization.appAddHom` and `Stacks.Algebraization.pullbackAppAddHom`,
which turn the biproduct identity `∑ j, b.π j ≫ b.ι j = 𝟙 b.pt` into the statement that a section
of `b.pt` is the sum of the sections it induces on the summands. Phrasing the additivity once, as
an `AddMonoidHom`, is what lets `map_sum` do the work; the finite biproduct is then handled
directly, with no induction on the index type.

Second, the sections of a module over a fixed open are the value of a limit-preserving functor
`Stacks.Algebraization.sectionsFunctor` to abelian groups, so the sections of `kernel β` are the
kernel of the map on sections. Preservation of limits is assembled by hand rather than inferred:
instance search does not unfold `sectionsFunctor` to the composite it is defined as.

As in the files this one builds on, `rw` cannot cross the projection separating `Γ(E, W)` from a
presheaf's sections, so the computations with sections are in term mode, using `congrArg` and
`CategoryTheory.NatTrans.naturality_apply` in place of rewrites; additivity of a map on sections is
reached through `CategoryTheory.ConcreteCategory.hom`, since a morphism of abelian groups in the
categorical sense carries no `FunLike` instance of its own. For the same budget reasons every step
is its own small lemma: the pullback functors along the structure morphisms of the tower are
opaque, and a tactic block large enough to mention two of them forces definitional comparisons
that exhaust the kernel.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

/-! ### Acting on a section is additive in the morphism -/

/-- Acting on a fixed section of `E` over `U`, as an additive map in the morphism `E ⟶ F`. -/
public def appAddHom {A : Scheme.{u}} {E F : A.Modules} (U : A.Opens) (x : Γ(E, U)) :
    (E ⟶ F) →+ Γ(F, U) where
  toFun φ := φ.app U x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `Stacks.Algebraization.appAddHom U x` sends a morphism `φ` to `φ.app U x`. -/
@[simp]
public theorem appAddHom_apply {A : Scheme.{u}} {E F : A.Modules} (U : A.Opens) (x : Γ(E, U))
    (φ : E ⟶ F) : appAddHom U x φ = φ.app U x :=
  rfl

/-- Pulling a morphism `E ⟶ F` back along `g` and acting with it on a fixed section of `g^* E`
over `U`, as an additive map in the morphism. -/
public def pullbackAppAddHom {A B : Scheme.{u}} (g : A ⟶ B) {E F : B.Modules} (U : A.Opens)
    (y : Γ((Scheme.Modules.pullback g).obj E, U)) :
    (E ⟶ F) →+ Γ((Scheme.Modules.pullback g).obj F, U) where
  toFun φ := ((Scheme.Modules.pullback g).map φ).app U y
  map_zero' := by rw [Functor.map_zero]; rfl
  map_add' _ _ := by rw [Functor.map_add]; rfl

/-- `Stacks.Algebraization.pullbackAppAddHom g U y` sends a morphism `φ` to the action of its
pullback along `g` on `y`. -/
@[simp]
public theorem pullbackAppAddHom_apply {A B : Scheme.{u}} (g : A ⟶ B) {E F : B.Modules}
    (U : A.Opens) (y : Γ((Scheme.Modules.pullback g).obj E, U)) (φ : E ⟶ F) :
    pullbackAppAddHom g U y φ = ((Scheme.Modules.pullback g).map φ).app U y :=
  rfl

/-- The pullback of a composite of morphisms of modules acts on sections as the composite of the
two pullbacks. -/
public theorem pullback_map_comp_app {A B : Scheme.{u}} (g : A ⟶ B) {E F G : B.Modules}
    (φ : E ⟶ F) (ψ : F ⟶ G) (U : A.Opens) (y : Γ((Scheme.Modules.pullback g).obj E, U)) :
    ((Scheme.Modules.pullback g).map (φ ≫ ψ)).app U y =
      ((Scheme.Modules.pullback g).map ψ).app U
        (((Scheme.Modules.pullback g).map φ).app U y) := by
  rw [Functor.map_comp]
  exact ConcreteCategory.comp_apply (((Scheme.Modules.pullback g).map φ).app U)
    (((Scheme.Modules.pullback g).map ψ).app U) y

/-- The pullback of the identity of a module fixes every section. -/
public theorem pullback_map_id_app {A B : Scheme.{u}} (g : A ⟶ B) (E : B.Modules) (U : A.Opens)
    (y : Γ((Scheme.Modules.pullback g).obj E, U)) :
    ((Scheme.Modules.pullback g).map (𝟙 E)).app U y = y :=
  congrArg (fun χ => Scheme.Modules.Hom.app χ U y) ((Scheme.Modules.pullback g).map_id E)

/-- Restricting a section twice is restricting it once. -/
public theorem presheaf_map_homOfLE_trans {A : Scheme.{u}} (E : A.Modules) {U₁ U₂ U₃ : A.Opens}
    (h₁₂ : U₂ ≤ U₁) (h₂₃ : U₃ ≤ U₂) (h₁₃ : U₃ ≤ U₁) (t : Γ(E, U₁)) :
    E.presheaf.map (homOfLE h₂₃).op (E.presheaf.map (homOfLE h₁₂).op t) =
      E.presheaf.map (homOfLE h₁₃).op t := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-! ### Sections of a biproduct -/

/-- A section of the vertex of a bilimit bicone of modules is the sum of the sections it induces
on the summands. -/
public theorem bicone_app_total {A : Scheme.{u}} {ι : Type*} [Fintype ι] {M : ι → A.Modules}
    {b : Limits.Bicone M} (hb : b.IsBilimit) (U : A.Opens) (x : Γ(b.pt, U)) :
    ∑ j : ι, (b.ι j).app U ((b.π j).app U x) = x := by
  have h : (appAddHom (F := b.pt) U x) (∑ j : ι, b.π j ≫ b.ι j) =
      (appAddHom (F := b.pt) U x) (𝟙 b.pt) := by
    rw [IsBilimit.total hb]
  rw [map_sum] at h
  exact h

/-- The pullback along `g` of a section of the vertex of a bilimit bicone of modules is the sum of
the pullbacks of the sections it induces on the summands. -/
public theorem pullback_bicone_app_total {A B : Scheme.{u}} (g : A ⟶ B) {ι : Type*} [Fintype ι]
    {M : ι → B.Modules} {b : Limits.Bicone M} (hb : b.IsBilimit) (U : A.Opens)
    (y : Γ((Scheme.Modules.pullback g).obj b.pt, U)) :
    ∑ j : ι, ((Scheme.Modules.pullback g).map (b.ι j)).app U
        (((Scheme.Modules.pullback g).map (b.π j)).app U y) = y := by
  have h : (pullbackAppAddHom (F := b.pt) g U y) (∑ j : ι, b.π j ≫ b.ι j) =
      (pullbackAppAddHom (F := b.pt) g U y) (𝟙 b.pt) := by
    rw [IsBilimit.total hb]
  rw [map_sum] at h
  exact (Finset.sum_congr rfl fun j _ =>
    (pullback_map_comp_app g (b.π j) (b.ι j) U y).symm).trans
      (h.trans (pullback_map_id_app g b.pt U y))

/-! ### Sections of a kernel -/

/-- The sections of a module over a fixed open, as a functor to abelian groups. -/
public def sectionsFunctor {Z : Scheme.{u}} (W : Z.Opens) : Z.Modules ⥤ Ab.{u} :=
  Scheme.Modules.toPresheaf Z ⋙ (CategoryTheory.evaluation _ _).obj (op W)

/-- Taking sections over a fixed open is an additive functor. -/
public instance additive_sectionsFunctor {Z : Scheme.{u}} (W : Z.Opens) :
    (sectionsFunctor W).Additive where
  map_add := rfl

/-- Taking sections over a fixed open preserves kernels: it is the composite of the
limit-preserving forgetful functor to presheaves of abelian groups with an evaluation. -/
public instance preservesLimitsOfShape_sectionsFunctor {Z : Scheme.{u}} (W : Z.Opens) :
    PreservesLimitsOfShape WalkingParallelPair (sectionsFunctor W) :=
  haveI : PreservesLimitsOfShape WalkingParallelPair (Scheme.Modules.toPresheaf Z) :=
    inferInstance
  haveI : PreservesLimitsOfShape WalkingParallelPair
      ((CategoryTheory.evaluation (Z.Opens)ᵒᵖ Ab.{u}).obj (op W)) := inferInstance
  comp_preservesLimitsOfShape _ _

/-- A section of `M` over `W` killed by `β` is the image of a section of `kernel β` over `W`. -/
public theorem exists_kernel_section {Z : Scheme.{u}} {M N : Z.Modules} (β : M ⟶ N)
    (W : Z.Opens) (t : Γ(M, W)) (ht : β.app W t = 0) :
    ∃ k : Γ(kernel β, W), (kernel.ι β).app W k = t := by
  refine ⟨(PreservesKernel.iso (sectionsFunctor W) β).inv
    ((AddCommGrpCat.kernelIsoKer ((sectionsFunctor W).map β)).inv
      ⟨t, AddMonoidHom.mem_ker.mpr ht⟩), ?_⟩
  show (sectionsFunctor W).map (kernel.ι β) _ = t
  rw [← ConcreteCategory.comp_apply, PreservesKernel.iso_inv_ι, ← ConcreteCategory.comp_apply,
    AddCommGrpCat.kernelIsoKer_inv_comp_ι]
  rfl

/-- The kernel inclusion is injective on sections. -/
public theorem kernel_ι_app_injective {Z : Scheme.{u}} {M N : Z.Modules} (β : M ⟶ N)
    (W : Z.Opens) : Function.Injective ((kernel.ι β).app W) := by
  have hfac : (sectionsFunctor W).map (kernel.ι β) =
      (PreservesKernel.iso (sectionsFunctor W) β).hom ≫
        kernel.ι ((sectionsFunctor W).map β) := by
    rw [← PreservesKernel.iso_inv_ι (sectionsFunctor W) β, Iso.hom_inv_id_assoc]
  have : Mono ((sectionsFunctor W).map (kernel.ι β)) := by
    rw [hfac]; infer_instance
  exact (AddCommGrpCat.mono_iff_injective _).1 this

namespace InfinitesimalTower

variable {Z : Scheme.{u}} (T : InfinitesimalTower Z)

/-! ### Opens containing the support -/

/-- The support of the tower sits inside the intersection of two opens containing it. -/
public theorem support_subset_inf {W W' : Z.Opens} (hW : T.support ⊆ W)
    (hW' : T.support ⊆ W') : T.support ⊆ (W ⊓ W' : Z.Opens) := by
  rw [Opens.coe_inf]
  exact Set.subset_inter hW hW'

/-- The support of the tower sits inside the infimum of a finite family of opens containing it. -/
public theorem support_subset_iInf {ι : Type*} [Finite ι] {W : ι → Z.Opens}
    (hW : ∀ j, T.support ⊆ W j) : T.support ⊆ (⨅ j, W j : Z.Opens) := by
  rw [Opens.coe_iInf]
  exact Set.subset_iInter hW

/-! ### Stability under finite biproducts -/

/-- Two sections with the same comparison family keep that property after applying a morphism. -/
private theorem sectionsAt_app_eq_of_eq {E F : Z.Modules} (φ : E ⟶ F) {W W' : Z.Opens}
    (hW : T.support ⊆ W) (hW' : T.support ⊆ W') {x : Γ(E, W)} {y : Γ(E, W')}
    (hxy : ∀ n : ℕ, T.sectionsAt E hW n x = T.sectionsAt E hW' n y) (n : ℕ) :
    T.sectionsAt F hW n (φ.app W x) = T.sectionsAt F hW' n (φ.app W' y) :=
  (T.sectionsAt_natural φ hW n x).trans
    ((congrArg (fun v => ((Scheme.Modules.pullback (T.obj n).hom).map φ).app ⊤ v)
      (hxy n)).trans (T.sectionsAt_natural φ hW' n y).symm)

/-- **The comparison is stable under finite biproducts.** If the comparison for the tower `T` is
an isomorphism at each of finitely many modules `M j`, then it is an isomorphism at the vertex of
any bilimit bicone over them.

`Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.bicone` is the same statement for a
merely `Finite` index type and with the bicone an explicit argument. -/
public theorem IsSectionsComplete.bicone_of_fintype {ι : Type*} [Fintype ι] {M : ι → Z.Modules}
    {b : Limits.Bicone M} (hb : b.IsBilimit) (hM : ∀ j, T.IsSectionsComplete (M j)) :
    T.IsSectionsComplete b.pt where
  exists_section s hs := by
    choose V hV t ht using fun j : ι =>
      (hM j).exists_section
        (fun n => ((Scheme.Modules.pullback (T.obj n).hom).map (b.π j)).app ⊤ (s n))
        (T.isCompatible_map (b.π j) hs)
    refine ⟨⨅ j, V j, T.support_subset_iInf hV,
      ∑ j : ι, (b.ι j).app (⨅ k, V k)
        ((M j).presheaf.map (homOfLE (iInf_le V j)).op (t j)), fun n => ?_⟩
    have key : ∀ j : ι, T.sectionsAt b.pt (T.support_subset_iInf hV) n
        ((b.ι j).app (⨅ k, V k) ((M j).presheaf.map (homOfLE (iInf_le V j)).op (t j))) =
        ((Scheme.Modules.pullback (T.obj n).hom).map (b.ι j)).app ⊤
          (((Scheme.Modules.pullback (T.obj n).hom).map (b.π j)).app ⊤ (s n)) := by
      intro j
      refine (T.sectionsAt_natural (b.ι j) (T.support_subset_iInf hV) n _).trans ?_
      exact congrArg
        (fun v => ((Scheme.Modules.pullback (T.obj n).hom).map (b.ι j)).app ⊤ v)
        ((T.sectionsAt_restrict (M j) (iInf_le V j) (hV j) (T.support_subset_iInf hV) n
          (t j)).trans (ht j n))
    exact ((map_sum
        (ConcreteCategory.hom (T.sectionsAt b.pt (T.support_subset_iInf hV) n))
        (fun j : ι => (b.ι j).app (⨅ k, V k)
          ((M j).presheaf.map (homOfLE (iInf_le V j)).op (t j))) Finset.univ).trans
      (Finset.sum_congr rfl fun j _ => key j)).trans
        (pullback_bicone_app_total (T.obj n).hom hb ⊤ (s n))
  eq_of_sectionsAt_eq W W' hW hW' x y hxy := by
    choose V hV k₁ k₂ hres using fun j : ι =>
      (hM j).eq_of_sectionsAt_eq W W' hW hW' ((b.π j).app W x) ((b.π j).app W' y)
        (sectionsAt_app_eq_of_eq T (b.π j) hW hW' hxy)
    have kx : (⨅ j, V j) ⊓ (W ⊓ W') ≤ W := inf_le_right.trans inf_le_left
    have ky : (⨅ j, V j) ⊓ (W ⊓ W') ≤ W' := inf_le_right.trans inf_le_right
    have kv : ∀ j : ι, (⨅ j, V j) ⊓ (W ⊓ W') ≤ V j := fun j => inf_le_left.trans (iInf_le V j)
    have key : ∀ j : ι,
        (b.π j).app ((⨅ j, V j) ⊓ (W ⊓ W')) (b.pt.presheaf.map (homOfLE kx).op x) =
          (b.π j).app ((⨅ j, V j) ⊓ (W ⊓ W')) (b.pt.presheaf.map (homOfLE ky).op y) := by
      intro j
      refine (NatTrans.naturality_apply (b.π j).mapPresheaf (homOfLE kx).op x).trans ?_
      refine Eq.trans ?_
        (NatTrans.naturality_apply (b.π j).mapPresheaf (homOfLE ky).op y).symm
      refine (presheaf_map_homOfLE_trans (M j) (k₁ j) (kv j) kx ((b.π j).app W x)).symm.trans ?_
      refine Eq.trans ?_ (presheaf_map_homOfLE_trans (M j) (k₂ j) (kv j) ky ((b.π j).app W' y))
      exact congrArg (fun v => (M j).presheaf.map (homOfLE (kv j)).op v) (hres j)
    refine ⟨(⨅ j, V j) ⊓ (W ⊓ W'), T.support_subset_inf (T.support_subset_iInf hV)
      (T.support_subset_inf hW hW'), kx, ky, ?_⟩
    exact (bicone_app_total hb ((⨅ j, V j) ⊓ (W ⊓ W'))
        (b.pt.presheaf.map (homOfLE kx).op x)).symm.trans
      ((Finset.sum_congr rfl fun j _ =>
          congrArg (fun v => (b.ι j).app ((⨅ j, V j) ⊓ (W ⊓ W')) v) (key j)).trans
        (bicone_app_total hb ((⨅ j, V j) ⊓ (W ⊓ W'))
          (b.pt.presheaf.map (homOfLE ky).op y)))

/-- **The comparison is stable under finite biproducts**, in the shape the
ample-characterisation lemmas of this repository produce: an explicit bicone over a family
indexed by a finite type, together with the proof that it is a bilimit.

The category of the bicone is pinned to `AlgebraicGeometry.Scheme.Modules Z` rather than left to
elaboration: `CategoryTheory.Limits.Bicone` would otherwise be free to read the family's target as
`SheafOfModules Z.ringCatSheaf`, and the two spellings do not share the `HasZeroMorphisms`
instance a caller needs to state `α ≫ β = 0` against the bicone's summands. -/
public theorem IsSectionsComplete.bicone {κ : Type u} [Finite κ] (M : κ → Z.Modules)
    (b : Limits.Bicone (C := AlgebraicGeometry.Scheme.Modules Z) M) (hb : b.IsBilimit)
    (hM : ∀ j, T.IsSectionsComplete (M j)) : T.IsSectionsComplete b.pt :=
  have : Fintype κ := Fintype.ofFinite κ
  IsSectionsComplete.bicone_of_fintype T hb hM

/-- **The comparison is stable under a finite biproduct.** -/
public theorem IsSectionsComplete.biproduct {ι : Type*} [Fintype ι] (M : ι → Z.Modules)
    [HasBiproduct M] (hM : ∀ j, T.IsSectionsComplete (M j)) : T.IsSectionsComplete (⨁ M) :=
  IsSectionsComplete.bicone_of_fintype T (Limits.biproduct.isBilimit M) hM

/-- **The comparison is stable under a binary biproduct.** -/
public theorem IsSectionsComplete.biprod {E F : Z.Modules} (hE : T.IsSectionsComplete E)
    (hF : T.IsSectionsComplete F) : T.IsSectionsComplete (E ⊞ F) :=
  IsSectionsComplete.bicone_of_fintype T
    ((Limits.BinaryBicone.toBiconeIsBilimit _).symm (Limits.BinaryBiproduct.isBilimit E F))
    (fun j => match j with
      | WalkingPair.left => hE
      | WalkingPair.right => hF)

/-! ### Stability under kernels -/

/-- **The comparison is stable under kernels.** If the comparison for the tower `T` is an
isomorphism at `M`, if two sections of `N` over opens containing the support which induce the same
family on the terms of the tower agree on a smaller open, and if the pullback of `kernel.ι β` to
each term of the tower is injective on global sections, then the comparison is an isomorphism at
`kernel β`.

An abstract kernel of `β` is handled by
`Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.of_isLimit_kernelFork`. -/
public theorem IsSectionsComplete.of_kernel {M N : Z.Modules} (β : M ⟶ N)
    (hM : T.IsSectionsComplete M)
    (hNinj : ∀ (W W' : Z.Opens) (hW : T.support ⊆ W) (hW' : T.support ⊆ W')
      (t : Γ(N, W)) (u : Γ(N, W')),
      (∀ n : ℕ, T.sectionsAt N hW n t = T.sectionsAt N hW' n u) →
      ∃ (W'' : Z.Opens) (_ : T.support ⊆ W'') (h₁ : W'' ≤ W) (h₂ : W'' ≤ W'),
        N.presheaf.map (homOfLE h₁).op t = N.presheaf.map (homOfLE h₂).op u)
    (hpullbackMono : ∀ n : ℕ, Function.Injective
      (((Scheme.Modules.pullback (T.obj n).hom).map (kernel.ι β)).app ⊤)) :
    T.IsSectionsComplete (kernel β) where
  exists_section s hs := by
    obtain ⟨W, hW, t, ht⟩ := hM.exists_section
      (fun n => ((Scheme.Modules.pullback (T.obj n).hom).map (kernel.ι β)).app ⊤ (s n))
      (T.isCompatible_map (kernel.ι β) hs)
    have htop : T.support ⊆ ((⊤ : Z.Opens) : Set Z) := Set.subset_univ _
    have hbeta : ∀ n : ℕ,
        T.sectionsAt N hW n (β.app W t) = T.sectionsAt N htop n (0 : Γ(N, (⊤ : Z.Opens))) := by
      intro n
      refine Eq.trans ?_
        (map_zero (ConcreteCategory.hom (T.sectionsAt N htop n))).symm
      refine (T.sectionsAt_natural β hW n t).trans ?_
      refine (congrArg
        (fun v => ((Scheme.Modules.pullback (T.obj n).hom).map β).app ⊤ v) (ht n)).trans ?_
      refine (pullback_map_comp_app (T.obj n).hom (kernel.ι β) β ⊤ (s n)).symm.trans ?_
      refine Eq.trans (congrArg
        (fun φ => pullbackAppAddHom (T.obj n).hom (⊤ : ((T.obj n).left).Opens) (s n) φ)
        (kernel.condition β)) ?_
      exact map_zero (pullbackAppAddHom (F := N) (T.obj n).hom ⊤ (s n))
    obtain ⟨W'', hW'', h₁, h₂, hres⟩ :=
      hNinj W ⊤ hW htop (β.app W t) (0 : Γ(N, (⊤ : Z.Opens))) hbeta
    have hzero : β.app W'' (M.presheaf.map (homOfLE h₁).op t) = 0 :=
      (NatTrans.naturality_apply β.mapPresheaf (homOfLE h₁).op t).trans
        (hres.trans (map_zero (ConcreteCategory.hom (N.presheaf.map (homOfLE h₂).op))))
    obtain ⟨k, hk⟩ :=
      exists_kernel_section β W'' (M.presheaf.map (homOfLE h₁).op t) hzero
    refine ⟨W'', hW'', k, fun n => hpullbackMono n ?_⟩
    refine (T.sectionsAt_natural (kernel.ι β) hW'' n k).symm.trans ?_
    refine (congrArg (fun v => T.sectionsAt M hW'' n v) hk).trans ?_
    exact (T.sectionsAt_restrict M h₁ hW hW'' n t).trans (ht n)
  eq_of_sectionsAt_eq W W' hW hW' x y hxy := by
    obtain ⟨W'', hW'', k₁, k₂, hres⟩ := hM.eq_of_sectionsAt_eq W W' hW hW'
      ((kernel.ι β).app W x) ((kernel.ι β).app W' y)
      (sectionsAt_app_eq_of_eq T (kernel.ι β) hW hW' hxy)
    refine ⟨W'', hW'', k₁, k₂, kernel_ι_app_injective β W'' ?_⟩
    refine (NatTrans.naturality_apply (kernel.ι β).mapPresheaf (homOfLE k₁).op x).trans ?_
    exact hres.trans
      (NatTrans.naturality_apply (kernel.ι β).mapPresheaf (homOfLE k₂).op y).symm

/-- **The comparison is stable under kernels**, with the hypothesis on the target of `β` packaged
as the full comparison at that target. -/
public theorem IsSectionsComplete.of_kernel_of_target {M N : Z.Modules} (β : M ⟶ N)
    (hM : T.IsSectionsComplete M) (hN : T.IsSectionsComplete N)
    (hpullbackMono : ∀ n : ℕ, Function.Injective
      (((Scheme.Modules.pullback (T.obj n).hom).map (kernel.ι β)).app ⊤)) :
    T.IsSectionsComplete (kernel β) :=
  IsSectionsComplete.of_kernel T β hM hN.eq_of_sectionsAt_eq hpullbackMono

/-- Injectivity of the pullback of a morphism on global sections only depends on the morphism up
to an isomorphism of its source. -/
public theorem injective_pullback_map_app_of_iso {A B : Scheme.{u}} (g : A ⟶ B)
    {K K' N : B.Modules} (e : K ≅ K') (α : K ⟶ N) (α' : K' ⟶ N) (hα : e.hom ≫ α' = α)
    (h : Function.Injective (((Scheme.Modules.pullback g).map α).app (⊤ : A.Opens))) :
    Function.Injective (((Scheme.Modules.pullback g).map α').app (⊤ : A.Opens)) := by
  have hrw : ∀ c : Γ((Scheme.Modules.pullback g).obj K', (⊤ : A.Opens)),
      ((Scheme.Modules.pullback g).map α).app ⊤
          (((Scheme.Modules.pullback g).map e.inv).app ⊤ c) =
        ((Scheme.Modules.pullback g).map α').app ⊤ c := by
    intro c
    refine (congrArg
      (fun φ => pullbackAppAddHom g (⊤ : A.Opens)
        (((Scheme.Modules.pullback g).map e.inv).app ⊤ c) φ) hα).symm.trans ?_
    refine (pullback_map_comp_app g e.hom α' ⊤ _).trans ?_
    exact congrArg (fun v => ((Scheme.Modules.pullback g).map α').app ⊤ v)
      (app_pullback_map_inv_hom g e c)
  intro a b hab
  refine (app_pullback_map_inv_hom g e a).symm.trans ?_
  exact (congrArg (fun v => ((Scheme.Modules.pullback g).map e.hom).app ⊤ v)
    (h ((hrw a).trans (hab.trans (hrw b).symm)))).trans (app_pullback_map_inv_hom g e b)

/-- **The comparison is stable under kernels**, for an abstract kernel fork: if `α : K ⟶ M`
exhibits `K` as the kernel of `β : M ⟶ N`, the comparison is an isomorphism at `M` and at `N`, and
the pullback of `α` to each term of the tower is injective on global sections, then the comparison
is an isomorphism at `K`. -/
public theorem IsSectionsComplete.of_isLimit_kernelFork {K M N : Z.Modules} (α : K ⟶ M)
    (β : M ⟶ N) (w : α ≫ β = 0) (hker : IsLimit (KernelFork.ofι α w))
    (hM : T.IsSectionsComplete M) (hN : T.IsSectionsComplete N)
    (hpullbackMono : ∀ n : ℕ,
      Function.Injective (((Scheme.Modules.pullback (T.obj n).hom).map α).app ⊤)) :
    T.IsSectionsComplete K :=
  IsSectionsComplete.of_iso T
    (IsLimit.conePointUniqueUpToIso hker (kernelIsKernel β)).symm
    (IsSectionsComplete.of_kernel_of_target T β hM hN fun n =>
      injective_pullback_map_app_of_iso (T.obj n).hom
        (IsLimit.conePointUniqueUpToIso hker (kernelIsKernel β)) α (kernel.ι β)
        (IsLimit.conePointUniqueUpToIso_hom_comp hker (kernelIsKernel β)
          WalkingParallelPair.zero)
        (hpullbackMono n))

end InfinitesimalTower

end Stacks.Algebraization

end
