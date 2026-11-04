module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystemProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionAlgebraization

/-!
# The completion functor between the categories of objects with support proper over the base

Let `g : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type and let `𝓘 ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals on the small étale site of `X`.
`AlgebraicGeometry.Space.CoherentAdicSystemProperSupport` cuts out the two full subcategories
`Coh_{support proper over Y}(𝒪_X) ⊆ Coh(𝒪_X)` and
`Coh_{support proper over Y}(X, 𝓘) ⊆ Coh(X, 𝓘)` of equation 76.42.5.1 and proves that the
completion of a coherent module with support proper over `Y` again has support proper over `Y`.
`AlgebraicGeometry.Space.CoherentCompletionFunctor` builds the completion functor
`Coh(𝒪_X) ⟶ Coh(X, 𝓘)` of Stacks 08B4.  This file puts the two together into the arrow of
equation 76.42.5.1 itself,
`Coh_{support proper over Y}(𝒪_X) ⟶ Coh_{support proper over Y}(X, 𝓘)`.

## Main definitions

* `AlgebraicGeometry.Space.completionFunctorProperOver` — the arrow of equation 76.42.5.1: the
  restriction of the completion functor of Stacks 08B4 to the two full subcategories of
  objects whose support is proper over `Y`.

## Main results

* `AlgebraicGeometry.Space.completionFunctorProperOver_obj_obj` and
  `AlgebraicGeometry.Space.completionFunctorProperOver_map` — the arrow is computed by the
  completion functor on the underlying coherent modules.
* `AlgebraicGeometry.Space.essImage_completionFunctorProperOver_of_iso` and
  `AlgebraicGeometry.Space.essImage_completionFunctorProperOver_of_hasProperSupport` — an
  object of `Coh_{support proper over Y}(X, 𝓘)` lies in the essential image of the arrow as
  soon as it is isomorphic, in the ambient category `Coh(X, 𝓘)`, to the completion of a
  coherent module whose support is proper over `Y`.  Essential-image membership therefore does
  not have to be witnessed inside the full subcategory.

## Implementation notes

The support condition cutting out the target is imposed on the term of the system at index `0`,
and the term of `𝓖^∧` there is `𝓖 / 𝓘 ^ 1 𝓖`, so the lifting condition for the functor is
`AlgebraicGeometry.Space.hasProperSupport_idealPowerQuotient` at exponent `1`.

Local Noetherianity of the étale charts of `X`, in the form of the `Fact` instance, and
quasi-coherence of `𝓘` are the hypotheses of the completion functor itself and are carried
unchanged; the restriction to the two full subcategories needs nothing further.

## References

* [Stacks Project, Tag 08B8](https://stacks.math.columbia.edu/tag/08B8)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (g : X ⟶ Y) (hg : IsLocallyOfFiniteType B S hS g)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).Submodule)

/-! ### The arrow of equation 76.42.5.1 -/

/-- **Stacks 08B8, the arrow.**  The completion functor
`Coh_{support proper over Y}(𝒪_X) ⟶ Coh_{support proper over Y}(X, 𝓘)` of
equation 76.42.5.1, the restriction of the completion functor of Stacks 08B4 to the full
subcategories of objects whose support is proper over `Y`.

It is well defined because the completion of a coherent module with support proper over `Y`
has all of its terms supported inside the support of the module, which is
`AlgebraicGeometry.Space.hasProperSupport_idealPowerQuotient`. -/
@[stacks 08B8 "the arrow, restricting the completion functor of Stacks 08B4 to the two full \
subcategories of objects with support proper over the base"]
def completionFunctorProperOver
    [Fact (HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) :
    CoherentModulesProperOver B S hS hX hY g hg ⥤
      CoherentAdicSystemsProperOver B S hS hX hY g hg 𝓘 :=
  ObjectProperty.lift (isCoherentAdicSystemProperOver B S hS hX hY g hg 𝓘)
    (ObjectProperty.ι (isCoherentProperOver B S hS hX hY g hg) ⋙
      completionFunctor B S hS X hX 𝓘 hI)
    fun G => hasProperSupport_idealPowerQuotient B S hS hX hY g hg 𝓘 1 G.obj.obj
      G.obj.property G.property

variable [Fact (HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)

/-- The arrow of equation 76.42.5.1 sends a coherent module with support proper over `Y` to its
completion along `𝓘`. -/
@[simp]
theorem completionFunctorProperOver_obj_obj
    (G : CoherentModulesProperOver B S hS hX hY g hg) :
    ((completionFunctorProperOver B S hS X Y hX hY g hg 𝓘 hI).obj G).obj =
      (completionFunctor B S hS X hX 𝓘 hI).obj G.obj :=
  rfl

/-- The arrow of equation 76.42.5.1 acts on morphisms by the completion functor. -/
@[simp]
theorem completionFunctorProperOver_map
    {G H : CoherentModulesProperOver B S hS hX hY g hg} (a : G ⟶ H) :
    ((completionFunctorProperOver B S hS X Y hX hY g hg 𝓘 hI).map a).hom =
      (completionFunctor B S hS X hX 𝓘 hI).map a.hom :=
  rfl

/-! ### Detecting the essential image in the ambient category -/

/-- **Essential-image membership for the arrow of equation 76.42.5.1 is detected in the ambient
category `Coh(X, 𝓘)`.**  An object of `Coh_{support proper over Y}(X, 𝓘)` isomorphic, as a
coherent `𝓘`-adic system, to the completion of a coherent module with support proper over `Y`
lies in the essential image of the arrow.

Both categories are full subcategories, so an isomorphism of the underlying objects is already
an isomorphism of the objects themselves. -/
theorem essImage_completionFunctorProperOver_of_iso
    (E : CoherentAdicSystemsProperOver B S hS hX hY g hg 𝓘)
    (G : CoherentModulesProperOver B S hS hX hY g hg)
    (e : (completionFunctor B S hS X hX 𝓘 hI).obj G.obj ≅ E.obj) :
    (completionFunctorProperOver B S hS X Y hX hY g hg 𝓘 hI).essImage E :=
  ⟨G, ⟨ObjectProperty.isoMk (isCoherentAdicSystemProperOver B S hS hX hY g hg 𝓘) e⟩⟩

/-- **A coherent `𝓘`-adic system algebraized by a coherent module whose support is proper over
`Y` lies in the essential image of the arrow of equation 76.42.5.1.**

This is the form in which the conclusion of Stacks 08BC is reached: the algebraizing module is
produced in the ambient category `Coh(𝒪_X)` and the properness of its support is established
separately, after which no further compatibility has to be checked. -/
theorem essImage_completionFunctorProperOver_of_hasProperSupport
    (E : CoherentAdicSystemsProperOver B S hS hX hY g hg 𝓘)
    (G : CoherentModules.{u, u} B S hS X hX)
    (hG : HasProperSupport B S hS hX hY g hg ((SheafOfModules.toSheaf _).obj G.obj))
    (e : (completionFunctor B S hS X hX 𝓘 hI).obj G ≅ E.obj) :
    (completionFunctorProperOver B S hS X Y hX hY g hg 𝓘 hI).essImage E :=
  essImage_completionFunctorProperOver_of_iso B S hS X Y hX hY g hg 𝓘 hI E ⟨G, hG⟩ e

/-! ### The support of the source of a map with coherent kernel -/

/-- **The support of the source of a morphism of `𝒪_Z`-modules is contained in the union of the
support of its kernel and the support of its target**, for a morphism of modules coherent on the
small étale site.

On the open complement of the two supports the kernel and the target both vanish, by Stacks
04KB and Stacks 07TZ.  Étale restriction of modules to that open subspace is exact, so it
carries the kernel of the morphism to the kernel of the restricted morphism; the restricted
morphism is therefore a monomorphism, and its target is zero, so its source is zero there.  The
support of a restriction is the inverse image of the support, again by Stacks 04KB, so the
source has no support on the open set. -/
theorem supportOfSheaf_subset_union_kernel (Z : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} [SheafOfModules.IsCoherentOnSite M]
    [SheafOfModules.IsCoherentOnSite N] (a : M ⟶ N) :
    supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf (structureRingSheaf B S hS Z)).obj M) ⊆
      supportOfSheaf B S hS Z.1
          ((SheafOfModules.toSheaf (structureRingSheaf B S hS Z)).obj (kernel a)) ∪
        supportOfSheaf B S hS Z.1
          ((SheafOfModules.toSheaf (structureRingSheaf B S hS Z)).obj N) := by
  classical
  have hkerft : SheafOfModules.IsFiniteTypeOnSite (kernel a) :=
    isFiniteTypeOnSite_kernel B S hS Z a
  have hNft : SheafOfModules.IsFiniteTypeOnSite N :=
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS Z N
  set K := supportOfSheaf B S hS Z.1
    ((SheafOfModules.toSheaf (structureRingSheaf B S hS Z)).obj (kernel a))
  set T := supportOfSheaf B S hS Z.1
    ((SheafOfModules.toSheaf (structureRingSheaf B S hS Z)).obj N)
  have hKcl : IsClosed K :=
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS Z.1 Z.2 (kernel a)
  have hTcl : IsClosed T :=
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS Z.1 Z.2 N
  have hWopen : IsOpen (K ∪ T)ᶜ := (hKcl.union hTcl).isOpen_compl
  have hzero : ∀ P : Modules.{u, u} B S hS Z.1 Z.2,
      supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf (structureRingSheaf B S hS Z)).obj P) ⊆
        K ∪ T → IsZero ((restrictToOpenPoints.{u, u} B S hS Z (K ∪ T)ᶜ hWopen).obj P) :=
    fun P hP => isZero_restrictToOpenPoints_of_disjoint_supportOfSheaf B S hS Z P _ hWopen
      (Set.eq_empty_of_forall_notMem fun _ hx => hx.1 (hP hx.2))
  have hNzero := hzero N Set.subset_union_right
  have hmono := mono_restrictToOpenPoints_map_of_isZero_kernel B S hS Z _ hWopen a
    (hzero (kernel a) Set.subset_union_left)
  have hMzero : IsZero ((restrictToOpenPoints.{u, u} B S hS Z (K ∪ T)ᶜ hWopen).obj M) := by
    rw [IsZero.iff_id_eq_zero]
    refine (cancel_mono ((restrictToOpenPoints.{u, u} B S hS Z (K ∪ T)ᶜ hWopen).map a)).1 ?_
    rw [Category.id_comp, zero_comp]
    exact hNzero.eq_zero_of_tgt _
  have hsupp : supportOfSheaf B S hS (openPointsSubspace B S hS Z (K ∪ T)ᶜ hWopen).1
      ((SheafOfModules.toSheaf _).obj
        ((restrictToOpenPoints.{u, u} B S hS Z (K ∪ T)ᶜ hWopen).obj M)) = ∅ :=
    (supportOfSheaf_eq_empty_iff_isZero B S hS _ _).2 hMzero
  rw [restrictToOpenPoints, supportOfSheaf_toSheaf_etaleModulePullback] at hsupp
  intro x hx
  by_contra hxn
  have hxr : x ∈ Set.range (pointsMap B S hS
      (openPointsSubspace B S hS Z (K ∪ T)ᶜ hWopen).1
      (openPointsSubspaceHom B S hS Z (K ∪ T)ᶜ hWopen).hom) := by
    rw [range_pointsMap_openPointsSubspaceHom]
    exact hxn
  obtain ⟨z, hz⟩ := hxr
  refine Set.eq_empty_iff_forall_notMem.mp hsupp z ?_
  rw [Set.mem_preimage, hz]
  exact hx

/-- **The support clause of Stacks 08BC.**  Let `E` be a coherent `𝓘`-adic system which is
algebraized by a coherent `𝒪_X`-module `G`, and suppose `G` carries a morphism `a : G ⟶ N` to a
coherent module whose support is proper over `Y` whose kernel also has support proper over `Y`.
Then `E` lies in the essential image of the arrow of equation 76.42.5.1.

The support of `G` is contained in the union of the support of the kernel of `a` and the support
of `N`, so it is proper over `Y` by Stacks 0CZH in the form
`AlgebraicGeometry.Space.hasProperSupport_of_subset_union`; `G` therefore lifts to
`Coh_{support proper over Y}(𝒪_X)` and the given isomorphism lifts with it.

This is the last paragraph of the proof of Stacks 08BC, where `N` is the module `𝓗` of that
lemma's hypothesis (2) and the kernel of `a` is annihilated by a power of the auxiliary ideal
`𝓚`, hence supported inside a closed subspace proper over the base.  The construction of `G`
itself is *not* provided here; see the module documentation of
`AlgebraicGeometry.Space.CoherentCompletionAlgebraization` for the input it needs. -/
theorem essImage_completionFunctorProperOver_of_kernel
    (E : CoherentAdicSystemsProperOver B S hS hX hY g hg 𝓘)
    (G : CoherentModules.{u, u} B S hS X hX) (N : Modules.{u, u} B S hS X hX)
    [SheafOfModules.IsCoherentOnSite N] (a : G.obj ⟶ N)
    (hN : HasProperSupport B S hS hX hY g hg
      ((SheafOfModules.toSheaf (structureRingSheaf B S hS ⟨X, hX⟩)).obj N))
    (hker : HasProperSupport B S hS hX hY g hg
      ((SheafOfModules.toSheaf (structureRingSheaf B S hS ⟨X, hX⟩)).obj (kernel a)))
    (e : (completionFunctor B S hS X hX 𝓘 hI).obj G ≅ E.obj) :
    (completionFunctorProperOver B S hS X Y hX hY g hg 𝓘 hI).essImage E := by
  have hGft : SheafOfModules.IsFiniteTypeOnSite G.obj :=
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS ⟨X, hX⟩ G.obj
  refine essImage_completionFunctorProperOver_of_hasProperSupport B S hS X Y hX hY g hg 𝓘 hI
    E G (hasProperSupport_of_subset_union B S hS hX hY g hg
      (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X hX G.obj)
      (supportOfSheaf_subset_union_kernel B S hS ⟨X, hX⟩ a) hker hN) e

end AlgebraicGeometry.Space

end
