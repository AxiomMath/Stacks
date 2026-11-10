module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Quasi-coherent modules on a site, and the Grothendieck axioms

Stacks 077V asserts that the category `QCoh(𝒪_X)` of quasi-coherent modules on an algebraic
space is a Grothendieck abelian category.  This file reduces that assertion to the closure
properties of quasi-coherence inside the ambient category of all modules, and discharges the
one closure property that needs no geometry: the zero module is quasi-coherent.

## Main results

* `SheafOfModules.IsQuasicoherentOnSite.of_isZero`: a zero sheaf of modules is quasi-coherent,
  on any site and over any sheaf of rings.
* `SheafOfModules.isQuasicoherentOnSite_containsZero`: the object property of quasi-coherence
  contains a zero object, as `CategoryTheory.ObjectProperty.ContainsZero` requires.
* `SheafOfModules.preservesFiniteLimits_ι_isQuasicoherentOnSite`: once quasi-coherence is
  closed under kernels and finite products, the inclusion of the quasi-coherent modules into
  all modules is left exact.
* `SheafOfModules.abelian_fullSubcategory_isQuasicoherentOnSite` and
  `SheafOfModules.isGrothendieckAbelian_fullSubcategory_isQuasicoherentOnSite`: the two
  conclusions of Stacks 077V, part (1), from those closure properties together with a
  separator.
* `AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` and
  `AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure`: the same
  two statements for the small étale ringed site of an algebraic space.
* `AlgebraicGeometry.Space.hasSheafify_smallEtaleRingedSite_addCommGrpCat` and
  `AlgebraicGeometry.Space.wEqualsLocallyBijective_smallEtaleRingedSite_addCommGrpCat`: the two
  sheafification hypotheses of those statements hold in every module universe at least
  `u + 1`.

## Implementation notes

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, Stacks 03DL(6) in the
universe-flexible form of `StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite`, and
the ambient abelian structure on all modules is the one of Stacks 03DB, whose module, ring and
site universes are independent.  Nothing is restated.

The reduction is Mathlib's instance making a full subcategory of an abelian category abelian as
soon as the defining property contains zero and is closed under kernels, cokernels and finite
products, together with `CategoryTheory.HasExactColimitsOfShape.domain_of_functor`, which pulls
exactness of filtered colimits back along the inclusion.  So what the source proof of Stacks
077V supplies beyond formal category theory is exactly four inputs, and they appear as
hypotheses here:

* closure of quasi-coherence under kernels, under cokernels and under finite products — the
  three parts of Stacks 03M1 for an algebraic space, whose site-level form is Stacks 0GNB(3);
* closure under filtered colimits, the colimit part of Stacks 03M1;
* a separator, which the source obtains from a groupoid presentation of the space through
  Stacks 03M3 and the cardinal bound of Stacks 077U;
* local smallness of the ambient module category, which is a universe hypothesis rather than
  mathematics: the small étale site of an algebraic space over `Scheme.{u}` has its objects in
  `Type (u + 1)`, so a hom type of modules on it is a priori only `Type (u + 1)`-small, while
  `CategoryTheory.IsGrothendieckAbelian.{u}` asks for `Type u`-smallness.

Closure under zero is the one input that is formal, and it is proved here: a zero module is the
cokernel of the zero map between two empty coproducts of copies of the structure sheaf, and the
covering witnessing quasi-coherence may be taken to be the identity.  The three auxiliary
lemmas about zero objects belong with `SheafOfModules.uliftForPresentation` in
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite`; they are here only to keep that
file untouched.

The module universe of the geometric statements is not free.  The ambient category of modules
on the small étale ringed site of an algebraic space is abelian only when presheaves of abelian
groups valued in the module universe have sheafifications on that site and sheafification
inverts exactly the locally bijective morphisms.  Both hold at the universe `u` of the schemes,
where they are the instances of `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian` obtained
from essential smallness of the site, and both hold in every universe at least `u + 1`, where
they are the two theorems listed above; so the geometric statements carry them as hypotheses
rather than fixing a universe.  At a module universe below `u + 1` and different from `u`
neither is available, and that is the only reason the module universe of Stacks 077V cannot be
taken free here.

## References

* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- A section of a zero sheaf of modules is zero. -/
theorem eq_zero_of_isZero {M : SheafOfModules.{m} R} (hM : IsZero M) (X : Cᵒᵖ)
    (x : M.val.obj X) : x = 0 := by
  have h : (𝟙 M : M ⟶ M) = 0 := (IsZero.iff_id_eq_zero M).1 hM
  have h2 := congrArg (fun k : M ⟶ M => k.val.app X x) h
  simpa [show (0 : M ⟶ M).val = 0 from rfl] using h2

/-- The universe lift used for global presentations carries a zero sheaf of modules to a zero
sheaf of modules: its sections are universe lifts of zero modules. -/
theorem isZero_uliftForPresentation {M : SheafOfModules.{m} R} (hM : IsZero M) :
    IsZero (uliftForPresentation.{u, v, r, m, t} M) := by
  rw [IsZero.iff_id_eq_zero]
  ext X x
  change x = 0
  exact ULift.ext (eq_zero_of_isZero hM X x.down)

/-- Restriction to a slice of the site carries a zero sheaf of modules to a zero sheaf of
modules: it preserves the zero morphisms, hence the identity of a zero object. -/
theorem isZero_over {M : SheafOfModules.{m} R} (hM : IsZero M) (U : C) :
    IsZero (M.over U) := by
  have : (overFunctor R U).PreservesZeroMorphisms := ⟨fun _ _ => by ext X x; rfl⟩
  exact (overFunctor R U).map_isZero hM

/-- A zero sheaf of modules has a global presentation: it is the cokernel of the zero map
between two empty coproducts of copies of the structure sheaf. -/
theorem hasGlobalPresentation_of_isZero {M : SheafOfModules.{m} R} (hM : IsZero M) :
    M.HasGlobalPresentation := by
  have hP : IsZero (uliftForPresentation.{u, v, r, m, max u v r} M) :=
    isZero_uliftForPresentation hM
  refine ⟨PEmpty.{max u v r m + 1}, PEmpty.{max u v r m + 1},
    uliftForPresentation.{u, v, r, m, max u v r} M,
    uliftForPresentation.{u, v, r, m, max u v r} M,
    fun i => i.elim, fun i => i.elim, ⟨?_⟩, ⟨?_⟩, 0, 0, by rw [zero_comp], ⟨?_⟩⟩
  · exact Cofan.IsColimit.mk _ (fun _ => 0) (fun _ j => j.elim)
      (fun _ k _ => hP.eq_of_src k 0)
  · exact Cofan.IsColimit.mk _ (fun _ => 0) (fun _ j => j.elim)
      (fun _ k _ => hP.eq_of_src k 0)
  · exact Cofork.IsColimit.mk _ (fun _ => 0)
      (fun s => by rw [comp_zero]; exact hP.eq_of_src 0 s.π)
      (fun _ k _ => hP.eq_of_src k 0)

/-- A zero sheaf of modules is quasi-coherent: every object of the site is covered by itself,
and the restriction of a zero module to any slice is again zero, hence globally presented. -/
theorem IsQuasicoherentOnSite.of_isZero {M : SheafOfModules.{m} R} (hM : IsZero M) :
    M.IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    refine ⟨ULift.{max u v} PUnit, fun _ => U, fun _ => 𝟙 U, ?_,
      fun _ => hasGlobalPresentation_of_isZero (isZero_over hM U)⟩
    have htop : Sieve.ofArrows (fun _ : ULift.{max u v} PUnit => U) (fun _ => 𝟙 U) = ⊤ := by
      refine le_antisymm le_top fun Z g _ => ?_
      rw [Sieve.mem_ofArrows_iff]
      exact ⟨ULift.up PUnit.unit, g, by simp⟩
    rw [htop]
    exact J.top_mem U

/-- Quasi-coherence of sheaves of modules contains a zero object. -/
instance isQuasicoherentOnSite_containsZero [HasZeroObject (SheafOfModules.{m} R)] :
    (isQuasicoherentOnSite.{u, v, r, m} R).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := SheafOfModules.{m} R)
    exact ⟨Z, hZ, IsQuasicoherentOnSite.of_isZero hZ⟩

section Reduction

variable (R)
variable [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderKernels]
  [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderCokernels]
  [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderFiniteProducts]

/-- The inclusion of the quasi-coherent modules into all modules is left exact, as soon as
quasi-coherence is closed under kernels and finite products: it then creates kernels, and a
functor between preadditive categories preserving kernels preserves all finite limits. -/
theorem preservesFiniteLimits_ι_isQuasicoherentOnSite :
    PreservesFiniteLimits (isQuasicoherentOnSite.{u, v, r, m} R).ι :=
  have : ∀ ⦃X Y : (isQuasicoherentOnSite.{u, v, r, m} R).FullSubcategory⦄ (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) (isQuasicoherentOnSite.{u, v, r, m} R).ι :=
    fun {_ _} f => ObjectProperty.preservesKernels_ι _ f
  CategoryTheory.Functor.preservesFiniteLimits_of_preservesKernels _

/-- **Stacks 077V, part (1), abelian structure, reduced.**  The quasi-coherent modules on a
site form an abelian category as soon as quasi-coherence is closed under kernels, cokernels
and finite products.  Closure under zero is `SheafOfModules.isQuasicoherentOnSite_containsZero`
and is not a hypothesis. -/
@[instance_reducible] noncomputable def abelian_fullSubcategory_isQuasicoherentOnSite :
    Abelian (isQuasicoherentOnSite.{u, v, r, m} R).FullSubcategory :=
  inferInstance

/-- **Stacks 077V, part (1), reduced.**  The quasi-coherent modules on a site form a
Grothendieck abelian category as soon as quasi-coherence is closed under kernels, cokernels,
finite products and filtered colimits, the ambient module category is locally small, and the
quasi-coherent modules have a separator.

Exactness of the filtered colimits is not a hypothesis: they are computed in the ambient
category of all modules, where they are exact by Stacks 03DB, and the inclusion is left exact
by `SheafOfModules.preservesFiniteLimits_ι_isQuasicoherentOnSite` and reflects finite limits
because it is fully faithful. -/
theorem isGrothendieckAbelian_fullSubcategory_isQuasicoherentOnSite
    [LocallySmall.{m} (SheafOfModules.{m} R)]
    (hfc : ∀ (K : Type m) [SmallCategory K] [IsFiltered K],
      (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderColimitsOfShape K)
    [HasSeparator (isQuasicoherentOnSite.{u, v, r, m} R).FullSubcategory] :
    IsGrothendieckAbelian.{m} (isQuasicoherentOnSite.{u, v, r, m} R).FullSubcategory := by
  have hsmall : LocallySmall.{m} (isQuasicoherentOnSite.{u, v, r, m} R).FullSubcategory :=
    locallySmall_of_faithful (isQuasicoherentOnSite.{u, v, r, m} R).ι
  have hcolim : HasFilteredColimitsOfSize.{m, m}
      (isQuasicoherentOnSite.{u, v, r, m} R).FullSubcategory :=
    ⟨fun K _ _ => have := hfc K; inferInstance⟩
  have hι := preservesFiniteLimits_ι_isQuasicoherentOnSite R
  have hab5 : AB5OfSize.{m, m} (isQuasicoherentOnSite.{u, v, r, m} R).FullSubcategory :=
    ⟨fun K _ _ => have := hfc K
      HasExactColimitsOfShape.domain_of_functor K
        (isQuasicoherentOnSite.{u, v, r, m} R).ι⟩
  exact ⟨hsmall, hcolim, hab5, inferInstance⟩

end Reduction

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Presheaves of abelian groups on the small étale ringed site of an algebraic space over
`Scheme.{u}` have sheafifications in every universe at least `u + 1`: the site has its objects
in `Type (u + 1)` and its morphisms in `Type u`. -/
theorem hasSheafify_smallEtaleRingedSite_addCommGrpCat :
    HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{max (u + 1) m} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat (smallEtaleRingedSite B S hS F hF).J

/-- On the small étale ringed site of an algebraic space, the local equivalences of presheaves
of abelian groups in any universe at least `u + 1` are exactly the locally bijective morphisms;
the site is essentially small at `u`. -/
theorem wEqualsLocallyBijective_smallEtaleRingedSite_addCommGrpCat :
    ((smallEtaleRingedSite B S hS F hF).J).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) m} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u} _

section Closure

variable [HasWeakSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
  [((smallEtaleRingedSite B S hS F hF).J).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderKernels]
  [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels]
  [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderFiniteProducts]

/-- **Stacks 077V, part (1), abelian structure, reduced to Stacks 03M1.**  The quasi-coherent
modules on an algebraic space form an abelian category as soon as quasi-coherence on its small
étale ringed site is closed under kernels, cokernels and finite products.

The two sheafification hypotheses on the module universe are instances at `m = u`, by
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify`, and hold in every universe at
least `u + 1` by `AlgebraicGeometry.Space.hasSheafify_smallEtaleRingedSite_addCommGrpCat` and
`AlgebraicGeometry.Space.wEqualsLocallyBijective_smallEtaleRingedSite_addCommGrpCat`. -/
@[instance_reducible] noncomputable def quasicoherentSheaves_abelian_of_closure :
    Abelian (QuasicoherentSheaves.{u, m} B S hS F hF) :=
  SheafOfModules.abelian_fullSubcategory_isQuasicoherentOnSite _

/-- **Stacks 077V, part (1), reduced to Stacks 03M1, 03M3 and 077U.**  The quasi-coherent
modules on an algebraic space form a Grothendieck abelian category as soon as quasi-coherence
on its small étale ringed site is closed under kernels, cokernels, finite products and filtered
colimits, the modules on that site are locally small, and the quasi-coherent ones have a
separator.

Local smallness is automatic in every module universe at least `u + 1`, where a hom type of
modules on the site is already a type of that universe; at `m = u` it is not, and is the one
hypothesis here that is a universe condition rather than mathematics. -/
theorem quasicoherentSheaves_isGrothendieckAbelian_of_closure
    [LocallySmall.{m} (Modules.{u, m} B S hS F hF)]
    [HasSeparator (QuasicoherentSheaves.{u, m} B S hS F hF)]
    (hfc : ∀ (K : Type m) [SmallCategory K] [IsFiltered K],
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderColimitsOfShape K) :
    IsGrothendieckAbelian.{m} (QuasicoherentSheaves.{u, m} B S hS F hF) :=
  SheafOfModules.isGrothendieckAbelian_fullSubcategory_isQuasicoherentOnSite _ hfc

end Closure

end AlgebraicGeometry.Space

end
