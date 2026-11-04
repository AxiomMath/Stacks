module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.KGroup
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.PerfectToSupportedCoherent
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Coproduct
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularBoundedCoherentPerfect
public import StacksFrontier.AlgebraicGeometry.TopIdeals.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The K-group of perfect complexes supported on a closed subscheme of a regular scheme

Let `X` be a Noetherian regular scheme and `Z ⊂ X` a closed subscheme. Coherent `𝒪_X`-modules
supported on `Z` form a weak Serre subcategory `Coh_Z(X)` of all `𝒪_X`-modules, and by both halves
of [Stacks, Tag 0FDC] the perfect complexes supported on `Z` are exactly the bounded complexes all
of whose cohomology sheaves lie in `Coh_Z(X)`:
`D_{Z, perf}(𝒪_X) = D^b_{Coh_Z(X)}(𝒪_X)`. Consequently the homomorphism
`K_0(Coh_Z(X)) → K_0(D_{Z, perf}(𝒪_X))` placing a module in degree zero is an isomorphism, and its
inverse is the alternating sum of the cohomology sheaves.

## Main definitions

* `AlgebraicGeometry.coherentSupportedProperty` is the property of being a coherent `𝒪_X`-module
  supported on `Z`, as a property of all `𝒪_X`-modules.
* `AlgebraicGeometry.singleSupportedPerfect` places such a module in degree zero.
* `AlgebraicGeometry.supportedCoherentToPerfectHom` is the homomorphism
  `K_0(Coh_Z(X)) → K_0(D_{Z, perf}(𝒪_X))`.
* `AlgebraicGeometry.supportedPerfectEulerHom'` is the alternating sum of cohomology sheaves, a
  homomorphism `K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))`.

## Main results

* `AlgebraicGeometry.derivedCategoryBBounded_coherentSupportedProperty`:
  `D^b_{Coh_Z(X)}(𝒪_X) = D_{Z, perf}(𝒪_X)`.
* `AlgebraicGeometry.bijective_supportedCoherentToPerfectHom`: the degree-zero homomorphism is
  bijective.
* `AlgebraicGeometry.supportedPerfectEulerHom'_comp_supportedCoherentToPerfectHom` and
  `AlgebraicGeometry.supportedCoherentToPerfectHom_comp_supportedPerfectEulerHom'`: the two
  homomorphisms are mutually inverse.

## Implementation notes

`Coh_Z(X)` is spelled here as a property of all `𝒪_X`-modules, the conjunction of coherence and of
containment of the support in the closed subset underlying `Z`, rather than as the property
`AlgebraicGeometry.supportedCoherentProperty` of a coherent module. The two full subcategories have
the same objects, but only the unnested spelling is a weak Serre subcategory of the ambient abelian
category in which the derived category is formed, which is what
`DerivedCategory.exists_addEquiv_K0_of_isWeakSerreClass` asks for.

Each half of the weak Serre property is the conjunction of its coherent half, which is
[Stacks, Tag 01BY], with its support half: the support of a kernel is contained in the support of
the source and the support of a cokernel in the support of the target, because a monomorphism and
an epimorphism of sheaves of modules are injective and surjective on stalks, and the support of the
middle term of an exact sequence is contained in the union of the other two supports.

Surjectivity of the degree-zero homomorphism is not reproved: it is the content of
`DerivedCategory.exists_addEquiv_K0_of_isWeakSerreClass`, whose isomorphism agrees with the
homomorphism here because both send the class of a module to the class of that module placed in
degree zero. That the alternating sum is a left inverse is the computation that a module placed in
degree zero has exactly one nonvanishing cohomology sheaf; the two together give both composites.

The remaining step of [Stacks, Tag 0FER] is the identification `K'_0(Z) = K_0(Coh_Z(X))` of
[Stacks, Tag 0FDT], which is not proved in this library; see
`AlgebraicGeometry.coherentToSupportedCoherentKZeroHom`.

## References

* [Stacks Project, Tag 0FER](https://stacks.math.columbia.edu/tag/0FER)
* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
* [Stacks Project, Tag 0FEQ](https://stacks.math.columbia.edu/tag/0FEQ)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 0FCS](https://stacks.math.columbia.edu/tag/0FCS)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated StrictlyPerfect
open DerivedCategoryB
open scoped ZeroObject

universe u d

namespace AlgebraicGeometry

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Coherent `𝒪_X`-modules whose set-theoretic support lies in the closed subscheme `Z`, as a
property of all `𝒪_X`-modules. -/
def coherentSupportedProperty : ObjectProperty (OXMod.{u, u} X.toRingedSpace) :=
  fun M => SheafOfModules.IsCoherent M ∧ SheafOfModules.supp M ⊆ Set.range i.base

/-- The property of being a coherent `𝒪_X`-module supported on `Z` is closed under
isomorphisms. -/
instance isClosedUnderIsomorphisms_coherentSupportedProperty :
    (coherentSupportedProperty i).IsClosedUnderIsomorphisms where
  of_iso e h :=
    ⟨ObjectProperty.prop_of_iso (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent) e h.1,
      (SheafOfModules.supp_eq_of_iso (X := X) e).symm.subset.trans h.2⟩

/-- Some zero `𝒪_X`-module is coherent and supported on `Z`. -/
instance containsZero_coherentSupportedProperty :
    (coherentSupportedProperty i).ContainsZero where
  exists_zero := by
    obtain ⟨W, hW, hWcoh⟩ := ObjectProperty.exists_prop_of_containsZero
      (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
    exact ⟨W, hW, hWcoh,
      (SheafOfModules.supp_eq_empty_of_isZero hW).subset.trans (Set.empty_subset _)⟩

/-- The kernel of a morphism of coherent `𝒪_X`-modules supported on `Z` is coherent and
supported on `Z`. -/
instance isClosedUnderKernels_coherentSupportedProperty :
    (coherentSupportedProperty i).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨φ, k, hk, hφ⟩
    refine (coherentSupportedProperty i).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel φ) hk) ⟨?_, ?_⟩
    · exact ObjectProperty.prop_kernel (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
        φ hφ.1.1 hφ.2.1
    · have hm : Mono (C := OXMod.{u, u} X.toRingedSpace) (kernel.ι φ) := inferInstance
      exact (Stacks.AlgebraicGeometry.Tag01YHTopIdeals.supp_subset_of_mono (X := X)
        (kernel.ι φ) ⟨fun g h hgh => hm.right_cancellation g h hgh⟩).trans hφ.1.2

/-- The cokernel of a morphism of coherent `𝒪_X`-modules supported on `Z` is coherent and
supported on `Z`. -/
instance isClosedUnderCokernels_coherentSupportedProperty :
    (coherentSupportedProperty i).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hφ⟩
    refine (coherentSupportedProperty i).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel φ) hk) ⟨?_, ?_⟩
    · exact ObjectProperty.prop_cokernel (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
        φ hφ.1.1 hφ.2.1
    · exact (Stacks.AlgebraicGeometry.IrreducibleDevissage.supp_cokernel_subset (X := X)
        φ).trans hφ.2.2

/-- The middle term of a short exact sequence of `𝒪_X`-modules whose outer terms are coherent and
supported on `Z` is coherent and supported on `Z`. -/
instance isClosedUnderExtensions_coherentSupportedProperty :
    (coherentSupportedProperty i).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ :=
    ⟨ObjectProperty.prop_X₂_of_shortExact (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
        hS h₁.1 h₃.1,
      (SheafOfModules.supp_subset_union_of_exact _ hS.exact).trans
        (Set.union_subset h₁.2 h₃.2)⟩

/-- **Coherent modules supported on a closed subscheme form a weak Serre subcategory.** Each
closure property is the conjunction of the corresponding property of coherence,
[Stacks, Tag 01BY], with a containment of supports. -/
instance isWeakSerreClass_coherentSupportedProperty :
    (coherentSupportedProperty i).IsWeakSerreClass where

variable [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]

omit [IsClosedImmersion i] in
/-- **Perfect complexes supported on `Z` are the bounded complexes with cohomology in `Coh_Z(X)`.**
On a Noetherian regular scheme a perfect object of the derived category is bounded with coherent
cohomology and conversely, by the two halves of [Stacks, Tag 0FDC]; the support condition is the
same on both sides. -/
theorem derivedCategoryBBounded_coherentSupportedProperty [IsNoetherian X] (hX : IsRegular X) :
    derivedCategoryBBounded (coherentSupportedProperty i) =
      (show ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) from
        fun K => RingedSpace.IsPerfect K ∧
          ∀ n : ℤ, SheafOfModules.supp
            ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj K) ⊆
              Set.range i.base) := by
  funext K
  refine propext ⟨fun h => ⟨?_, fun n => (h.2 n).2⟩, fun h => ?_⟩
  · exact Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_of_isBoundedCoherent_of_isRegular
      hX K ⟨h.1, fun n => (h.2 n).1⟩
  · obtain ⟨hb, hc⟩ :=
      Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect_of_isRegular
        X hX K h.1
    exact ⟨hb, fun n => ⟨hc n, h.2 n⟩⟩

section

variable [IsNoetherian X] (hX : IsRegular X)

/-- **A coherent module supported on `Z` is a perfect complex supported on `Z` once placed in
degree zero.** Perfectness is the degree-zero case of the forward half of [Stacks, Tag 0FDC]; the
cohomology sheaf in degree zero is the module itself and all others vanish. -/
def singleSupportedPerfect (F : (coherentSupportedProperty i).FullSubcategory) :
    supportedPerfectDerivedCategory i :=
  ⟨(DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F.obj,
    have : SheafOfModules.IsCoherent (R := X.ringCatSheaf) F.obj := F.property.1
    isPerfect_single_of_isCoherent_of_isRegular hX (F.obj : X.Modules), by
    intro n
    obtain rfl | hn := eq_or_ne n 0
    · exact (SheafOfModules.supp_eq_of_iso (X := X)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (OXMod.{u, u} X.toRingedSpace) 0).app F.obj)).subset.trans F.property.2
    · exact (SheafOfModules.supp_eq_empty_of_isZero
        (DerivedCategory.isZero_homology_singleFunctor_obj
          (C := OXMod.{u, u} X.toRingedSpace) F.obj hn)).subset.trans (Set.empty_subset _)⟩

omit [IsNoetherian X] in
/-- The underlying object of `D(𝒪_X)` of a coherent module supported on `Z` placed in degree zero
is that module placed in degree zero. -/
@[simp]
theorem singleSupportedPerfect_obj (F : (coherentSupportedProperty i).FullSubcategory) :
    (singleSupportedPerfect i hX F).obj =
      (DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F.obj :=
  rfl

omit [IsNoetherian X] in
/-- The class of a coherent module supported on `Z`, placed in degree zero, is additive along short
exact sequences: the inclusion of a weak Serre subcategory is exact, so a short exact sequence of
`Coh_Z(X)` is one of `𝒪_X`-modules, which gives a distinguished triangle of the three modules
placed in degree zero. -/
theorem cls_singleSupportedPerfect_add
    (S : ShortComplex (coherentSupportedProperty i).FullSubcategory) (hS : S.ShortExact) :
    Pretriangulated.K0.cls (singleSupportedPerfect i hX S.X₂) =
      Pretriangulated.K0.cls (singleSupportedPerfect i hX S.X₁) +
        Pretriangulated.K0.cls (singleSupportedPerfect i hX S.X₃) := by
  have : PreservesFiniteLimits (ObjectProperty.ι (coherentSupportedProperty i)) :=
    (coherentSupportedProperty i).preservesFiniteLimits_ι_of_isWeakSerreClass
  have : PreservesFiniteColimits (ObjectProperty.ι (coherentSupportedProperty i)) :=
    (coherentSupportedProperty i).preservesFiniteColimits_ι_of_isWeakSerreClass
  exact Pretriangulated.K0.cls_add_of_shortExact (C := OXMod.{u, u} X.toRingedSpace)
    (hS.map_of_exact (ObjectProperty.ι (coherentSupportedProperty i)))
    (singleSupportedPerfect i hX S.X₁) (singleSupportedPerfect i hX S.X₂)
    (singleSupportedPerfect i hX S.X₃) rfl rfl rfl

/-- **The homomorphism `K_0(Coh_Z(X)) → K_0(D_{Z, perf}(𝒪_X))`** sending the class of a coherent
module supported on `Z` to the class of that module placed in degree zero. It is the analogue on
`Coh_Z(X)` of the homomorphism `K_0(Coh(𝒪_Z)) → K_0(D_{Z, perf}(𝒪_X))` of [Stacks, Tag 0FEQ]. -/
def supportedCoherentToPerfectHom :
    KZero (coherentSupportedProperty i).FullSubcategory →+
      Pretriangulated.K0 (supportedPerfectDerivedCategory i) :=
  KZero.lift (fun F => Pretriangulated.K0.cls (singleSupportedPerfect i hX F))
    (cls_singleSupportedPerfect_add i hX)

omit [IsNoetherian X] in
/-- `supportedCoherentToPerfectHom` sends the class of a coherent module supported on `Z` to the
class of that module placed in degree zero. -/
@[simp]
theorem supportedCoherentToPerfectHom_mk (F : (coherentSupportedProperty i).FullSubcategory) :
    supportedCoherentToPerfectHom i hX (KZero.mk _ F) =
      Pretriangulated.K0.cls (singleSupportedPerfect i hX F) :=
  KZero.lift_mk _ _ _

/-- **The homomorphism `K_0(Coh_Z(X)) → K_0(D_{Z, perf}(𝒪_X))` is bijective.** This is
[Stacks, Tag 0FCS] applied to the weak Serre subcategory of coherent modules supported on `Z`,
whose bounded derived category is `D_{Z, perf}(𝒪_X)` by [Stacks, Tag 0FDC]: the isomorphism it
produces also sends the class of a module to the class of that module placed in degree zero, so it
agrees with this homomorphism. -/
theorem bijective_supportedCoherentToPerfectHom :
    Function.Bijective (supportedCoherentToPerfectHom i hX) := by
  obtain ⟨e, -, he⟩ := DerivedCategory.exists_addEquiv_K0_of_isWeakSerreClass
    (coherentSupportedProperty i)
    (((derivedCategoryBBounded_coherentSupportedProperty i hX).symm).trans
      (derivedCategoryBBounded_eq_bounded_inf (coherentSupportedProperty i)))
  have hhom : e.toAddMonoidHom = supportedCoherentToPerfectHom i hX :=
    KZero.hom_ext fun F => by
      rw [supportedCoherentToPerfectHom_mk]
      exact he F (singleSupportedPerfect i hX F) (Iso.refl _)
  rw [← hhom]
  exact e.bijective

/-- Degree-zero cohomology of a perfect complex supported on `Z`, as a coherent module supported on
`Z`: the cohomology sheaves of a perfect complex on a Noetherian regular scheme are coherent by the
converse half of [Stacks, Tag 0FDC], and their supports lie in `Z` by definition of
`D_{Z, perf}(𝒪_X)`. -/
def supportedPerfectHomology' :
    supportedPerfectDerivedCategory i ⥤ (coherentSupportedProperty i).FullSubcategory :=
  ObjectProperty.lift (coherentSupportedProperty i)
    (ObjectProperty.ι _ ⋙ DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0)
    fun E =>
      ⟨(Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect_of_isRegular
        X hX E.obj E.property.1).2 0, E.property.2 0⟩

/-- Degree-zero cohomology `supportedPerfectHomology'` preserves zero morphisms. -/
instance preservesZeroMorphisms_supportedPerfectHomology' :
    (supportedPerfectHomology' i hX).PreservesZeroMorphisms where
  map_zero _ _ := (ObjectProperty.ι (coherentSupportedProperty i)).map_injective
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).map_zero _ _)

/-- Degree-zero cohomology `supportedPerfectHomology'` is a homological functor. -/
instance isHomological_supportedPerfectHomology' :
    (supportedPerfectHomology' i hX).IsHomological where
  exact T hT := by
    refine exact_of_exact_map_ι (coherentSupportedProperty i) ?_
    exact Functor.map_distinguished_exact
      (ObjectProperty.ι _ ⋙ DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0) T hT

/-- A cohomology sheaf that vanishes among all `𝒪_X`-modules is a zero object of `Coh_Z(X)`: the
inclusion is fully faithful, and a fully faithful functor reflects zero objects. -/
theorem isZero_supportedPerfectHomology'_of_isZero (E : supportedPerfectDerivedCategory i) (n : ℤ)
    (hn : IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj E.obj)) :
    IsZero ((supportedPerfectHomology' i hX).obj
      ((shiftFunctor (supportedPerfectDerivedCategory i) n).obj E)) := by
  refine IsZero.of_full_of_faithful_of_isZero
    (ObjectProperty.ι (coherentSupportedProperty i)) _ ?_
  refine IsZero.of_iso hn ?_
  refine (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).mapIso
    ((Functor.commShiftIso (ObjectProperty.ι _) n).app E) ≪≫ ?_
  exact ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).shiftIso n 0 n
    (add_zero n)).app E.obj

/-- Only finitely many cohomology sheaves of a perfect complex on a Noetherian regular scheme are
nonzero, by the converse half of [Stacks, Tag 0FDC]. -/
theorem finite_nonzero_supportedPerfectHomology' (E : supportedPerfectDerivedCategory i) :
    {n : ℤ | ¬ IsZero ((supportedPerfectHomology' i hX).obj
      ((shiftFunctor (supportedPerfectDerivedCategory i) n).obj E))}.Finite := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect_of_isRegular
      X hX E.obj E.property.1
  refine (Set.finite_Icc a b).subset fun n hn => ?_
  simp only [Set.mem_ofPred_eq] at hn
  by_contra hmem
  simp only [Set.mem_Icc, not_and_or, not_le] at hmem
  rcases hmem with h | h
  · exact hn (isZero_supportedPerfectHomology'_of_isZero i hX E n (ha n h))
  · exact hn (isZero_supportedPerfectHomology'_of_isZero i hX E n (hb n h))

/-- The Euler characteristic of a perfect complex supported on `Z` exists as a homomorphism of
`K`-groups into `K_0(Coh_Z(X))`. -/
theorem exists_supportedPerfectEulerHom' :
    ∃ φ : Pretriangulated.K0 (supportedPerfectDerivedCategory i) →+
      KZero (coherentSupportedProperty i).FullSubcategory,
      ∀ E : supportedPerfectDerivedCategory i, φ (Pretriangulated.K0.cls E) =
        eulerClass (supportedPerfectDerivedCategory i)
          (coherentSupportedProperty i).FullSubcategory (supportedPerfectHomology' i hX) E :=
  K0_homomorphism_of_homological (supportedPerfectDerivedCategory i)
    (coherentSupportedProperty i).FullSubcategory (supportedPerfectHomology' i hX)
    (isHomological_supportedPerfectHomology' i hX)
    (finite_nonzero_supportedPerfectHomology' i hX)

/-- **The homomorphism `K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))` of [Stacks, Tag 0FEP]**, in the
unnested spelling of `Coh_Z(X)`: the alternating sum of the classes of the cohomology sheaves of a
perfect complex supported on `Z`. -/
@[stacks 0FEP "the homomorphism K_0(D_{Z, perf}(O_X)) → K_0(Coh_Z(X)), with Coh_Z(X) spelled as a \
weak Serre subcategory of all O_X-modules. As for the nested spelling: the value on a class is \
the alternating sum ∑_n (-1)^n [H^n(E)] rather than the source's \
[⊕_n H^{2n}(E)] - [⊕_n H^{2n+1}(E)], the same element of K_0 but the identification of the two \
expressions is NOT proved; and X is Noetherian regular, the hypotheses of Stacks 0FER, rather \
than locally Noetherian. The identification K_0(Coh_Z(X)) = K'_0(Z) is Stacks 0FDT and is NOT \
covered"]
def supportedPerfectEulerHom' :
    Pretriangulated.K0 (supportedPerfectDerivedCategory i) →+
      KZero (coherentSupportedProperty i).FullSubcategory :=
  Classical.choose (exists_supportedPerfectEulerHom' i hX)

/-- **[Stacks, Tag 0FEP].** The homomorphism `K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))` sends the
class of a perfect complex supported on `Z` to the alternating sum of the classes of its cohomology
sheaves. -/
@[stacks 0FEP "the defining property of the homomorphism, in the alternating-sum form"]
theorem supportedPerfectEulerHom'_cls (E : supportedPerfectDerivedCategory i) :
    supportedPerfectEulerHom' i hX (Pretriangulated.K0.cls E) =
      eulerClass (supportedPerfectDerivedCategory i)
        (coherentSupportedProperty i).FullSubcategory (supportedPerfectHomology' i hX) E :=
  Classical.choose_spec (exists_supportedPerfectEulerHom' i hX) E

/-- The degree-zero cohomology of a coherent module supported on `Z` placed in degree zero is that
module. -/
def supportedPerfectHomology'_obj_single
    (F : (coherentSupportedProperty i).FullSubcategory) :
    (supportedPerfectHomology' i hX).obj ((shiftFunctor (supportedPerfectDerivedCategory i)
        (0 : ℤ)).obj (singleSupportedPerfect i hX F)) ≅ F := by
  refine (ObjectProperty.fullyFaithfulι (coherentSupportedProperty i)).preimageIso ?_
  refine ?_ ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (OXMod.{u, u} X.toRingedSpace) 0).app F.obj
  refine (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).mapIso
    ((Functor.commShiftIso (ObjectProperty.ι _) (0 : ℤ)).app
      (singleSupportedPerfect i hX F)) ≪≫ ?_
  exact ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).shiftIso (0 : ℤ) 0 0
    (add_zero 0)).app (singleSupportedPerfect i hX F).obj

/-- **The first of the two inverse identities of [Stacks, Tag 0FER].** Taking the alternating sum
of the cohomology sheaves of a coherent module supported on `Z`, placed in degree zero, returns the
class of that module: the only nonvanishing cohomology sheaf is the module itself, in degree zero.
-/
@[stacks 0FER "the identity K_0(Coh_Z(X)) → K_0(D_{Z, perf}(O_X)) → K_0(Coh_Z(X)); the \
identification K_0(Coh_Z(X)) = K'_0(Z) of Stacks 0FDT, under which this is the source's statement \
about K_0(Coh(Z)), is NOT covered"]
theorem supportedPerfectEulerHom'_comp_supportedCoherentToPerfectHom :
    (supportedPerfectEulerHom' i hX).comp (supportedCoherentToPerfectHom i hX) =
      AddMonoidHom.id (KZero (coherentSupportedProperty i).FullSubcategory) := by
  refine KZero.hom_ext fun F => ?_
  rw [AddMonoidHom.comp_apply, supportedCoherentToPerfectHom_mk, supportedPerfectEulerHom'_cls,
    AddMonoidHom.id_apply]
  have hvanish : ∀ n : ℤ, n ≠ 0 → ((-1 : ℤ) ^ n.natAbs) •
      KZero.mk (coherentSupportedProperty i).FullSubcategory
        ((supportedPerfectHomology' i hX).obj
          ((shiftFunctor (supportedPerfectDerivedCategory i) n).obj
            (singleSupportedPerfect i hX F))) = 0 := by
    intro n hn
    rw [KZero.mk_eq_zero_of_isZero (isZero_supportedPerfectHomology'_of_isZero i hX
      (singleSupportedPerfect i hX F) n
      (DerivedCategory.isZero_homology_singleFunctor_obj
        (C := OXMod.{u, u} X.toRingedSpace) F.obj hn)), smul_zero]
  rw [eulerClass, finsum_eq_single _ (0 : ℤ) hvanish]
  simpa using KZero.mk_eq_of_iso (supportedPerfectHomology'_obj_single i hX F)

/-- **The second of the two inverse identities of [Stacks, Tag 0FER].** Placing the alternating sum
of the cohomology sheaves of a perfect complex supported on `Z` back in degree zero returns the
class of the complex.

Surjectivity of the degree-zero homomorphism, the step the source proves from the truncation
triangles and the finite filtration of a coherent module supported on `Z`, is taken from
[Stacks, Tag 0FCS]. -/
theorem supportedCoherentToPerfectHom_supportedPerfectEulerHom'
    (x : Pretriangulated.K0 (supportedPerfectDerivedCategory i)) :
    supportedCoherentToPerfectHom i hX (supportedPerfectEulerHom' i hX x) = x := by
  obtain ⟨y, rfl⟩ := (bijective_supportedCoherentToPerfectHom i hX).2 x
  exact congrArg (supportedCoherentToPerfectHom i hX)
    (DFunLike.congr_fun (supportedPerfectEulerHom'_comp_supportedCoherentToPerfectHom i hX) y)

/-- **The two homomorphisms of [Stacks, Tag 0FEP] and [Stacks, Tag 0FEQ] are mutually inverse**, so
`K_0(Coh_Z(X)) = K_0(D_{Z, perf}(𝒪_X))`: the alternating sum of cohomology sheaves and the
placement of a coherent module supported on `Z` in degree zero compose to the identity in this
direction, and `supportedPerfectEulerHom'_comp_supportedCoherentToPerfectHom` is the other
direction. -/
@[stacks 0FER "the identity K_0(D_{Z, perf}(O_X)) → K_0(Coh_Z(X)) → K_0(D_{Z, perf}(O_X)); with \
supportedPerfectEulerHom'_comp_supportedCoherentToPerfectHom this is the source's 'mutually \
inverse', EXCEPT that the source's left hand side is K'_0(Z) = K_0(Coh(Z)) and here it is \
K_0(Coh_Z(X)); the identification of the two is Stacks 0FDT and is NOT covered"]
theorem supportedCoherentToPerfectHom_comp_supportedPerfectEulerHom' :
    (supportedCoherentToPerfectHom i hX).comp (supportedPerfectEulerHom' i hX) =
      AddMonoidHom.id (Pretriangulated.K0 (supportedPerfectDerivedCategory i)) :=
  AddMonoidHom.ext (supportedCoherentToPerfectHom_supportedPerfectEulerHom' i hX)

end

end AlgebraicGeometry

end
