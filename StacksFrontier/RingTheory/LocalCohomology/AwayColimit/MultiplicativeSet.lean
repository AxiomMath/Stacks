module

public import StacksFrontier.RingTheory.LocalCohomology.AwayColimit.Basic
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.CechSectionsComparison
import all StacksFrontier.RingTheory.LocalCohomology.AwayColimit.Basic
import all StacksFrontier.RingTheory.F6Sweep.LocalCohomologySupportSurjectivity

/-!
# Local cohomology on principal supports along a multiplicative set

Let `S` be a multiplicative subset of a commutative ring `A` and let `M` be an `A`-module whose
localization at `S` vanishes. The closed subsets `V(f)` for `f ∈ S` grow as `f` is replaced by a
multiple, so the local cohomology modules `Hⁱ_{V(f)}(M)` form a filtered system over the elements
of `S` ordered by divisibility. This file computes its colimit in the two degrees the source
treats: in degree zero the canonical map to `M` is an isomorphism, and in degree one the colimit
vanishes.

Both are consequences of the four-term low-degree sequence
`0 ⟶ H⁰_{V(f)}(M) ⟶ M ⟶ Γ(D(f), M̃) ⟶ H¹_{V(f)}(M) ⟶ 0`
of `Stacks.LocalCohomology.exact_lowDegreeSequence`. In degree zero: each leg
`H⁰_{V(f)}(M) ⟶ M` is injective, so the map out of the filtered colimit is injective; and an
element of `M` killed by `f` restricts to zero on `D(f) = Spec A ∖ V(f)`, hence lies in the image
of the leg at `f`, which gives surjectivity because the localization of `M` at `S` vanishes. In
degree one: a class in `H¹_{V(f)}(M)` is the image of a section on `D(f)`; that open is
quasi-compact, so the section is a fraction on each of finitely many opens covering it and a
single element `a ∈ S` annihilates all of their numerators, so the section lifts to a submodule
`N ⊆ M` annihilated by `a`. Over `N` the class dies already on the larger support `V(fa)`, because
`fa` annihilates `N` and therefore every section of `Ñ` on `D(fa)` vanishes. So every element of
the system dies at a larger index, and the colimit is zero.

## Main definitions

* `Stacks.LocalCohomology.principalLocalCohomologySystem` — the divisibility-indexed system
  `f ↦ Hⁱ_{V(f)}(M)`, with the maps induced by the inclusions `V(g) ⊆ V(f)` of supports.
* `Stacks.LocalCohomology.principalLocalCohomologyCocone` — the cocone on the degree-zero system
  whose leg at `f` is the canonical map `H⁰_{V(f)}(M) ⟶ M`.
* `Stacks.LocalCohomology.colimitPrincipalLocalCohomologyToModule` — the induced map out of the
  degree-zero colimit.

## Main results

* `Stacks.LocalCohomology.isIso_colimitPrincipalLocalCohomologyToModule` — **Stacks 0DWT, degree
  zero**: `colim_{f ∈ S} H⁰_{V(f)}(M) ⟶ M` is an isomorphism when `S⁻¹M = 0`.
* `Stacks.LocalCohomology.isZero_colimitPrincipalLocalCohomologyOne` — **Stacks 0DWT, degree
  one**: `colim_{f ∈ S} H¹_{V(f)}(M) = 0` when `S⁻¹M = 0`.
* `Stacks.LocalCohomology.localCohomologyComparison_naturality` — the comparison attached to an
  inclusion of support ideals is natural in the module.

## Implementation notes

The index type `Stacks.LocalCohomology.MultiplicativeIndex` and its divisibility preorder are
taken from `StacksFrontier/RingTheory/LocalCohomology/AwayColimit/Basic.lean`, where they index the
system of Stacks 0DWU; the two tags use the same index. As there, the index lives in the universe
of `A`, so the colimit exists in `ModuleCat.{u} A` only for a module universe at least that of the
ring, and the statements are single-universe, with `A : Type u` and `M : ModuleCat.{u} A`.

The transition maps are the cohomology of `Stacks.Algebraization.localCohomologyComparison`, the
adjunct of the counit, which is what the system of Stacks 0DWU uses as well; no separate
functoriality of local cohomology in the support ideal is introduced.

`Stacks.LocalCohomology.fg_idealSpan_singleton` restates `Submodule.fg_span_singleton` with the
ideal written as `Ideal.span`, which is the spelling the local-cohomology API uses. The two are
definitionally equal, but only after unfolding `Ideal.span`, so a statement built with the
`Submodule` spelling is not type-correct at the transparency `rw` works at, which makes every
rewrite inside it fail. Likewise the proofs below compose the comparison with the counit in term
mode rather than by `rw`: the comparison's type names `Dualizing.localCohomologyFunctor` while the
counit's names `Dualizing.localCohomologyRightAdjoint`, and these too agree only after unfolding.

## References

* [Stacks Project, Tag 0DWT](https://stacks.math.columbia.edu/tag/0DWT)
* [Stacks Project, Tag 0DWU](https://stacks.math.columbia.edu/tag/0DWU)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

open SupportSurjectivity AwayColimit

variable {A : Type u} [CommRing A]

/-- A principal ideal is finitely generated, with the ideal written as `Ideal.span`. -/
theorem fg_idealSpan_singleton (x : A) : (Ideal.span {x} : Ideal A).FG :=
  Submodule.fg_span_singleton x

/-! ### Naturality of the comparison for an inclusion of supports -/

/-- Local cohomology with support in `J` is `I`-power-torsion in the derived sense when `I ≤ J`. -/
private theorem derivedPowerTorsionProperty_localCohomologyOnModules_of_le (I J : Ideal A)
    (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J) (M : ModuleCat.{u} A) :
    Dualizing.derivedPowerTorsionProperty A I hI ((localCohomologyOnModules A J hJ).obj M) :=
  fun q x ↦ by
    obtain ⟨n, hn, hx⟩ := derivedPowerTorsionProperty_localCohomologyOnModules J hJ M q x
    exact ⟨n, hn, fun a ha ↦ hx a (pow_le_pow_left' hIJ n ha)⟩

/-- **The comparison for an inclusion `I ≤ J` of support ideals is natural in the module.** Both
composites are morphisms out of an `I`-power-torsion object into `RΓ_{V(I)}(N)`, and they agree
after composing with the counit, which determines them. -/
theorem localCohomologyComparison_naturality (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (hIJ : I ≤ J) {M N : ModuleCat.{u} A} (e : M ⟶ N) :
    (localCohomologyOnModules A J hJ).map e ≫
        Stacks.Algebraization.localCohomologyComparison A J I hJ hI hIJ
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) =
      Stacks.Algebraization.localCohomologyComparison A J I hJ hI hIJ
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫
        (localCohomologyOnModules A I hI).map e := by
  have hW := derivedPowerTorsionProperty_localCohomologyOnModules_of_le I J hI hJ hIJ M
  have hcI : Stacks.Algebraization.localCohomologyComparison A J I hJ hI hIJ
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ≫
      (Dualizing.localCohomologyAdjunction A I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) =
    (Dualizing.localCohomologyAdjunction A J hJ).counit.app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) :=
    localCohomologyMapOfLE_comp_augmentation I J hI hJ hIJ N
  have hcM : Stacks.Algebraization.localCohomologyComparison A J I hJ hI hIJ
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫
      (Dualizing.localCohomologyAdjunction A I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) =
    (Dualizing.localCohomologyAdjunction A J hJ).counit.app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) :=
    localCohomologyMapOfLE_comp_augmentation I J hI hJ hIJ M
  have hnatI : (localCohomologyOnModules A I hI).map e ≫
      (Dualizing.localCohomologyAdjunction A I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) =
    (Dualizing.localCohomologyAdjunction A I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map e :=
    (Dualizing.localCohomologyAdjunction A I hI).counit.naturality
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map e)
  have hnatJ : (localCohomologyOnModules A J hJ).map e ≫
      (Dualizing.localCohomologyAdjunction A J hJ).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) =
    (Dualizing.localCohomologyAdjunction A J hJ).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map e :=
    (Dualizing.localCohomologyAdjunction A J hJ).counit.naturality
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map e)
  have left : ((localCohomologyOnModules A J hJ).map e ≫
        Stacks.Algebraization.localCohomologyComparison A J I hJ hI hIJ
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)) ≫
      (Dualizing.localCohomologyAdjunction A I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) =
    (Dualizing.localCohomologyAdjunction A J hJ).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map e :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t ↦ (localCohomologyOnModules A J hJ).map e ≫ t) hcI).trans hnatJ)
  have right : (Stacks.Algebraization.localCohomologyComparison A J I hJ hI hIJ
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫
        (localCohomologyOnModules A I hI).map e) ≫
      (Dualizing.localCohomologyAdjunction A I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) =
    (Dualizing.localCohomologyAdjunction A J hJ).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map e :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t ↦ Stacks.Algebraization.localCohomologyComparison A J I hJ hI hIJ
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫ t) hnatI).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun t ↦ t ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map e)
            hcM)))
  exact (bijective_comp_localCohomologyCounit I hI
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) _ hW).injective
    (left.trans right.symm)

/-- **The comparison for `I ≤ I` is the identity.** Both are morphisms into `RΓ_{V(I)}(M)` out of
an `I`-power-torsion object agreeing after composition with the counit. -/
theorem localCohomologyComparison_self (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A) :
    Stacks.Algebraization.localCohomologyComparison A I I hI hI le_rfl
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) =
      𝟙 ((localCohomologyOnModules A I hI).obj M) :=
  (bijective_comp_localCohomologyCounit I hI
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) _
      (derivedPowerTorsionProperty_localCohomologyOnModules I hI M)).injective
    ((localCohomologyMapOfLE_comp_augmentation I I hI hI le_rfl M).trans
      (Category.id_comp _).symm)

/-- **The comparisons for `I ≤ K ≤ J` compose.** Each side is a morphism into `RΓ_{V(I)}(M)` out
of a `J`-power-torsion, hence `I`-power-torsion, object, and both become the counit of the
`J`-adjunction after composition with the counit of the `I`-adjunction. -/
theorem localCohomologyComparison_comp (I K J : Ideal A) (hI : I.FG) (hK : K.FG) (hJ : J.FG)
    (hIK : I ≤ K) (hKJ : K ≤ J) (M : ModuleCat.{u} A) :
    Stacks.Algebraization.localCohomologyComparison A J K hJ hK hKJ
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫
      Stacks.Algebraization.localCohomologyComparison A K I hK hI hIK
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) =
    Stacks.Algebraization.localCohomologyComparison A J I hJ hI (hIK.trans hKJ)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) := by
  have hW := derivedPowerTorsionProperty_localCohomologyOnModules_of_le I J hI hJ
    (hIK.trans hKJ) M
  exact (bijective_comp_localCohomologyCounit I hI
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) _ hW).injective
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t ↦ Stacks.Algebraization.localCohomologyComparison A J K hJ hK hKJ
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫ t)
          (localCohomologyMapOfLE_comp_augmentation I K hI hK hIK M)).trans
        ((localCohomologyMapOfLE_comp_augmentation K J hK hJ hKJ M).trans
          (localCohomologyMapOfLE_comp_augmentation I J hI hJ (hIK.trans hKJ) M).symm)))

/-! ### The divisibility-indexed system of principal supports -/

/-- A multiple generates a smaller principal ideal, so divisibility in the index reverses the
inclusion of the support ideals. -/
theorem span_singleton_le_span_singleton_of_le {S : Submonoid A}
    {f g : MultiplicativeIndex S} (hfg : f ≤ g) :
    Ideal.span {g.val} ≤ Ideal.span {f.val} :=
  Ideal.span_singleton_le_span_singleton.mpr hfg

variable (A) in
/-- The filtered system `f ↦ Hⁱ_{V(f)}(M)` indexed by the elements of a multiplicative subset
ordered by divisibility. The transition map for `f ∣ g` is the cohomology of the canonical
comparison for the inclusion `V(g) ⊆ V(f)` of supports. -/
def principalLocalCohomologySystem (S : Submonoid A) (M : ModuleCat.{u} A) (i : ℤ) :
    MultiplicativeIndex S ⥤ ModuleCat.{u} A where
  obj f := localCohomologyModule A (Ideal.span {f.val}) (fg_idealSpan_singleton f.val) M i
  map {f g} hfg := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
    (Stacks.Algebraization.localCohomologyComparison A (Ideal.span {f.val})
      (Ideal.span {g.val}) (fg_idealSpan_singleton f.val) (fg_idealSpan_singleton g.val)
      (span_singleton_le_span_singleton_of_le hfg.le)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))
  map_id f :=
    (congrArg (fun t ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map t)
        (localCohomologyComparison_self (Ideal.span {f.val})
          (fg_idealSpan_singleton f.val) M)).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map_id _)
  map_comp {f g h} hfg hgh :=
    (congrArg (fun t ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map t)
        (localCohomologyComparison_comp (Ideal.span {h.val}) (Ideal.span {g.val})
          (Ideal.span {f.val}) (fg_idealSpan_singleton h.val) (fg_idealSpan_singleton g.val)
          (fg_idealSpan_singleton f.val) (span_singleton_le_span_singleton_of_le hgh.le)
          (span_singleton_le_span_singleton_of_le hfg.le) M).symm).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map_comp _ _)

variable (A) in
/-- The cocone on the degree-zero system whose leg at `f` is the canonical map
`H⁰_{V(f)}(M) ⟶ M`. The legs are compatible because the comparison for an inclusion of supports
followed by the counit is the counit. -/
def principalLocalCohomologyCocone (S : Submonoid A) (M : ModuleCat.{u} A) :
    Cocone (principalLocalCohomologySystem A S M 0) where
  pt := M
  ι :=
    { app f := localCohomologyZeroToModule A (Ideal.span {f.val})
        (fg_idealSpan_singleton f.val) M
      naturality := fun {f g} hfg ↦ by
        have h : Stacks.Algebraization.localCohomologyComparison A (Ideal.span {f.val})
              (Ideal.span {g.val}) (fg_idealSpan_singleton f.val)
              (fg_idealSpan_singleton g.val)
              (span_singleton_le_span_singleton_of_le hfg.le)
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫
            (Dualizing.localCohomologyAdjunction A (Ideal.span {g.val})
              (fg_idealSpan_singleton g.val)).counit.app
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) =
          (Dualizing.localCohomologyAdjunction A (Ideal.span {f.val})
            (fg_idealSpan_singleton f.val)).counit.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) :=
          localCohomologyMapOfLE_comp_augmentation (Ideal.span {g.val}) (Ideal.span {f.val})
            (fg_idealSpan_singleton g.val) (fg_idealSpan_singleton f.val)
            (span_singleton_le_span_singleton_of_le hfg.le) M
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun t ↦ t ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso
                (ModuleCat.{u} A) 0).hom.app M)
              ((((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map_comp _ _).symm).trans
                (congrArg
                  (fun t ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map t) h))).trans
            (Category.comp_id _).symm) }

variable (A) in
/-- The canonical map `colim_{f ∈ S} H⁰_{V(f)}(M) ⟶ M` out of the degree-zero colimit. -/
def colimitPrincipalLocalCohomologyToModule (S : Submonoid A) (M : ModuleCat.{u} A) :
    colimit (principalLocalCohomologySystem A S M 0) ⟶ M :=
  colimit.desc _ (principalLocalCohomologyCocone A S M)

/-- The composite of the colimit inclusion at `f` with the canonical map to `M` is the counit
`H⁰_{V(f)}(M) ⟶ M`. -/
theorem colimit_ι_comp_colimitPrincipalLocalCohomologyToModule (S : Submonoid A)
    (M : ModuleCat.{u} A) (f : MultiplicativeIndex S) :
    colimit.ι (principalLocalCohomologySystem A S M 0) f ≫
        colimitPrincipalLocalCohomologyToModule A S M =
      localCohomologyZeroToModule A (Ideal.span {f.val}) (fg_idealSpan_singleton f.val) M :=
  colimit.ι_desc _ _

/-! ### A filtered colimit with injective and jointly surjective legs -/

/-- If every leg of a cocone on a filtered diagram of modules is injective and the legs are
jointly surjective, the induced map out of the colimit is an isomorphism. -/
theorem isIso_colimit_desc_of_injective_of_jointly_surjective {J : Type u} [SmallCategory J]
    [IsFiltered J] [Nonempty J] (D : J ⥤ ModuleCat.{u} A) (c : Cocone D)
    (hinj : ∀ j, Function.Injective (c.ι.app j).hom)
    (hsurj : ∀ y : c.pt, ∃ j, ∃ x : D.obj j, (c.ι.app j).hom x = y) :
    IsIso (colimit.desc D c) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, fun y ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨j, x, hx⟩ := isColimit_exists_rep_moduleCat D (colimit.cocone D)
      (colimit.isColimit D) z
    have hfac : (colimit.desc D c).hom ((colimit.ι D j).hom x) = (c.ι.app j).hom x :=
      ConcreteCategory.congr_hom (colimit.ι_desc c j) x
    have hxz : (colimit.ι D j).hom x = z := hx
    have hx0 : (c.ι.app j).hom x = 0 := by rwa [← hfac, hxz]
    have hxeq : x = 0 := hinj j (by rw [hx0, map_zero])
    rw [← hxz, hxeq, map_zero]
  · obtain ⟨j, x, hx⟩ := hsurj y
    exact ⟨(colimit.ι D j).hom x,
      (ConcreteCategory.congr_hom (colimit.ι_desc c j) x).trans hx⟩

/-! ### Degree zero -/

/-- An element of a module whose localization at `S` vanishes is killed by an element of `S`. -/
private theorem exists_smul_eq_zero_of_subsingleton_localizedModule (S : Submonoid A)
    (M : ModuleCat.{u} A) [Subsingleton (LocalizedModule S M)] (m : M) :
    ∃ a : S, (a : A) • m = 0 := by
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_zero_iff S (LocalizedModule.mkLinearMap S M)).mp
    (Subsingleton.elim (LocalizedModule.mkLinearMap S M m) 0)
  exact ⟨a, ha⟩

/-- A prime in the image of the open complement of `V(f)` does not contain `f`. -/
theorem notMem_asIdeal_of_mem_complementZeroLocus_image_top {f : A} {p : PrimeSpectrum A}
    (hp : p ∈ (complementZeroLocus A (Ideal.span {f})).ι ''ᵁ ⊤) : f ∉ p.asIdeal := by
  rw [AlgebraicGeometry.Scheme.Opens.ι_image_top] at hp
  have hnot : p ∉ PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal A) : Set A) :=
    (Set.mem_compl_iff _ _).mp hp
  intro hf
  exact hnot ((PrimeSpectrum.mem_zeroLocus p _).2
    (SetLike.coe_subset_coe.mpr (Ideal.span_le.2 (Set.singleton_subset_iff.2 hf))))

/-- An element of `M` annihilated by a power of `f` restricts to zero on `Spec A ∖ V(f)`, hence
comes from degree-zero local cohomology with support in `V(f)`. -/
theorem exists_localCohomologyZeroToModule_eq_of_pow_smul_eq_zero (f : A)
    (M : ModuleCat.{u} A) (m : M) (n : ℕ) (hkill : f ^ n • m = 0) :
    ∃ x : localCohomologyModule A (Ideal.span {f}) (fg_idealSpan_singleton f) M 0,
      (localCohomologyZeroToModule A (Ideal.span {f})
        (fg_idealSpan_singleton f) M).hom x = m := by
  classical
  have hres : restrictionToComplement
      (localizationTriangleData.{u, u} A (Ideal.span {f}) (fg_idealSpan_singleton f)) M
      (complementTilde A (Ideal.span {f}) M) (Iso.refl _) m = 0 := by
    rw [restrictionToComplement_apply]
    simp only [Iso.refl_inv]
    apply Subtype.ext
    funext x
    show LocalizedModule.mk m (1 : x.1.asIdeal.primeCompl) = 0
    rw [← LocalizedModule.zero_mk (M := M) (1 : x.1.asIdeal.primeCompl)]
    refine LocalizedModule.mk_eq.mpr ⟨⟨f ^ n, ?_⟩, ?_⟩
    · exact fun hpow ↦ notMem_asIdeal_of_mem_complementZeroLocus_image_top x.2
        ((PrimeSpectrum.isPrime x.1).mem_of_pow_mem n hpow)
    · simp [Submonoid.smul_def, hkill]
  exact (exact_localCohomologyZeroToModule_restrictionToComplement
    (localizationTriangleData.{u, u} A (Ideal.span {f}) (fg_idealSpan_singleton f)) M
    (complementTilde A (Ideal.span {f}) M) (Iso.refl _) m).mp hres

variable (A) in
/-- **Stacks 0DWT, degree zero.** Let `S` be a multiplicative subset of a commutative ring `A`
and let `M` be an `A`-module whose localization at `S` vanishes. Then the canonical map
`colim_{f ∈ S} H⁰_{V(f)}(M) ⟶ M` is an isomorphism.

The legs `H⁰_{V(f)}(M) ⟶ M` are injective, which gives injectivity on the filtered colimit; and
every `m ∈ M` is annihilated by some `f ∈ S`, hence restricts to zero on `Spec A ∖ V(f)` and so
lies in the image of the leg at `f`. -/
@[stacks 0DWT "degree zero"]
theorem isIso_colimitPrincipalLocalCohomologyToModule (S : Submonoid A) (M : ModuleCat.{u} A)
    [Subsingleton (LocalizedModule S M)] :
    IsIso (colimitPrincipalLocalCohomologyToModule A S M) := by
  refine isIso_colimit_desc_of_injective_of_jointly_surjective _ _
    (fun f ↦ localCohomologyZeroToModule_injective A _ (fg_idealSpan_singleton f.val) M)
    fun y ↦ ?_
  obtain ⟨a, ha⟩ := exists_smul_eq_zero_of_subsingleton_localizedModule S M y
  obtain ⟨x, hx⟩ := exists_localCohomologyZeroToModule_eq_of_pow_smul_eq_zero
    (a : A) M y 1 (by rwa [pow_one])
  exact ⟨⟨a, a.property⟩, x, hx⟩

/-! ### Degree one -/

/-- Finitely many elements of a module whose localization at `S` vanishes are annihilated by a
single element of `S`. -/
theorem exists_mem_forall_smul_eq_zero (S : Submonoid A) (M : ModuleCat.{u} A)
    [Subsingleton (LocalizedModule S M)] {ι : Type*} (m : ι → M) (B : Finset ι) :
    ∃ a : S, ∀ i ∈ B, (a : A) • m i = 0 := by
  classical
  induction B using Finset.induction with
  | empty => exact ⟨1, by simp⟩
  | @insert i B _ ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨a, ha'⟩ := exists_smul_eq_zero_of_subsingleton_localizedModule S M (m i)
    refine ⟨a * b, fun j hj ↦ ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [Submonoid.coe_mul, mul_comm, mul_smul, ha', smul_zero]
    · rw [Submonoid.coe_mul, mul_smul, hb j hj, smul_zero]

/-- A locally fractional section on a quasi-compact open comes from a submodule annihilated by a
single element of `S`: the open is covered by finitely many of the opens on which the section is a
fraction, and one element of `S` kills all of the finitely many numerators. -/
theorem exists_annihilated_submodule_moduleSections (S : Submonoid A) (M : ModuleCat.{u} A)
    [Subsingleton (LocalizedModule S M)]
    (U : Opens (PrimeSpectrum.Top A)) (hU : IsCompact (U : Set (PrimeSpectrum.Top A)))
    (s : moduleSections M U) :
    ∃ (a : S) (N : Submodule A M), (∀ n : N, (a : A) • (n : M) = 0) ∧
      ∃ t : moduleSections (ModuleCat.of A N) U,
        (associatedAbPresheafMap (ModuleCat.ofHom N.subtype)).app (op U) t = s := by
  classical
  choose V hxV inc m d hd using s.property
  obtain ⟨B, hB⟩ := hU.elim_finite_subcover (fun x : U ↦ (V x : Set _))
    (fun x ↦ (V x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  obtain ⟨a, ha⟩ := exists_mem_forall_smul_eq_zero S M m B
  have hm (i : U) (hi : i ∈ B) :
      m i ∈ LinearMap.ker ((a : A) • (LinearMap.id : M →ₗ[A] M)) := ha i hi
  have hcover (x : U) : ∃ i ∈ B, x.1 ∈ V i := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hB x.2)
    obtain ⟨hiB, hxi⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hiB, hxi⟩
  have hlift (x : U) : ∃ z : LocalizedModule x.1.asIdeal.primeCompl
      (LinearMap.ker ((a : A) • (LinearMap.id : M →ₗ[A] M))),
      IsLocalizedModule.map x.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl _)
        (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
        (LinearMap.ker ((a : A) • (LinearMap.id : M →ₗ[A] M))).subtype z = s.1 x := by
    obtain ⟨i, hi, hxi⟩ := hcover x
    obtain ⟨hdi, heq⟩ := hd i ⟨x.1, hxi⟩
    refine ⟨LocalizedModule.mk ⟨m i, hm i hi⟩ ⟨d i, hdi⟩, ?_⟩
    rw [IsLocalizedModule.map_LocalizedModules]
    exact heq.symm
  choose t ht using hlift
  refine ⟨a, LinearMap.ker ((a : A) • (LinearMap.id : M →ₗ[A] M)), fun n ↦ n.property,
    ⟨⟨t, ?_⟩, ?_⟩⟩
  · intro x
    obtain ⟨i, hi, hxi⟩ := hcover x
    refine ⟨V i, hxi, inc i, ⟨m i, hm i hi⟩, d i, fun y ↦ ?_⟩
    obtain ⟨hdi, heq⟩ := hd i y
    refine ⟨hdi, ?_⟩
    apply IsLocalizedModule.map_injective y.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl _)
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
      (LinearMap.ker ((a : A) • (LinearMap.id : M →ₗ[A] M))).subtype
      (Submodule.injective_subtype _)
    rw [IsLocalizedModule.map_LocalizedModules]
    exact (ht (inc i y)).trans heq
  · exact Subtype.ext (funext ht)

/-- Degree-one local cohomology with support in `V(f)` of a module annihilated by `f` vanishes:
every class comes from a section on `Spec A ∖ V(f)`, and there `f` acts invertibly while
annihilating the module, so every section is zero. -/
theorem isZero_localCohomologyModule_one_of_smul_eq_zero (f : A) (M : ModuleCat.{u} A)
    (hM : ∀ m : M, f • m = 0) :
    IsZero (localCohomologyModule A (Ideal.span {f}) (fg_idealSpan_singleton f) M 1) := by
  classical
  rw [ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun z ↦ ?_
  obtain ⟨s, rfl⟩ := localizationBoundary_surjective
    (localizationTriangleData.{u, u} A (Ideal.span {f}) (fg_idealSpan_singleton f)) M
    (complementTilde A (Ideal.span {f}) M) (Iso.refl _) z
  have hs : s = 0 := by
    apply Subtype.ext
    funext p
    have hp : f ∈ p.1.asIdeal.primeCompl :=
      notMem_asIdeal_of_mem_complementZeroLocus_image_top p.2
    apply LocalizedModule.eq_zero_of_smul_eq_zero f hp
    induction s.1 p using LocalizedModule.induction_on with
    | h m e => rw [LocalizedModule.smul'_mk, hM m, LocalizedModule.zero_mk]
  rw [hs, map_zero]

/-- Every class in `H¹_{V(f)}(M)` dies on a larger principal support `V(fa)` with `a ∈ S`: it is
the image of a section on the quasi-compact open `D(f)`, that section lifts to a submodule
annihilated by some `a ∈ S`, and the degree-one local cohomology of that submodule on `V(fa)`
vanishes because `fa` annihilates it. -/
theorem exists_principalLocalCohomologySystem_map_eq_zero (S : Submonoid A)
    (M : ModuleCat.{u} A) [Subsingleton (LocalizedModule S M)] (f : MultiplicativeIndex S)
    (x : (principalLocalCohomologySystem A S M 1).obj f) :
    ∃ (g : MultiplicativeIndex S) (hfg : f ≤ g),
      (principalLocalCohomologySystem A S M 1).map (homOfLE hfg) x = 0 := by
  classical
  obtain ⟨s, hs⟩ := localizationBoundary_surjective
    (localizationTriangleData.{u, u} A (Ideal.span {f.val})
      (fg_idealSpan_singleton f.val)) M
    (complementTilde A (Ideal.span {f.val}) M) (Iso.refl _) x
  obtain ⟨a, N, ha, t, ht⟩ := exists_annihilated_submodule_moduleSections S M
    ((complementZeroLocus A (Ideal.span {f.val})).ι ''ᵁ ⊤)
    (by
      rw [AlgebraicGeometry.Scheme.Opens.ι_image_top]
      exact (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr
        ⟨Ideal.span {f.val}, fg_idealSpan_singleton f.val, rfl⟩).1) s
  refine ⟨⟨f.val * (a : A), S.mul_mem f.property a.property⟩, ⟨a, rfl⟩, ?_⟩
  have hN : ∀ n : ModuleCat.of A N, (f.val * (a : A)) • n = 0 := by
    intro n
    apply Subtype.ext
    show (f.val * (a : A)) • (n : M) = 0
    rw [mul_smul, ha n, smul_zero]
  have hyx : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
      ((localCohomologyOnModules A (Ideal.span {f.val})
        (fg_idealSpan_singleton f.val)).map (ModuleCat.ofHom N.subtype))
      (localizationBoundary
        (localizationTriangleData.{u, u} A (Ideal.span {f.val})
          (fg_idealSpan_singleton f.val)) (ModuleCat.of A N)
        (complementTilde A (Ideal.span {f.val}) (ModuleCat.of A N)) (Iso.refl _) t) = x := by
    rw [← localizationBoundary_naturality
      (localizationTriangleData.{u, u} A (Ideal.span {f.val})
        (fg_idealSpan_singleton f.val)) (ModuleCat.ofHom N.subtype) t, ht]
    exact hs
  have hz : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map
      (Stacks.Algebraization.localCohomologyComparison A (Ideal.span {f.val})
        (Ideal.span {(f.val * (a : A))}) (fg_idealSpan_singleton f.val)
        (fg_idealSpan_singleton (f.val * (a : A)))
        (Ideal.span_singleton_le_span_singleton.mpr ⟨(a : A), rfl⟩)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A N)))
      (localizationBoundary
        (localizationTriangleData.{u, u} A (Ideal.span {f.val})
          (fg_idealSpan_singleton f.val)) (ModuleCat.of A N)
        (complementTilde A (Ideal.span {f.val}) (ModuleCat.of A N)) (Iso.refl _) t) = 0 :=
    (ModuleCat.isZero_iff_subsingleton.mp
      (isZero_localCohomologyModule_one_of_smul_eq_zero (f.val * (a : A))
        (ModuleCat.of A N) hN)).elim _ _
  have hnat := congrArg
    (fun k ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map k
      (localizationBoundary
        (localizationTriangleData.{u, u} A (Ideal.span {f.val})
          (fg_idealSpan_singleton f.val)) (ModuleCat.of A N)
        (complementTilde A (Ideal.span {f.val}) (ModuleCat.of A N)) (Iso.refl _) t))
    (localCohomologyComparison_naturality (Ideal.span {(f.val * (a : A))})
      (Ideal.span {f.val}) (fg_idealSpan_singleton (f.val * (a : A)))
      (fg_idealSpan_singleton f.val)
      (Ideal.span_singleton_le_span_singleton.mpr ⟨(a : A), rfl⟩)
      (ModuleCat.ofHom N.subtype))
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hnat
  rwa [hyx, hz, map_zero] at hnat

variable (A) in
/-- **Stacks 0DWT, degree one.** Let `S` be a multiplicative subset of a commutative ring `A` and
let `M` be an `A`-module whose localization at `S` vanishes. Then
`colim_{f ∈ S} H¹_{V(f)}(M) = 0`.

Every class in the system dies at a larger index, so every leg into the colimit is zero and the
identity of the colimit is zero. -/
@[stacks 0DWT "degree one"]
theorem isZero_colimitPrincipalLocalCohomologyOne (S : Submonoid A) (M : ModuleCat.{u} A)
    [Subsingleton (LocalizedModule S M)] :
    IsZero (colimit (principalLocalCohomologySystem A S M 1)) := by
  refine (IsZero.iff_id_eq_zero (colimit (principalLocalCohomologySystem A S M 1))).2
    (colimit.hom_ext fun f ↦ ?_)
  ext x
  obtain ⟨g, hfg, hx⟩ := exists_principalLocalCohomologySystem_map_eq_zero S M f x
  have h := ConcreteCategory.congr_hom
    (colimit.w (principalLocalCohomologySystem A S M 1) (homOfLE hfg)) x
  simp only [ConcreteCategory.comp_apply, hx, map_zero] at h
  simpa using h.symm

end Stacks.LocalCohomology

end
