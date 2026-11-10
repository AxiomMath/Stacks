module

public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.AwayColimit.Basic
import all StacksFrontier.RingTheory.LocalCohomology.AwayColimit.Basic
import all StacksFrontier.RingTheory.LocalCohomology.SupportInjectivity.Basic
import all StacksFrontier.RingTheory.F6Sweep.LocalCohomologySupportSurjectivity
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Local cohomology over a multiplicative set

Let `S` be a multiplicative subset of a commutative ring `A`. If an `A`-module `M` becomes zero
after localization at `S`, the direct limit over `f ∈ S`, ordered by divisibility, of the local
cohomology of `M` supported on the principal closed subset `V(f)` is `M` in degree zero and is
zero in degree one. This is Stacks 0DWT.

The two conclusions come from the two halves of the support-change machinery of Stacks 0DWV,
both of which are available with the ring universe and the module universe independent. Degree
zero is injectivity of `H⁰_{V(f)}(M) ⟶ M` together with the lifting step
`Stacks.LocalCohomology.SupportSurjectivity.exists_lift_of_smul_eq_zero`: an element of `M` killed
by `s ∈ S` comes from `H⁰_{V(s)}(M)`. Degree one is the enlargement step
`Stacks.LocalCohomology.SupportInjectivity.localCohomology_kernel_eventually_zero`: a class on
`V(f)` which dies on all of `Spec A` dies already on `V(f s)` for some `s ∈ S`, so every element
of the colimit is zero.

Both steps are applied with the ambient support ideal equal to `⊥`, where local cohomology is the
identity functor: every object of `D(A)` is `⊥`-power torsion, so the augmentation
`RΓ_{V(⊥)}(M) ⟶ M` is an isomorphism, `H⁰_{V(⊥)}(M) = M` and `H¹_{V(⊥)}(M) = 0`.

## Main definitions

* `Stacks.LocalCohomology.principalDerivedLocalCohomology` — `RΓ_{V(f)}(M)` for a single ring
  element `f`.
* `Stacks.LocalCohomology.principalLocalCohomologyCounit` — its augmentation to `M`.
* `Stacks.LocalCohomology.derivedLocalCohomologyMultiplicativeSystem` — the divisibility-indexed
  derived direct system `f ↦ RΓ_{V(f)}(M)` with its augmentation to the constant system at `M`.
* `Stacks.LocalCohomology.localCohomologyMultiplicativeSystem` and
  `Stacks.LocalCohomology.liftedLocalCohomologyMultiplicativeSystem` — its degreewise cohomology,
  and that system placed in a module category large enough for its colimit.
* `Stacks.LocalCohomology.colimitLocalCohomologyDegreeZeroToModule` — the canonical comparison
  from the degree-zero colimit to the universe lift of `M`.

## Main results

* `Stacks.LocalCohomology.isIso_colimitLocalCohomology_degreeZero_toModule` — **Stacks 0DWT in
  degree zero**: the comparison is an isomorphism.
* `Stacks.LocalCohomology.isZero_colimitLocalCohomology_degreeOne` — **Stacks 0DWT in degree
  one**: the degree-one colimit vanishes.

## Implementation notes

The index type `Stacks.LocalCohomology.MultiplicativeIndex S` lives in the universe of the ring,
so the colimit of the system is formed after lifting the cohomology modules to
`ModuleCat.{max u v} A`; the module universe of `M` itself is unrestricted.

No `@[stacks 0DWT]` attribute is placed here.

## References

* [Stacks Project, Tag 0DWT](https://stacks.math.columbia.edu/tag/0DWT)
* [Stacks Project, Tag 0DWV](https://stacks.math.columbia.edu/tag/0DWV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

open SupportSurjectivity SupportInjectivity

/-! ### Local cohomology with support in `V(⊥)` -/

/-- Every object of `D(A)` is `⊥`-power torsion: the first power of `⊥` is `⊥` itself, and `0`
annihilates everything. -/
private theorem derivedPowerTorsionProperty_bot (A : Type u) [CommRing A]
    (X : DerivedCategory (ModuleCat.{v} A)) :
    Dualizing.derivedPowerTorsionProperty A ⊥ Submodule.fg_bot X := by
  intro i x
  refine ⟨1, one_pos, fun a ha => ?_⟩
  rw [pow_one] at ha
  rw [(Submodule.mem_bot A).mp ha, zero_smul]

/-- If `M` placed in degree zero already has `I`-power-torsion cohomology, the augmentation
`RΓ_{V(I)}(M) ⟶ M` is an isomorphism: the unit of the coreflection is invertible there because
the inclusion of the subcategory is fully faithful, and the augmentation is its inverse. -/
private theorem isIso_localCohomologyAugmentation
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (M : ModuleCat.{v} A)
    (hK : Dualizing.derivedPowerTorsionProperty A I hI
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)) :
    IsIso (localCohomologyAugmentation A I hI M) := by
  let P := Dualizing.derivedPowerTorsionProperty A I hI
  let adj := Dualizing.localCohomologyAdjunction A I hI
  let X : P.FullSubcategory := ⟨(DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M, hK⟩
  have htri : P.ι.map (adj.unit.app X) ≫ localCohomologyAugmentation A I hI M = 𝟙 (P.ι.obj X) :=
    adj.left_triangle_components X
  have hcomp : IsIso (P.ι.map (adj.unit.app X) ≫ localCohomologyAugmentation A I hI M) := by
    rw [htri]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_left (P.ι.map (adj.unit.app X))
    (localCohomologyAugmentation A I hI M)

/-- `H⁰_{V(⊥)}(M) ⟶ M` is an isomorphism. -/
private theorem isIso_localCohomologyZeroToModule_bot
    (A : Type u) [CommRing A] (M : ModuleCat.{v} A) :
    IsIso (localCohomologyZeroToModule A ⊥ Submodule.fg_bot M) := by
  have h := isIso_localCohomologyAugmentation A ⊥ Submodule.fg_bot M
    (derivedPowerTorsionProperty_bot A _)
  have h0 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map
      (localCohomologyAugmentation A ⊥ Submodule.fg_bot M)) := by
    infer_instance
  change IsIso (_ ≫ _)
  infer_instance

/-- `H⁰_{V(⊥)}(M) ⟶ M` is injective. -/
private theorem localCohomologyZeroToModule_bot_injective
    (A : Type u) [CommRing A] (M : ModuleCat.{v} A) :
    Function.Injective (localCohomologyZeroToModule A ⊥ Submodule.fg_bot M).hom := by
  have := isIso_localCohomologyZeroToModule_bot A M
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- `H¹_{V(⊥)}(M) = 0`: local cohomology with support in `V(⊥) = Spec A` is the identity, and a
module placed in degree zero has no cohomology in degree one. -/
private theorem isZero_localCohomologyModule_bot_one
    (A : Type u) [CommRing A] (M : ModuleCat.{v} A) :
    IsZero (localCohomologyModule A ⊥ Submodule.fg_bot M 1) := by
  have h := isIso_localCohomologyAugmentation A ⊥ Submodule.fg_bot M
    (derivedPowerTorsionProperty_bot A _)
  exact (isZero_homologyFunctor_one_singleFunctor_obj M).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 1).mapIso
      (asIso (localCohomologyAugmentation A ⊥ Submodule.fg_bot M)))

/-- A module all of whose elements are annihilated by some element of `S` vanishes after
localization at `S`. -/
private theorem subsingleton_localizedModule_of_forall_smul_eq_zero
    {A : Type u} [CommRing A] (S : Submonoid A) (N : Type v) [AddCommGroup N] [Module A N]
    (h : ∀ n : N, ∃ s : S, (s : A) • n = 0) : Subsingleton (LocalizedModule S N) := by
  suffices hz : ∀ z : LocalizedModule S N, z = 0 from ⟨fun x y => by rw [hz x, hz y]⟩
  intro z
  induction z using LocalizedModule.induction_on with
  | h n t =>
    obtain ⟨s, hs⟩ := h n
    rw [← LocalizedModule.zero_mk (M := N) t]
    refine LocalizedModule.mk_eq.mpr ⟨s, ?_⟩
    simp only [smul_zero]
    rw [Submonoid.smul_def, Submonoid.smul_def, smul_comm, hs, smul_zero]

/-! ### Composing and transporting the comparison of supports -/

/-- The comparison `RΓ_{V(J₀)}(M) ⟶ RΓ_{V(J')}(M)` is the unique morphism over the counit of the
`J'`-adjunction: composing it with that counit gives the counit of the `J₀`-adjunction. -/
theorem localCohomologyComparison_comp_counit
    (A : Type u) [CommRing A] (J₀ J' : Ideal A) (hJ₀ : J₀.FG) (hJ' : J'.FG) (h : J' ≤ J₀)
    (M : ModuleCat.{v} A) :
    Stacks.Algebraization.localCohomologyComparison A J₀ J' hJ₀ hJ' h
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) ≫
        (Dualizing.localCohomologyAdjunction A J' hJ').counit.app
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) =
      (Dualizing.localCohomologyAdjunction A J₀ hJ₀).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) :=
  localCohomologyMapOfLE_comp_augmentation J' J₀ hJ' hJ₀ h M

/-- The comparison of a support with itself is the identity. -/
theorem localCohomologyComparison_self_eq_id
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (M : ModuleCat.{v} A) :
    Stacks.Algebraization.localCohomologyComparison A I I hI hI le_rfl
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) = 𝟙 _ := by
  apply (localCohomology_counit_bijective A I hI
    ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)
    (localCohomologyObject A I hI M)
    (restrictLocalCohomologySupport A I I hI hI le_rfl M).property).injective
  change mapOfLE A I I hI hI le_rfl M ≫ localCohomologyAugmentation A I hI M =
    𝟙 _ ≫ localCohomologyAugmentation A I hI M
  rw [Category.id_comp, localCohomologyMapOfLE_comp_augmentation I I hI hI le_rfl M]

/-- The comparisons of supports compose, as morphisms of `D(A)`.

`Stacks.LocalCohomology.localCohomologyComparison_comp` is the same composition law for a
module in the same universe as the ring; this statement asks no such equality of universes, so
it carries the primed name. -/
theorem localCohomologyComparison_comp'
    (A : Type u) [CommRing A] (J₀ J₁ J₂ : Ideal A) (h₀ : J₀.FG) (h₁ : J₁.FG) (h₂ : J₂.FG)
    (h₁₀ : J₁ ≤ J₀) (h₂₁ : J₂ ≤ J₁) (M : ModuleCat.{v} A) :
    Stacks.Algebraization.localCohomologyComparison A J₀ J₁ h₀ h₁ h₁₀
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) ≫
        Stacks.Algebraization.localCohomologyComparison A J₁ J₂ h₁ h₂ h₂₁
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) =
      Stacks.Algebraization.localCohomologyComparison A J₀ J₂ h₀ h₂ (h₂₁.trans h₁₀)
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) := by
  apply (localCohomology_counit_bijective A J₂ h₂
    ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)
    (localCohomologyObject A J₀ h₀ M)
    (restrictLocalCohomologySupport A J₂ J₀ h₂ h₀ (h₂₁.trans h₁₀) M).property).injective
  change (mapOfLE A J₁ J₀ h₁ h₀ h₁₀ M ≫ mapOfLE A J₂ J₁ h₂ h₁ h₂₁ M) ≫
      localCohomologyAugmentation A J₂ h₂ M =
    mapOfLE A J₂ J₀ h₂ h₀ (h₂₁.trans h₁₀) M ≫ localCohomologyAugmentation A J₂ h₂ M
  rw [Category.assoc, localCohomologyMapOfLE_comp_augmentation J₂ J₁ h₂ h₁ h₂₁ M,
    localCohomologyMapOfLE_comp_augmentation J₁ J₀ h₁ h₀ h₁₀ M,
    localCohomologyMapOfLE_comp_augmentation J₂ J₀ h₂ h₀ (h₂₁.trans h₁₀) M]

/-- The comparison of supports is compatible with the degree-zero maps to `M`. -/
private theorem localCohomologyModuleMapOfLE_comp_zeroToModule
    (A : Type u) [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J)
    (M : ModuleCat.{v} A) :
    localCohomologyModuleMapOfLE A I J hI hJ hIJ M 0 ≫ localCohomologyZeroToModule A I hI M =
      localCohomologyZeroToModule A J hJ M := by
  change (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map (mapOfLE A I J hI hJ hIJ M) ≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map
        (localCohomologyAugmentation A I hI M) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).hom.app M) = _
  rw [← Category.assoc, ← Functor.map_comp,
    localCohomologyMapOfLE_comp_augmentation I J hI hJ hIJ M]
  rfl

/-- `Stacks.LocalCohomology.SupportSurjectivity.exists_lift_of_smul_eq_zero` with the enlarged
support presented by an arbitrary ideal equal to `I + (f)`. -/
private theorem exists_lift_of_smul_eq_zero_of_eq
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (M : ModuleCat.{v} A) (i : ℤ) (f : A)
    (J : Ideal A) (hJ : J.FG) (hJeq : I ⊔ Ideal.span {f} = J) (hIJ : I ≤ J)
    (y : localCohomologyModule A I hI M i) (hy : f • y = 0) :
    ∃ z : localCohomologyModule A J hJ M i,
      (localCohomologyModuleMapOfLE A I J hI hJ hIJ M i).hom z = y := by
  subst hJeq
  exact exists_lift_of_smul_eq_zero A I hI M i f y hy

/-- `Stacks.LocalCohomology.SupportInjectivity.localCohomology_kernel_eventually_zero` with the
enlarged supports presented by arbitrary ideals equal to `I + (f)` and `I + (f s)`. -/
private theorem kernel_eventually_zero_of_eq
    (A : Type u) [CommRing A] (I : Ideal A) (S : Submonoid A) (hI : I.FG)
    (M : ModuleCat.{v} A) (i : ℤ)
    (hvan : Subsingleton (LocalizedModule S (localCohomologyModule A I hI M (i - 1))))
    (f : A) (J : Ideal A) (hJ : J.FG) (hJeq : I ⊔ Ideal.span {f} = J) (hIJ : I ≤ J)
    (x : localCohomologyModule A J hJ M i)
    (hx : (localCohomologyModuleMapOfLE A I J hI hJ hIJ M i).hom x = 0) :
    ∃ s : S, ∀ (J' : Ideal A) (hJ' : J'.FG), I ⊔ Ideal.span {f * (s : A)} = J' →
      ∀ hJ'J : J' ≤ J, (localCohomologyModuleMapOfLE A J' J hJ' hJ hJ'J M i).hom x = 0 := by
  subst hJeq
  obtain ⟨s, hs⟩ := localCohomology_kernel_eventually_zero A I S hI M i hvan f x hx
  refine ⟨s, fun J' hJ' hJ'eq hJ'J => ?_⟩
  subst hJ'eq
  exact hs

/-! ### The two steps of Stacks 0DWT at the support `V(⊥)` -/

/-- An element of `M` annihilated by `f` comes from `H⁰_{V(f)}(M)`. The class lifts along the
comparison from the full support `V(⊥)`, where local cohomology is the identity. -/
private theorem exists_localCohomologyZeroToModule_eq_of_smul_eq_zero
    (A : Type u) [CommRing A] (M : ModuleCat.{v} A) (f : A) (m : M) (hm : f • m = 0) :
    ∃ z : localCohomologyModule A (Ideal.span {f})
        (Submodule.fg_span (Set.finite_singleton f)) M 0,
      (localCohomologyZeroToModule A (Ideal.span {f})
        (Submodule.fg_span (Set.finite_singleton f)) M).hom z = m := by
  have hiso := isIso_localCohomologyZeroToModule_bot A M
  let ε := localCohomologyZeroToModule A ⊥ Submodule.fg_bot M
  let y := (inv ε).hom m
  have hεy : ε.hom y = m := congrArg (fun k => ModuleCat.Hom.hom k m) (IsIso.inv_hom_id ε)
  have hy : f • y = 0 := by
    apply localCohomologyZeroToModule_bot_injective A M
    rw [map_smul, hεy, hm, map_zero]
  obtain ⟨z, hz⟩ := exists_lift_of_smul_eq_zero_of_eq A ⊥ Submodule.fg_bot M 0 f
    (Ideal.span {f}) (Submodule.fg_span (Set.finite_singleton f)) (bot_sup_eq _) bot_le y hy
  refine ⟨z, ?_⟩
  have hcomp := localCohomologyModuleMapOfLE_comp_zeroToModule A ⊥ (Ideal.span {f})
    Submodule.fg_bot (Submodule.fg_span (Set.finite_singleton f)) bot_le M
  have := congrArg (fun k => ModuleCat.Hom.hom k z) hcomp
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
  rw [← this, hz, hεy]

/-- If `M` vanishes after localization at `S`, so does `H⁰_{V(⊥)}(M)`, which is `M`. -/
private theorem subsingleton_localizedModule_localCohomologyModule_bot
    (A : Type u) [CommRing A] (S : Submonoid A) (M : ModuleCat.{v} A)
    [Subsingleton (LocalizedModule S M)] (i : ℤ) (hi : i = 0) :
    Subsingleton (LocalizedModule S (localCohomologyModule A ⊥ Submodule.fg_bot M i)) := by
  subst hi
  let ε := localCohomologyZeroToModule A ⊥ Submodule.fg_bot M
  refine subsingleton_localizedModule_of_forall_smul_eq_zero S _ fun y => ?_
  obtain ⟨s, hs⟩ := exists_complement_smul_eq_zero S M (ε.hom y)
  refine ⟨s, ?_⟩
  apply localCohomologyZeroToModule_bot_injective A M
  rw [map_smul, hs, map_zero]

/-! ### The divisibility-indexed system of local cohomology modules -/

/-- The derived object `RΓ_{V(f)}(M)` computing local cohomology with support in the principal
closed subset `V(f)`. -/
def principalDerivedLocalCohomology (A : Type u) [CommRing A] (f : A) (M : ModuleCat.{v} A) :
    DerivedCategory (ModuleCat.{v} A) :=
  (Dualizing.derivedPowerTorsionProperty A (Ideal.span {f})
      (Submodule.fg_span (Set.finite_singleton f))).ι.obj
    ((Dualizing.localCohomologyFunctor A (Ideal.span {f})
      (Submodule.fg_span (Set.finite_singleton f))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M))

/-- The counit of the defining local-cohomology adjunction at a principal support. -/
def principalLocalCohomologyCounit (A : Type u) [CommRing A] (f : A) (M : ModuleCat.{v} A) :
    principalDerivedLocalCohomology A f M ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M :=
  (Dualizing.localCohomologyAdjunction A (Ideal.span {f})
    (Submodule.fg_span (Set.finite_singleton f))).counit.app _

/-- The canonical derived direct system `f ↦ RΓ_{V(f)}(M)` for `f ∈ S`. Its transition maps
commute with the counits; nested support and the defining adjunction uniquely characterize
those maps. -/
def derivedLocalCohomologyMultiplicativeSystem
    (A : Type u) [CommRing A] (S : Submonoid A) (M : ModuleCat.{v} A) :
    { F : MultiplicativeIndex S ⥤ DerivedCategory (ModuleCat.{v} A) //
      ∃ η : F ⟶ (Functor.const (MultiplicativeIndex S)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M),
        ∃ hobj : ∀ f : MultiplicativeIndex S,
            F.obj f = principalDerivedLocalCohomology A f M,
        (∀ f : MultiplicativeIndex S,
          η.app f = eqToHom (hobj f) ≫ principalLocalCohomologyCounit A f M) ∧
        (∀ f g : MultiplicativeIndex S, f ≤ g →
          (Dualizing.derivedPowerTorsionProperty A (Ideal.span {(g : A)})
            (Submodule.fg_span (Set.finite_singleton (g : A)))) (F.obj f)) } := by
  classical
  have hspan : ∀ {f g : MultiplicativeIndex S}, f ≤ g →
      Ideal.span {(g : A)} ≤ Ideal.span {(f : A)} := fun hfg =>
    Ideal.span_singleton_le_span_singleton.mpr hfg
  let F : MultiplicativeIndex S ⥤ DerivedCategory (ModuleCat.{v} A) :=
    { obj := fun f => principalDerivedLocalCohomology A f M
      map := fun {f g} hfg =>
        Stacks.Algebraization.localCohomologyComparison A (Ideal.span {(f : A)})
          (Ideal.span {(g : A)})
          (Submodule.fg_span (Set.finite_singleton (f : A)))
          (Submodule.fg_span (Set.finite_singleton (g : A))) (hspan (leOfHom hfg))
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)
      map_id := fun f => localCohomologyComparison_self_eq_id A _ _ M
      map_comp := fun {f g h} hfg hgh =>
        (localCohomologyComparison_comp' A (Ideal.span {(f : A)}) (Ideal.span {(g : A)})
          (Ideal.span {(h : A)})
          (Submodule.fg_span (Set.finite_singleton (f : A)))
          (Submodule.fg_span (Set.finite_singleton (g : A)))
          (Submodule.fg_span (Set.finite_singleton (h : A)))
          (hspan (leOfHom hfg)) (hspan (leOfHom hgh)) M).symm }
  let η : F ⟶ (Functor.const (MultiplicativeIndex S)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) :=
    { app := fun f => principalLocalCohomologyCounit A f M
      naturality := by
        intro f g hfg
        change Stacks.Algebraization.localCohomologyComparison A (Ideal.span {(f : A)})
            (Ideal.span {(g : A)})
            (Submodule.fg_span (Set.finite_singleton (f : A)))
            (Submodule.fg_span (Set.finite_singleton (g : A))) (hspan (leOfHom hfg))
            ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) ≫
            principalLocalCohomologyCounit A g M =
          principalLocalCohomologyCounit A f M ≫ 𝟙 _
        rw [Category.comp_id]
        exact localCohomologyComparison_comp_counit A (Ideal.span {(f : A)})
          (Ideal.span {(g : A)}) _ _ (hspan (leOfHom hfg)) M }
  refine ⟨F, η, fun f => rfl, fun f => (Category.id_comp _).symm, fun f g hfg i x => ?_⟩
  obtain ⟨n, hn, hx⟩ := (((Dualizing.localCohomologyFunctor A (Ideal.span {(f : A)})
    (Submodule.fg_span (Set.finite_singleton (f : A)))).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)).property i) x
  exact ⟨n, hn, fun a ha => hx a (pow_le_pow_left' (hspan hfg) n ha)⟩

/-- The augmentation of the system is the counit of the local-cohomology adjunction. -/
theorem derivedLocalCohomologyMultiplicativeSystem_counit
    (A : Type u) [CommRing A] (S : Submonoid A) (M : ModuleCat.{v} A)
    (f : MultiplicativeIndex S) :
    (derivedLocalCohomologyMultiplicativeSystem A S M).2.choose.app f =
      principalLocalCohomologyCounit A f M := by
  have h := (derivedLocalCohomologyMultiplicativeSystem A S M).2.choose_spec.choose_spec.1 f
  rw [h]
  exact Category.id_comp _

/-- The direct system of cohomology modules induced by the canonical derived transition maps. -/
def localCohomologyMultiplicativeSystem
    (A : Type u) [CommRing A] (S : Submonoid A) (M : ModuleCat.{v} A) (i : ℤ) :
    MultiplicativeIndex S ⥤ ModuleCat.{v} A :=
  (derivedLocalCohomologyMultiplicativeSystem A S M).1 ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{v} A) i

/-- Universe lifting of the local-cohomology system, in a module category large enough to
contain its colimit. -/
def liftedLocalCohomologyMultiplicativeSystem
    (A : Type u) [CommRing A] (S : Submonoid A) (M : ModuleCat.{v} A) (i : ℤ) :
    MultiplicativeIndex S ⥤ ModuleCat.{max u v} A :=
  localCohomologyMultiplicativeSystem A S M i ⋙ ModuleCat.uliftFunctor.{u} A

/-- The canonical comparison from the degree-zero direct limit to the universe lift of `M`,
induced by the counits `H⁰_{V(f)}(M) ⟶ M`. -/
def colimitLocalCohomologyDegreeZeroToModule
    (A : Type u) [CommRing A] (S : Submonoid A) (M : ModuleCat.{v} A) :
    { φ : colimit (liftedLocalCohomologyMultiplicativeSystem A S M 0) ⟶
        (ModuleCat.uliftFunctor.{u} A).obj M //
      ∀ f, colimit.ι (liftedLocalCohomologyMultiplicativeSystem A S M 0) f ≫ φ =
        (ModuleCat.uliftFunctor.{u} A).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map
            ((derivedLocalCohomologyMultiplicativeSystem A S M).2.choose.app f) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (ModuleCat.{v} A) 0).hom.app M) } := by
  classical
  let F := (derivedLocalCohomologyMultiplicativeSystem A S M).1
  let η := (derivedLocalCohomologyMultiplicativeSystem A S M).2.choose
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0
  let U := ModuleCat.uliftFunctor.{u} A
  let D := liftedLocalCohomologyMultiplicativeSystem A S M 0
  let iso := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0
  let c : Cocone D :=
    { pt := U.obj M
      ι :=
        { app := fun f => U.map (H.map (η.app f) ≫ iso.hom.app M)
          naturality := by
            intro f g hfg
            change U.map (H.map (F.map hfg)) ≫ U.map (H.map (η.app g) ≫ iso.hom.app M) =
              U.map (H.map (η.app f) ≫ iso.hom.app M) ≫ 𝟙 _
            rw [Category.comp_id, ← Functor.map_comp, ← Category.assoc, ← H.map_comp]
            have hη : F.map hfg ≫ η.app g = η.app f :=
              (η.naturality hfg).trans (Category.comp_id _)
            rw [hη] } }
  exact ⟨colimit.desc D c, fun f => colimit.ι_desc c f⟩

/-- The leg of the degree-zero colimit comparison at `f` is the canonical map
`H⁰_{V(f)}(M) ⟶ M`, lifted to the larger module universe. -/
private theorem colimitLocalCohomologyDegreeZeroToModule_fac
    (A : Type u) [CommRing A] (S : Submonoid A) (M : ModuleCat.{v} A)
    (f : MultiplicativeIndex S) :
    colimit.ι (liftedLocalCohomologyMultiplicativeSystem A S M 0) f ≫
        (colimitLocalCohomologyDegreeZeroToModule A S M).1 =
      (ModuleCat.uliftFunctor.{u} A).map (localCohomologyZeroToModule A (Ideal.span {(f : A)})
        (Submodule.fg_span (Set.finite_singleton (f : A))) M) := by
  rw [(colimitLocalCohomologyDegreeZeroToModule A S M).2 f,
    derivedLocalCohomologyMultiplicativeSystem_counit]
  rfl

/-! ### A colimit criterion in module categories -/

/-- A map out of a filtered colimit of modules is an isomorphism as soon as every leg of the
cocone is injective and every element of the target is hit by some leg. -/
private theorem isIso_colimit_desc_of_injective_of_exists
    (A : Type u) [CommRing A] {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ ModuleCat.{max u v} A) [HasColimit D]
    (c : Cocone D)
    (hconn : ∀ i j : J, ∃ k, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hinj : ∀ i, Function.Injective (c.ι.app i).hom)
    (hsurj : ∀ y : c.pt, ∃ i, ∃ x : D.obj i, (c.ι.app i).hom x = y) :
    IsIso (colimit.desc D c) := by
  classical
  choose i x hx using hsurj
  let g : c.pt → ↥(colimit D) := fun y ↦ colimit.ι D (i y) (x y)
  have hg (j : J) (z : D.obj j) : g ((c.ι.app j).hom z) = colimit.ι D j z := by
    obtain ⟨k, ⟨p⟩, ⟨q⟩⟩ := hconn (i ((c.ι.app j).hom z)) j
    have heq : D.map p (x ((c.ι.app j).hom z)) = D.map q z := by
      apply hinj k
      rw [Cocone.w_apply, Cocone.w_apply, hx]
    dsimp only [g]
    exact (Cocone.w_apply (colimit.cocone D) p _).symm.trans
      ((congrArg (colimit.ι D k) heq).trans (Cocone.w_apply (colimit.cocone D) q z))
  let G : c.pt ⟶ colimit D := ModuleCat.ofHom
    { toFun := g
      map_add' := by
        intro a b
        obtain ⟨k, ⟨p⟩, ⟨q⟩⟩ := hconn (i a) (i b)
        have ha : (c.ι.app k).hom (D.map p (x a)) = a :=
          (Cocone.w_apply c p _).trans (hx a)
        have hb : (c.ι.app k).hom (D.map q (x b)) = b :=
          (Cocone.w_apply c q _).trans (hx b)
        rw [← ha, ← hb, ← map_add, hg, hg, hg, map_add]
      map_smul' := by
        intro r a
        calc
          g (r • a) = g ((c.ι.app (i a)).hom (r • x a)) := by rw [map_smul, hx a]
          _ = colimit.ι D (i a) (r • x a) := hg (i a) _
          _ = r • colimit.ι D (i a) (x a) := by simp
          _ = r • g ((c.ι.app (i a)).hom (x a)) := by rw [hg (i a) (x a)]
          _ = r • g a := by rw [hx a] }
  refine ⟨⟨G, ?_, ?_⟩⟩
  · refine colimit.hom_ext fun j => ?_
    ext z
    change G ((colimit.ι D j ≫ colimit.desc D c) z) = colimit.ι D j z
    rw [colimit.ι_desc]
    exact hg j z
  · ext y
    change (colimit.ι D (i y) ≫ colimit.desc D c) (x y) = y
    rw [colimit.ι_desc]
    exact hx y

/-- The version of `Stacks.LocalCohomology.isIso_colimit_desc_of_injective_of_exists` for a map
out of the colimit presented by its restrictions to the legs. -/
private theorem isIso_of_colimit_ι_comp
    (A : Type u) [CommRing A] {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ ModuleCat.{max u v} A) [HasColimit D] {T : ModuleCat.{max u v} A}
    (φ : colimit D ⟶ T)
    (hconn : ∀ i j : J, ∃ k, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hinj : ∀ i, Function.Injective (colimit.ι D i ≫ φ).hom)
    (hsurj : ∀ y : T, ∃ i, ∃ x : D.obj i, (colimit.ι D i ≫ φ).hom x = y) :
    IsIso φ := by
  let c : Cocone D :=
    { pt := T
      ι :=
        { app := fun i => colimit.ι D i ≫ φ
          naturality := by
            intro i j p
            dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
            rw [Category.comp_id, ← Category.assoc, colimit.w] } }
  have hφ : φ = colimit.desc D c := by
    refine colimit.hom_ext fun j => ?_
    rw [colimit.ι_desc]
  rw [hφ]
  exact isIso_colimit_desc_of_injective_of_exists A D c hconn hinj hsurj

/-! ### Stacks 0DWT -/

/-- **Stacks 0DWT, degree zero.** If `M` vanishes after localization at `S`, the canonical map
from `colim_{f ∈ S} H⁰_{V(f)}(M)` to the universe lift of `M` is an isomorphism. -/
theorem isIso_colimitLocalCohomology_degreeZero_toModule
    (A : Type u) [CommRing A] (S : Submonoid A) (M : ModuleCat.{v} A)
    [Subsingleton (LocalizedModule S M)] :
    IsIso (colimitLocalCohomologyDegreeZeroToModule A S M).1 := by
  classical
  refine isIso_of_colimit_ι_comp A (liftedLocalCohomologyMultiplicativeSystem A S M 0)
    (colimitLocalCohomologyDegreeZeroToModule A S M).1 ?_ ?_ ?_
  · intro f g
    exact ⟨⟨(f : A) * (g : A), S.mul_mem f.property g.property⟩,
      ⟨homOfLE ⟨(g : A), rfl⟩⟩, ⟨homOfLE ⟨(f : A), mul_comm _ _⟩⟩⟩
  · intro f
    rw [colimitLocalCohomologyDegreeZeroToModule_fac]
    exact fun x y h => ULift.ext (localCohomologyZeroToModule_injective A
      (Ideal.span {(f : A)}) (Submodule.fg_span (Set.finite_singleton (f : A))) M
      (congrArg ULift.down h))
  · intro y
    obtain ⟨s, hs⟩ := exists_complement_smul_eq_zero S M y.down
    obtain ⟨z, hz⟩ :=
      exists_localCohomologyZeroToModule_eq_of_smul_eq_zero A M (s : A) y.down hs
    refine ⟨⟨(s : A), s.property⟩, ULift.up z, ?_⟩
    rw [colimitLocalCohomologyDegreeZeroToModule_fac]
    exact ULift.ext hz

/-- A class in `H¹_{V(f)}(M)` dies on an enlarged principal support `V(f s)` with `s ∈ S`,
because it dies on all of `Spec A` and `M` vanishes after localization at `S`. -/
private theorem localCohomologyMultiplicativeSystem_degreeOne_eventually_zero
    (A : Type u) [CommRing A] (S : Submonoid A) (M : ModuleCat.{v} A)
    [Subsingleton (LocalizedModule S M)] (f : MultiplicativeIndex S)
    (x : (localCohomologyMultiplicativeSystem A S M 1).obj f) :
    ∃ (g : MultiplicativeIndex S) (hfg : f ≤ g),
      ((localCohomologyMultiplicativeSystem A S M 1).map (homOfLE hfg)).hom x = 0 := by
  classical
  have hvan := subsingleton_localizedModule_localCohomologyModule_bot A S M ((1 : ℤ) - 1)
    (by norm_num)
  have hx : (localCohomologyModuleMapOfLE A ⊥ (Ideal.span {(f : A)}) Submodule.fg_bot
      (Submodule.fg_span (Set.finite_singleton (f : A))) bot_le M 1).hom x = 0 :=
    (ModuleCat.isZero_iff_subsingleton.mp (isZero_localCohomologyModule_bot_one A M)).elim _ _
  obtain ⟨s, hs⟩ := kernel_eventually_zero_of_eq A ⊥ S Submodule.fg_bot M 1 hvan (f : A)
    (Ideal.span {(f : A)}) (Submodule.fg_span (Set.finite_singleton (f : A)))
    (bot_sup_eq _) bot_le x hx
  refine ⟨⟨(f : A) * (s : A), S.mul_mem f.property s.property⟩, ⟨(s : A), rfl⟩, ?_⟩
  exact hs (Ideal.span {(f : A) * (s : A)})
    (Submodule.fg_span (Set.finite_singleton ((f : A) * (s : A)))) (bot_sup_eq _)
    (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right (f : A) (s : A)))

/-- **Stacks 0DWT, degree one.** If `M` vanishes after localization at `S`, then
`colim_{f ∈ S} H¹_{V(f)}(M)` is zero. -/
theorem isZero_colimitLocalCohomology_degreeOne
    (A : Type u) [CommRing A] (S : Submonoid A) (M : ModuleCat.{v} A)
    [Subsingleton (LocalizedModule S M)] :
    IsZero (colimit (liftedLocalCohomologyMultiplicativeSystem A S M 1)) := by
  classical
  let D := liftedLocalCohomologyMultiplicativeSystem A S M 1
  refine (IsZero.iff_id_eq_zero (colimit D)).2 (colimit.hom_ext fun f => ?_)
  ext x
  obtain ⟨g, hfg, hx⟩ :=
    localCohomologyMultiplicativeSystem_degreeOne_eventually_zero A S M f x.down
  have hx' : (D.map (homOfLE hfg)).hom x = 0 := ULift.ext hx
  have h := congrArg (fun k => k x) (colimit.w D (homOfLE hfg))
  simp only [ConcreteCategory.comp_apply, hx', map_zero] at h
  simpa using h.symm

/-! ### Non-vacuity -/

/-- The hypothesis of Stacks 0DWT is satisfiable with `M` arbitrary: at `S = ⊤`, which contains
`0`, every module vanishes after localization. So the degree-zero conclusion identifies the
colimit with an arbitrary module, and is not vacuous. -/
theorem subsingleton_localizedModule_top (A : Type u) [CommRing A] (M : ModuleCat.{v} A) :
    Subsingleton (LocalizedModule (⊤ : Submonoid A) M) :=
  subsingleton_localizedModule_of_forall_smul_eq_zero ⊤ M
    fun _ => ⟨⟨0, Submonoid.mem_top 0⟩, zero_smul A _⟩

/-- The hypothesis of Stacks 0DWT is not automatic: at the trivial submonoid `S = ⊥` it fails for
every nonzero module, so the theorems above are not statements about all modules. -/
theorem not_subsingleton_localizedModule_bot (A : Type u) [CommRing A] (M : ModuleCat.{v} A)
    (m : M) (hm : m ≠ 0) :
    ¬ Subsingleton (LocalizedModule (⊥ : Submonoid A) M) := by
  intro hsub
  have heq : LocalizedModule.mk m (1 : (⊥ : Submonoid A)) =
    LocalizedModule.mk 0 (1 : (⊥ : Submonoid A)) := Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp heq
  have hu1 : (u : A) = 1 := Submonoid.mem_bot.mp u.property
  have h2 : (u : A) • m = 0 := by simpa [Submonoid.smul_def] using hu
  exact hm (by rwa [hu1, one_smul] at h2)

end Stacks.LocalCohomology

end
