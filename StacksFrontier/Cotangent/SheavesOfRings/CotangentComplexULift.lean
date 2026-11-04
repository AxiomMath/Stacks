module

public import Mathlib.RingTheory.Finiteness.Small
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits
public import StacksFrontier.Cotangent.SchemeCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageDerivationTransport
public import StacksFrontier.Cotangent.SheavesOfRings.ULiftStandardResolution
public import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# Lifting the universe of the sections commutes with the cotangent complex

Let `a : A ⟶ B` be a homomorphism of sheaves of commutative rings on a site, with sections in a
universe containing the universes of the objects and of the morphisms of the site. Raising the
universe of the sections of `A` and `B` by `ULift` gives a homomorphism `↑a : ↑A ⟶ ↑B`, and
raising the universe of the sections of a sheaf of `B`-modules gives a sheaf of `↑B`-modules. This
file proves that the second operation carries the cotangent complex `L_{B/A}` to the cotangent
complex `L_{↑B/↑A}`.

## Main definitions

* `CategoryTheory.Sheaf.liftTargetModules`: the universe lift of sheaves of `B`-modules, with
  values in sheaves of `↑B`-modules: the sections of `↑M` over `U` are `ULift (M(U))`, a module
  over `ULift (B(U))` through `ULift.ringEquiv`.
* `CategoryTheory.Sheaf.liftCotangentSimplicialModule`: the lift of the base-changed simplicial
  module of `a`, as a corepresentation of the `↑A`-derivations of the standard resolution of `↑a`.

## Main results

* `CategoryTheory.Sheaf.cotangentComplexULiftIso`: the lift of the cotangent complex of `a` is the
  cotangent complex of `↑a`.
* `AlgebraicGeometry.Scheme.Hom.cotangentComplexULiftIso`: for a morphism of schemes `f`, the
  lift of the cotangent complex `L_{X/Y}` of Tag 08T2 to sections in the next universe is the
  cotangent complex of the lifted structure map of the Zariski ringed topoi.

## Implementation notes

The lift `↑` of sheaves of commutative rings is `sheafCompose J commRingCatULift`, sectionwise
`ULift`. The cotangent complex of `↑a` is characterized by its simplicial module of base-changed
differentials, a corepresentation of the `↑A`-derivations of the standard resolution of `↑a`
(`CategoryTheory.Sheaf.CotangentSimplicialModuleData`). The standard resolution of `↑a` is the
lift of that of `a` (`CategoryTheory.Sheaf.resolutionULiftIso`), so it suffices to show that the
lift of `Ω_{P_n/A} ⊗_{P_n} B` corepresents the `↑A`-derivations of `↑P_n` into every sheaf of
`↑B`-modules, including those whose sections are not lifts
(`CategoryTheory.Sheaf.bijective_liftDerivation_postcomp`). The source of the corepresentation is
what makes this possible: by Tag 08SX the term `Ω_{P_n/A} ⊗_{P_n} B` receives a locally bijective
map from the presheaf `U ↦ L^{-n}_{B(U)/A(U)}`, so its lift receives a locally bijective map from
the lifted presheaf, and maps out of it into a sheaf are maps of presheaves out of
`U ↦ ULift (L^{-n}_{B(U)/A(U)})`. Such a map is determined by its values on the pure
differentials `1 ⊗ d p`, which generate
(`CategoryTheory.Sheaf.span_sectionsCotangentDifferential`), and every derivation of `P'_n(U)`
into a module in an arbitrary universe is such a map
(`CategoryTheory.Sheaf.exists_sectionsCotangentComplex_linearMap`): its values span a small
submodule, to which the universal property in the universe of the rings applies. Finally, two
derivations of `↑P_n` agree as soon as they agree on the image of the lifted sectionwise
resolution `U ↦ ULift (P'_n(U))`, the comparison map being inverted by sheafification
(`CategoryTheory.Sheaf.W_whiskerRight_commRingCatULift`,
`CategoryTheory.Sheaf.derivation_ext_of_W`).

## References

* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08T2](https://stacks.math.columbia.edu/tag/08T2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicGeometry.SheafOfModules (commRingCatULift)

namespace CategoryTheory.Sheaf

universe u v w w'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-! ## The universe lift of sheaves of modules -/

section Modules

/-- **The universe lift of sheaves of `B`-modules**: the sections of the lift of `M` over `U` are
`ULift (M(U))`, a module over the sections `ULift (B(U))` of the lift of `B` through
`ULift.ringEquiv`. -/
noncomputable def liftTargetModules (B : Sheaf J CommRingCat.{max u v w}) :
    targetModules.{u, v, w} J B ⥤
      targetModules.{u, v, max w w'} J ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B) :=
  Stacks.SheafOfModules.moduleULift.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf B) ⋙
    (Stacks.UniverseLift.uliftRingTransport.{w'} B.obj).sheafFunctor
      (R := Stacks.SheafOfModules.Tensor.ringSheaf B)
      (R' := Stacks.SheafOfModules.Tensor.ringSheaf
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B))

/-- The universe lift of sheaves of modules is additive. -/
instance liftTargetModules_additive (B : Sheaf J CommRingCat.{max u v w}) :
    (liftTargetModules.{u, v, w, w'} J B).Additive := by
  have h₂ : ((Stacks.UniverseLift.uliftRingTransport.{w'} B.obj).sheafFunctor
      (R := Stacks.SheafOfModules.Tensor.ringSheaf B)
      (R' := Stacks.SheafOfModules.Tensor.ringSheaf
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B))).Additive :=
    Stacks.UniverseLift.RingTransport.sheafFunctor_additive
      (R := Stacks.SheafOfModules.Tensor.ringSheaf B)
      (R' := Stacks.SheafOfModules.Tensor.ringSheaf
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B))
      (Stacks.UniverseLift.uliftRingTransport.{w'} B.obj)
  exact Functor.instAdditiveComp _ _

/-- The lift of a derivation: an `A₀`-derivation of `P` with values in a sheaf of `B₀`-modules
`N`, read along `ε : P ⟶ B₀`, gives an `↑A₀`-derivation of `↑P` with values in the lift of `N`,
read along `↑ε`, by `x ↦ ULift.up (d x.down)`. -/
noncomputable def liftDerivation {A₀ P B₀ : Sheaf J CommRingCat.{max u v w}} {b : A₀ ⟶ P}
    {ε : P ⟶ B₀} {N : targetModules.{u, v, w} J B₀}
    (d : ((SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).map ε)).obj
        N).val.Derivation' b.hom) :
    ((SheafOfModules.restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{max u v w w'} RingCat.{max u v w w'})).map
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map ε))).obj
        ((liftTargetModules.{u, v, w, w'} J B₀).obj N)).val.Derivation'
      ((sheafCompose J commRingCatULift.{max u v w, w'}).map b).hom where
  d {U} := AddMonoidHom.mk' (fun x => ULift.up (d.d x.down))
    (fun x y => congrArg ULift.up (d.d.map_add x.down y.down))
  d_mul {U} x y := congrArg ULift.up (d.d_mul x.down y.down)
  d_map {U V} g x := congrArg ULift.up (d.d_map g x.down)
  d_app {U} x := congrArg ULift.up (d.d_app x.down)

/-- The lift of a derivation has components `x ↦ ULift.up (d x.down)`. -/
theorem liftDerivation_d {A₀ P B₀ : Sheaf J CommRingCat.{max u v w}} {b : A₀ ⟶ P}
    {ε : P ⟶ B₀} {N : targetModules.{u, v, w} J B₀}
    (d : ((SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).map ε)).obj
        N).val.Derivation' b.hom)
    {U : Cᵒᵖ} (x : ((sheafCompose J commRingCatULift.{max u v w, w'}).obj P).obj.obj U) :
    (liftDerivation.{u, v, w, w'} J d).d x = ULift.up (d.d x.down) :=
  rfl

end Modules

/-! ## The sectionwise cotangent terms in an arbitrary universe -/

section Sections

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- The pure differentials `1 ⊗ d p` generate the degree-`-n` term of `L_{B(U)/A(U)}` as a
`B(U)`-module. -/
theorem span_sectionsCotangentDifferential (U : Cᵒᵖ) (n : ℕ) :
    Submodule.span (sectionsAlgebra J f U)
      (Set.range (sectionsCotangentDifferential' J f U n)) = ⊤ := by
  let N₀ := Submodule.span (sectionsAlgebra J f U)
    (Set.range (sectionsCotangentDifferential' J f U n))
  have h := sectionsCotangentComplex_hom_ext J f U n
    (N := ModuleCat.of (sectionsAlgebra J f U)
      ((CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).X (-(n : ℤ)) ⧸ N₀))
    (ModuleCat.ofHom N₀.mkQ) 0 (fun p => by
      show N₀.mkQ _ = 0
      exact (Submodule.Quotient.mk_eq_zero N₀).mpr (Submodule.subset_span ⟨p, rfl⟩))
  rw [eq_top_iff]
  intro x _
  exact (Submodule.Quotient.mk_eq_zero N₀).mp (ConcreteCategory.congr_hom h x)

/-- **Linear maps out of the degree-`-n` term of `L_{B(U)/A(U)}` into a module in an arbitrary
universe are derivations of the degree-`n` term of the standard resolution of `A(U) → B(U)`**:
every such derivation is the composite of the pure differential `1 ⊗ d -` with a linear map. The
values of the derivation span a submodule which is small, so the universal property of the
degree-`-n` term in its own universe applies to it. -/
theorem exists_sectionsCotangentComplex_linearMap (U : Cᵒᵖ) (n : ℕ) {M : Type*}
    [AddCommGroup M] [Module (sectionsAlgebra J f U) M]
    (d : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌) →+ M)
    (hmul : ∀ p q, d (p * q) =
      CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) (op ⦋n⦌) p • d q +
        CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) (op ⦋n⦌) q • d p)
    (hbase : ∀ a : A.obj.obj U, d (algebraMap (A.obj.obj U) _ a) = 0) :
    ∃ α : (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).X (-(n : ℤ)) →ₗ[sectionsAlgebra J f U] M,
      ∀ p, α (sectionsCotangentDifferential' J f U n p) = d p := by
  let S := sectionsAlgebra J f U
  let M₀ := Submodule.span S (Set.range d)
  have : Small.{max u v w} M₀ := Submodule.small_span _
  let e := Shrink.linearEquiv.{max u v w} S M₀
  let N : ModuleCat.{max u v w} S := ModuleCat.of S (Shrink.{max u v w} M₀)
  have hmem (p) : d p ∈ M₀ := Submodule.subset_span ⟨p, rfl⟩
  let d₀ : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U) S).left.obj
      (op ⦋n⦌) →+ N := e.symm.toAddMonoidHom.comp (d.codRestrict M₀ hmem)
  have hd₀ (p) : e (d₀ p) = ⟨d p, hmem p⟩ := e.apply_symm_apply _
  have hmul₀ (p q) : d₀ (p * q) =
      CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U) S
          (op ⦋n⦌) p • d₀ q +
        CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U) S
          (op ⦋n⦌) q • d₀ p := by
    apply e.injective
    rw [hd₀, map_add, map_smul, map_smul, hd₀, hd₀]
    exact Subtype.ext (hmul p q)
  have hbase₀ (a : A.obj.obj U) : d₀ (algebraMap (A.obj.obj U) _ a) = 0 := by
    apply e.injective
    rw [hd₀, map_zero]
    exact Subtype.ext (hbase a)
  let β := CommAlgCat.cotangentTermDesc.{max u v w, max u v w} (A.obj.obj U) S (op ⦋n⦌) N d₀
    hmul₀ hbase₀
  refine ⟨M₀.subtype ∘ₗ e.toLinearMap ∘ₗ β.hom ∘ₗ
    (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (A.obj.obj U) S n).hom.hom,
    fun p => ?_⟩
  have h₁ : (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (A.obj.obj U) S n).hom
      (sectionsCotangentDifferential' J f U n p) =
      CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U) S (op ⦋n⦌) p :=
    ConcreteCategory.congr_hom
      (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (A.obj.obj U) S n).inv_hom_id
      _
  show M₀.subtype (e (β ((CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
    (A.obj.obj U) S n).hom (sectionsCotangentDifferential' J f U n p)))) = d p
  rw [h₁, show β (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U) S
      (op ⦋n⦌) p) = d₀ p from CommAlgCat.cotangentTermDesc_differential _ _ _ _ _ _ _ p]
  exact congrArg Subtype.val (hd₀ p)

end Sections

/-! ## The lift of the base-changed differentials corepresents the lifted derivations -/

section Corepresentation

variable {A B : Sheaf J CommRingCat.{max u v w}} (a : A ⟶ B)

attribute [local instance] moduleOfSections

/-- The canonical map from the lift of the presheaf `U ↦ L^{-n}_{B(U)/A(U)}` of Tag 08SX to the
underlying presheaf of the lift of the degree-`n` term of the base-changed simplicial module. -/
noncomputable def liftSectionwiseCotangentTermComparison (n : ℕ) :
    (Stacks.UniverseLift.RingTransport.functor
      (R' := (Stacks.SheafOfModules.Tensor.ringSheaf
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B)).obj)
      (Stacks.UniverseLift.uliftRingTransport.{w'} B.obj)).obj
        ((Stacks.SheafOfModules.presheafULift.{w'}
          (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).obj
            (sectionwiseCotangentTerm J a (-(n : ℤ)))) ⟶
      ((liftTargetModules.{u, v, w, w'} J B).obj
        ((cotangentSimplicialModule J a).object.obj (op ⦋n⦌))).val :=
  (Stacks.UniverseLift.RingTransport.functor
      (R' := (Stacks.SheafOfModules.Tensor.ringSheaf
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B)).obj)
      (Stacks.UniverseLift.uliftRingTransport.{w'} B.obj)).map
    ((Stacks.SheafOfModules.presheafULift.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
        (sectionwiseCotangentTermComparison J a (-(n : ℤ)) ≫
          (cotangentComplex_degreeIso J a n).hom.val))

/-- Before lifting, the canonical map is inverted by sheafification. -/
theorem W_toPresheaf_sectionwiseCotangentTermComparison_comp (n : ℕ) :
    J.W ((PresheafOfModules.toPresheaf _).map
      (sectionwiseCotangentTermComparison J a (-(n : ℤ)) ≫
        (cotangentComplex_degreeIso J a n).hom.val)) := by
  rw [Functor.map_comp]
  have : IsIso ((PresheafOfModules.toPresheaf _).map (cotangentComplex_degreeIso J a n).hom.val) :=
    Functor.map_isIso (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)
      (cotangentComplex_degreeIso J a n).hom
  exact MorphismProperty.comp_mem _ _ _
    (W_toPresheaf_sectionwiseCotangentTermComparison J a _)
    (ObjectProperty.isLocal_of_isIso _ _)

/-- The lifted canonical map is locally injective. -/
theorem isLocallyInjective_liftSectionwiseCotangentTermComparison (n : ℕ) :
    PresheafOfModules.IsLocallyInjective J
      (liftSectionwiseCotangentTermComparison.{u, v, w, w'} J a n) := by
  have := (W_toPresheaf_sectionwiseCotangentTermComparison_comp J a n).isLocallyInjective
  exact Stacks.Sheaves.UniverseLift.isLocallyInjective_uliftFunctor.{u, v, max u v w, w'}
    ((PresheafOfModules.toPresheaf _).map
      (sectionwiseCotangentTermComparison J a (-(n : ℤ)) ≫
        (cotangentComplex_degreeIso J a n).hom.val))

/-- The lifted canonical map is locally surjective. -/
theorem isLocallySurjective_liftSectionwiseCotangentTermComparison (n : ℕ) :
    PresheafOfModules.IsLocallySurjective J
      (liftSectionwiseCotangentTermComparison.{u, v, w, w'} J a n) := by
  have := (W_toPresheaf_sectionwiseCotangentTermComparison_comp J a n).isLocallySurjective
  exact Stacks.Sheaves.UniverseLift.isLocallySurjective_uliftFunctor.{u, v, max u v w, w'}
    ((PresheafOfModules.toPresheaf _).map
      (sectionwiseCotangentTermComparison J a (-(n : ℤ)) ≫
        (cotangentComplex_degreeIso J a n).hom.val))

/-- The lifted canonical map sends the lift of the pure differential `1 ⊗ d p` to the lift of
the universal derivation of the image of `p` in `P_n(U)`. -/
theorem liftSectionwiseCotangentTermComparison_app_differential (n : ℕ) (U : Cᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J a U)).left.obj (op ⦋n⦌)) :
    (liftSectionwiseCotangentTermComparison.{u, v, w, w'} J a n).app U
        (ULift.up (sectionsCotangentDifferential' J a U n p)) =
      ULift.up ((universalSheafDerivation J a (op ⦋n⦌)).d
        ((sectionwiseResolutionComparison J a (op ⦋n⦌)).app U p)) := by
  show ULift.up ((cotangentComplex_degreeIso J a n).hom.val.app U
    ((sectionwiseCotangentTermComparison J a (-(n : ℤ))).app U
      (sectionsCotangentDifferential' J a U n p))) = _
  rw [sectionwiseCotangentTermComparison_app_differential]
  exact congrArg ULift.up (ConcreteCategory.congr_hom (congrArg (fun k => k.val.app U)
    (cotangentComplex_degreeIso J a n).inv_hom_id) _)

/-- **The lift of `Ω_{P_n/A} ⊗_{P_n} B` corepresents the `↑A`-derivations of `↑P_n`**, with values
in an arbitrary sheaf of `↑B`-modules, not only in lifts: postcomposition with the lift of the
universal derivation is a bijection. -/
theorem bijective_liftDerivation_postcomp (n : ℕ)
    (M : targetModules.{u, v, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B)) :
    Function.Bijective (fun φ : (liftTargetModules.{u, v, w, w'} J B).obj
        ((cotangentSimplicialModule J a).object.obj (op ⦋n⦌)) ⟶ M =>
      (liftDerivation.{u, v, w, w'} J (universalSheafDerivation J a (op ⦋n⦌))).postcomp
        ((SheafOfModules.restrictScalars ((sheafCompose J
          (forget₂ CommRingCat.{max u v w w'} RingCat.{max u v w w'})).map
            ((sheafCompose J commRingCatULift.{max u v w, w'}).map
              (resolutionAugmentation J a (op ⦋n⦌))))).map φ).val) := by
  have := isLocallyInjective_liftSectionwiseCotangentTermComparison.{u, v, w, w'} J a n
  have := isLocallySurjective_liftSectionwiseCotangentTermComparison.{u, v, w, w'} J a n
  let χ := liftSectionwiseCotangentTermComparison.{u, v, w, w'} J a n
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v w w'} :=
    wEqualsLocallyBijectiveAddCommGrpCat.{u, v, max w w'} J
  let e := PresheafOfModules.homEquivOfIsLocallyBijective χ M.isSheaf
  let c := sectionwiseResolutionComparison J a (op ⦋n⦌)
  have hgen := liftSectionwiseCotangentTermComparison_app_differential.{u, v, w, w'} J a n
  have hspan (U : Cᵒᵖ) (y) : y ∈ Submodule.span (sectionsAlgebra J a U)
      (Set.range (sectionsCotangentDifferential' J a U n)) := by
    rw [span_sectionsCotangentDifferential]
    trivial
  constructor
  · intro φ ψ h
    have hd (U : Cᵒᵖ) (p) :
        (χ ≫ φ.val).app U (ULift.up (sectionsCotangentDifferential' J a U n p)) =
        (χ ≫ ψ.val).app U (ULift.up (sectionsCotangentDifferential' J a U n p)) := by
      show φ.val.app U (χ.app U _) = ψ.val.app U (χ.app U _)
      rw [hgen]
      exact PresheafOfModules.Derivation.congr_d h (ULift.up (c.app U p))
    apply SheafOfModules.hom_ext
    apply e.injective
    show χ ≫ φ.val = χ ≫ ψ.val
    apply PresheafOfModules.Hom.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨y⟩
    let X := ((Stacks.UniverseLift.RingTransport.functor
      (R' := (Stacks.SheafOfModules.Tensor.ringSheaf
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B)).obj)
      (Stacks.UniverseLift.uliftRingTransport.{w'} B.obj)).obj
      ((Stacks.SheafOfModules.presheafULift.{w'}
        (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).obj
          (sectionwiseCotangentTerm J a (-(n : ℤ))))).obj U
    induction hspan U y using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact hd U p
    | zero =>
      exact ((map_zero ((χ ≫ φ.val).app U).hom).trans (map_zero ((χ ≫ ψ.val).app U).hom).symm)
    | add x y _ _ hx hy =>
      exact ((map_add ((χ ≫ φ.val).app U).hom (show X from ULift.up x)
        (show X from ULift.up y)).trans (congrArg₂ (· + ·) hx hy)).trans
          (map_add ((χ ≫ ψ.val).app U).hom (show X from ULift.up x)
            (show X from ULift.up y)).symm
    | smul b x _ hx =>
      let b' : (Stacks.SheafOfModules.Tensor.ringSheaf
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B)).obj.obj U := ULift.up b
      exact ((map_smul ((χ ≫ φ.val).app U).hom b' (show X from ULift.up x)).trans
        (congrArg (b' • ·) hx)).trans
          (map_smul ((χ ≫ ψ.val).app U).hom b' (show X from ULift.up x)).symm
  · intro Dd
    let σ (U : Cᵒᵖ) : (sectionsAlgebra J a U) →+* (Stacks.SheafOfModules.Tensor.ringSheaf
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B)).obj.obj U :=
      ULift.ringEquiv.symm.toRingHom
    have hex (U : Cᵒᵖ) : ∃ α : (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J a U)).X (-(n : ℤ)) →+ M.val.obj U,
        (∀ (b : sectionsAlgebra J a U) y, α (b • y) = σ U b • α y) ∧
        ∀ p, α (sectionsCotangentDifferential' J a U n p) = Dd.d (ULift.up (c.app U p)) := by
      let : Module (sectionsAlgebra J a U) (M.val.obj U) := Module.compHom _ (σ U)
      let d : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J a U)).left.obj (op ⦋n⦌) →+ M.val.obj U :=
        { toFun := fun p => Dd.d (ULift.up (c.app U p))
          map_zero' := (congrArg (fun x => Dd.d (ULift.up x)) (map_zero (c.app U).hom)).trans
            (map_zero (Dd.d (X := U)))
          map_add' := fun p q => (congrArg (fun x => Dd.d (ULift.up x))
            (map_add (c.app U).hom p q)).trans (map_add (Dd.d (X := U)) _ _) }
      have hmul (p q) : d (p * q) =
          CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
              (sectionsAlgebra J a U) (op ⦋n⦌) p • d q +
            CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
              (sectionsAlgebra J a U) (op ⦋n⦌) q • d p := by
        have h₁ := resolutionAugmentation_resolutionSectionsComparison J a U (op ⦋n⦌) p
        have h₂ := resolutionAugmentation_resolutionSectionsComparison J a U (op ⦋n⦌) q
        refine (congrArg (fun x => Dd.d (ULift.up x)) (map_mul (c.app U).hom p q)).trans
          ((Dd.d_mul (ULift.up (c.app U p)) (ULift.up (c.app U q))).trans ?_)
        exact congrArg₂ (· + ·)
          (congrArg (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf
            ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B)).obj.obj U =>
              r • (show M.val.obj U from Dd.d (ULift.up (c.app U q)))) (congrArg ULift.up h₁))
          (congrArg (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf
            ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B)).obj.obj U =>
              r • (show M.val.obj U from Dd.d (ULift.up (c.app U p)))) (congrArg ULift.up h₂))
      have hbase (a₀ : A.obj.obj U) : d (algebraMap (A.obj.obj U) _ a₀) = 0 := by
        have hb := ConcreteCategory.congr_hom
          (NatTrans.congr_app (sectionwiseResolutionBase_comp_comparison J a (op ⦋n⦌)) U) a₀
        exact (congrArg (fun x => Dd.d (ULift.up x)) hb).trans (Dd.d_app (ULift.up a₀))
      obtain ⟨α, hα⟩ := exists_sectionsCotangentComplex_linearMap J a U n d hmul hbase
      exact ⟨α.toAddMonoidHom, fun b y => α.map_smul b y, hα⟩
    choose α hα using hex
    have hnat {U V : Cᵒᵖ} (g : U ⟶ V) (y) :
        α V ((sectionwiseCotangentTerm J a (-(n : ℤ))).map g y) = M.val.map g (α U y) := by
      induction hspan U y using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨p, rfl⟩ := hx
        have h₁ := squareCotangentComplexMap_sectionsCotangentDifferential' J a g n p
        have hc := ConcreteCategory.congr_hom (c.naturality g) p
        refine (congrArg (α V) h₁).trans (((hα V).2 _).trans ?_)
        rw [(hα U).2]
        exact (congrArg (fun x => Dd.d (ULift.up x)) hc).trans (Dd.d_map g (ULift.up (c.app U p)))
      | zero =>
        exact (congrArg (α V) (map_zero _)).trans ((map_zero _).trans
          ((map_zero (M.val.map g).hom).symm.trans (congrArg (M.val.map g) (map_zero _).symm)))
      | add x y _ _ hx hy =>
        exact (congrArg (α V) (map_add _ x y)).trans ((map_add _ _ _).trans
          ((congrArg₂ (· + ·) hx hy).trans ((map_add (M.val.map g).hom _ _).symm.trans
            (congrArg (M.val.map g) (map_add _ x y).symm))))
      | smul b x _ hx =>
        refine (congrArg (α V) ((sectionwiseCotangentTerm J a (-(n : ℤ))).map_smul g b x)).trans
          (((hα V).1 _ _).trans ?_)
        refine (congrArg (σ V _ • ·) hx).trans ?_
        refine Eq.trans ?_ (congrArg (M.val.map g) ((hα U).1 b x)).symm
        exact (M.val.map_smul g (σ U b) (α U x)).symm
    let F := Stacks.UniverseLift.RingTransport.functor
      (R' := (Stacks.SheafOfModules.Tensor.ringSheaf
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B)).obj)
      (Stacks.UniverseLift.uliftRingTransport.{w'} B.obj)
    let P' := (Stacks.SheafOfModules.presheafULift.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).obj
        (sectionwiseCotangentTerm J a (-(n : ℤ)))
    let ψ : F.obj P' ⟶ M.val :=
      { app U := ModuleCat.ofHom (X := (F.obj P').obj U) (Y := M.val.obj U)
          { toFun := fun x => α U x.down
            map_add' := fun x y => (α U).map_add x.down y.down
            map_smul' := fun r x => (hα U).1 r.down x.down }
        naturality := fun {U V} g => by
          ext x
          exact hnat g x.down }
    have hψ : χ ≫ e.symm ψ = ψ := e.apply_symm_apply ψ
    refine ⟨⟨e.symm ψ⟩, ?_⟩
    refine derivation_ext_of_W.{u, v, max w w'} J
      ((sheafCompose J commRingCatULift.{max u v w, w'}).map (resolutionBase J a (op ⦋n⦌)))
      (sectionwiseResolutionPresheaf J a (op ⦋n⦌) ⋙ commRingCatULift.{max u v w, w'})
      (Functor.whiskerRight c commRingCatULift.{max u v w, w'})
      (W_whiskerRight_commRingCatULift.{u, v, w, w'} J c
        (W_sectionwiseResolutionComparison J a (op ⦋n⦌))) _ _ _ (fun U q => ?_)
    show (e.symm ψ).app U (ULift.up ((universalSheafDerivation J a (op ⦋n⦌)).d
      (c.app U q.down))) = Dd.d (ULift.up (c.app U q.down))
    refine (congrArg ((e.symm ψ).app U) (hgen U q.down).symm).trans ?_
    refine (ConcreteCategory.congr_hom (congrArg (fun k : F.obj P' ⟶ M.val => k.app U) hψ)
      (ULift.up (sectionsCotangentDifferential' J a U n q.down))).trans ?_
    exact (hα U).2 q.down

/-- `bijective_liftDerivation_postcomp` in an arbitrary simplicial degree. -/
theorem bijective_liftDerivation_postcomp' (n : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B)) :
    Function.Bijective (fun φ : (liftTargetModules.{u, v, w, w'} J B).obj
        ((cotangentSimplicialModule J a).object.obj n) ⟶ M =>
      (liftDerivation.{u, v, w, w'} J (universalSheafDerivation J a n)).postcomp
        ((SheafOfModules.restrictScalars ((sheafCompose J
          (forget₂ CommRingCat.{max u v w w'} RingCat.{max u v w w'})).map
            ((sheafCompose J commRingCatULift.{max u v w, w'}).map
                (resolutionAugmentation J a n)))).map φ).val) := by
  obtain ⟨⟨n⟩⟩ := n
  exact bijective_liftDerivation_postcomp.{u, v, w, w'} J a n M

end Corepresentation

/-! ## The lift of the cotangent complex -/

section Lift

variable {A B : Sheaf J CommRingCat.{max u v w}} (a : A ⟶ B)

/-- **The degreewise corepresentation**: a morphism out of the lift of `Ω_{P_n/A} ⊗_{P_n} B`
into a sheaf of `↑B`-modules is an `↑A`-derivation of the degree-`n` term of the standard
resolution of `↑a`. It is postcomposition with the lift of the universal derivation, followed
by the transport along the comparison `↑P_n ≅ P_n(↑a)` of the standard resolutions. -/
noncomputable def liftCotangentDerivationEquiv (n : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B)) :
    ((liftTargetModules.{u, v, w, w'} J B).obj ((cotangentSimplicialModule J a).object.obj n) ⟶
        M) ≃ resolutionDerivations.{u, v, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) n M :=
  (Equiv.ofBijective _ (bijective_liftDerivation_postcomp'.{u, v, w, w'} J a n M)).trans
    (Stacks.Sheaves.RingedToposModules.derivationRingEquiv M
      (resolutionULiftIso.{u, v, w, w'} J a n) (resolutionULiftIso_base.{u, v, w, w'} J a n)
      (resolutionULiftIso_augmentation.{u, v, w, w'} J a n))

/-- The corepresented derivation of a morphism out of the lift of `Ω_{P_n/A} ⊗_{P_n} B`. -/
theorem liftCotangentDerivationEquiv_d (n : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, max w w'} J ((sheafCompose J commRingCatULift.{max u v w, w'}).obj B))
    (φ : (liftTargetModules.{u, v, w, w'} J B).obj
      ((cotangentSimplicialModule J a).object.obj n) ⟶ M) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) n).obj.obj U) :
    (liftCotangentDerivationEquiv.{u, v, w, w'} J a n M φ).d x =
      φ.val.app U (ULift.up ((universalSheafDerivation J a n).d
        ((resolutionULiftIso.{u, v, w, w'} J a n).inv.hom.app U x).down)) :=
  rfl

/-- The comparison of the standard resolutions, read backwards, is natural in the simplicial
variable. -/
theorem resolutionULiftIso_inv_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    ((standardResolution.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)).left.map g).right ≫
        (resolutionULiftIso.{u, v, w, w'} J a j).inv =
      (resolutionULiftIso.{u, v, w, w'} J a i).inv ≫
        (sheafCompose J commRingCatULift.{max u v w, w'}).map
            ((standardResolution.{v, u, w} J a).left.map g).right := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← resolutionULiftIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **The lift of the base-changed simplicial module of `a` is a base-changed simplicial module
of `↑a`**: its terms corepresent the `↑A`-derivations of the standard resolution of `↑a`,
naturally in the coefficient module and compatibly with the simplex maps. -/
noncomputable def liftCotangentSimplicialModule :
    CotangentSimplicialModuleData.{u, v, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) where
  object := (cotangentSimplicialModule J a).object ⋙ liftTargetModules.{u, v, w, w'} J B
  derivationEquiv := liftCotangentDerivationEquiv.{u, v, w, w'} J a
  naturality _ _ _ _ _ :=
    PresheafOfModules.Derivation.ext (funext fun _ => AddMonoidHom.ext fun _ => rfl)
  simplex_naturality {i j} g M h U x := by
    rw [liftCotangentDerivationEquiv_d, liftCotangentDerivationEquiv_d]
    have hD := (cotangentSimplicialModule J a).simplex_naturality g
      ((cotangentSimplicialModule J a).object.obj j) (𝟙 _) U
      ((resolutionULiftIso.{u, v, w, w'} J a i).inv.hom.app U x).down
    rw [Category.comp_id, CotangentSimplicialModuleData.derivationEquiv_eq_postcomp] at hD
    have hρ := ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app U)
      (resolutionULiftIso_inv_naturality.{u, v, w, w'} J a g)) x
    change h.val.app U (ULift.up (((cotangentSimplicialModule J a).object.map g).val.app U
      ((universalSheafDerivation J a i).d
        ((resolutionULiftIso.{u, v, w, w'} J a i).inv.hom.app U x).down))) = _
    refine congrArg (fun y => h.val.app U (ULift.up y)) (hD.trans ?_)
    exact congrArg (fun y => (universalSheafDerivation J a j).d (ULift.down y)) hρ.symm

/-- **Lifting the universe of the sections commutes with the cotangent complex.** For a
homomorphism `a : A ⟶ B` of sheaves of commutative rings, the lift of the cotangent complex
`L_{B/A}` to sections in a larger universe is the cotangent complex `L_{↑B/↑A}` of the lifted
homomorphism. -/
noncomputable def cotangentComplexULiftIso :
    ((liftTargetModules.{u, v, w, w'} J B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex J a) ≅
      cotangentComplex.{u, v, max w w'} J
          ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) :=
  (Stacks.DerivedIndexing.mapExtendIso (liftTargetModules.{u, v, w, w'} J B)
      (ComplexShape.embeddingUpIntLE 0)
      ((AlgebraicTopology.alternatingFaceMapComplex (targetModules J B)).obj
        (cotangentSimplicialModule J a).object)).symm ≪≫
    ((ComplexShape.embeddingUpIntLE 0).extendFunctor _).mapIso
      (eqToIso (Functor.congr_obj (AlgebraicTopology.map_alternatingFaceMapComplex
        (liftTargetModules.{u, v, w, w'} J B)) (cotangentSimplicialModule J a).object)) ≪≫
    (liftCotangentSimplicialModule.{u, v, w, w'} J a).complexIsoCotangentComplex

end Lift

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

universe u

/-- The universe lift of sheaves of `𝒪_X`-modules on the Zariski site of a scheme, to sections
in the next universe, is additive. -/
instance liftTargetModules_zariski_additive (X : Scheme.{u}) :
    (CategoryTheory.Sheaf.liftTargetModules.{u, u, u, u + 1} (Opens.grothendieckTopology ↥X)
      X.zariskiRingedTopos.O).Additive :=
  CategoryTheory.Sheaf.liftTargetModules_additive.{u, u, u, u + 1} _ _

namespace Hom

/-- **The lift of the cotangent complex of a morphism of schemes.** For a morphism of schemes
`f : X ⟶ Y`, raising the universe of the sections of the cotangent complex `L_{X/Y}` of Tag 08T2
by one gives the cotangent complex, on the Zariski site of `X`, of the structure map
`f⁻¹𝒪_Y ⟶ 𝒪_X` with its sections raised to the next universe. -/
noncomputable def cotangentComplexULiftIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((CategoryTheory.Sheaf.liftTargetModules.{u, u, u, u + 1} (Opens.grothendieckTopology ↥X)
        X.zariskiRingedTopos.O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          f.cotangentComplex ≅
      CategoryTheory.Sheaf.cotangentComplex.{u, u, u + 1} (Opens.grothendieckTopology ↥X)
        ((sheafCompose (Opens.grothendieckTopology ↥X) commRingCatULift.{u, u + 1}).map
          (zariskiRingedToposHom f).fSharpInverseImage) :=
  CategoryTheory.Sheaf.cotangentComplexULiftIso.{u, u, u, u + 1} (Opens.grothendieckTopology ↥X)
    (zariskiRingedToposHom f).fSharpInverseImage

end Hom

end AlgebraicGeometry.Scheme

end
