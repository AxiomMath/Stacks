module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAssembly
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalComplement
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentComplementAffine
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ZeroLocusGeometry

/-!
# Formal sections under condition (3)(a), from the completed-complement hypothesis

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and `F` a coherent module on
`U = Spec(A) ∖ V(𝔞)` satisfying conditions (1), (2) and (3) of Stacks 0EIF, with (3) in the
form (3)(a). Granting `Stacks.Algebraization.CompletedComplementIsFormalSections` (Stacks 0BLX),
the comparison map `Γ(U, F) ⟶ lim Γ(U, F/IⁿF)` of Stacks 0EG2 is an isomorphism.

## Main results

* `Stacks.Algebraization.surjective_comparisonAt_of_completedComplementIsFormalSections`: for a
  finite module `M`, every formal section of `M̃|_U` is realized by a section over the
  neighbourhood `U ∖ V(J)`, when the derived completion unit is invertible on `H⁰`.
* `Stacks.Algebraization.isIso_comparisonMap_of_completedComplementIsFormalSections`: the
  comparison map of `M̃|_U` is then an isomorphism.
* `Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_of_eq_top`: for
  `𝔞 = A`, the ideal `A` itself makes the derived completion unit invertible on `H⁰`.
* `Stacks.Algebraization.isIso_comparisonMap_of_serreOne_of_completedComplementIsFormalSections`:
  the comparison map of a coherent `F` satisfying conditions (1), (2) and (3)(a) is an
  isomorphism.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- If `β.hom ≫ f = q ≫ r` and `α.hom ≫ q = s`, then `(α ≪≫ β).hom ≫ f = s ≫ r`. -/
private theorem trans_hom_comp_comp {C : Type*} [Category C] {X Y Z W V : C}
    (α : X ≅ Y) (β : Y ≅ Z) (f : Z ⟶ W) (q : Y ⟶ V) (r : V ⟶ W) (s : X ⟶ V)
    (hβ : β.hom ≫ f = q ≫ r) (hα : α.hom ≫ q = s) :
    (α ≪≫ β).hom ≫ f = s ≫ r := by
  rw [Iso.trans_hom, Category.assoc, hβ, ← Category.assoc, hα]

/-- A morphism `g` of abelian groups is surjective if, up to isomorphisms of its source and
target, it is the image in `Ab` of `f ≫ q` for an isomorphism `f` and an epimorphism `q` of
`R`-modules. -/
private theorem surjective_of_isIso_square_of_epi {R : Type u} [Ring R]
    {X Y Z : ModuleCat.{u} R} (f : X ⟶ Y) (q : Y ⟶ Z) [IsIso f] (hq : Epi q)
    {X' Y' : Ab.{u}} (g : X' ⟶ Y')
    (uu : (forget₂ (ModuleCat R) Ab.{u}).obj X ≅ X')
    (vv : (forget₂ (ModuleCat R) Ab.{u}).obj Z ≅ Y')
    (hcomm : (forget₂ (ModuleCat R) Ab.{u}).map (f ≫ q) ≫ vv.hom = uu.hom ≫ g) :
    Function.Surjective (ConcreteCategory.hom g) :=
  surjective_of_isIso_square _ g uu vv hcomm
    ((ModuleCat.epi_iff_surjective (f ≫ q)).mp (epi_comp f q))

section Milnor

variable (S : AlgebraizationSituation.{u}) (J : Ideal S.A) (hJa : J ≤ S.a)
  (M : ModuleCat.{u} S.A) [Module.Finite S.A M]
  (D : LocalizationTriangleData.{u, u} S.A J J.fg_of_isNoetherianRing)
  (hV : PrimeSpectrum.zeroLocus (J : Set S.A) ∩ PrimeSpectrum.zeroLocus (S.I : Set S.A) =
    PrimeSpectrum.zeroLocus (S.a : Set S.A) ∩ PrimeSpectrum.zeroLocus (S.I : Set S.A))

/-- The comparison from `Ab`-valued formal sections to the limit of the tower of degree-zero
cohomology, transported along the tower comparison. -/
public def assemblyLimitIso :
    (forget₂ (ModuleCat S.A) Ab.{u}).obj
        (limit ((idealPowerQuotientTower.{u, u} S.I M ⋙ D.complement) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) 0)) ≅
      limit (formalSections S.A S.I S.a ((restrictedTildeFunctor S).obj M)) :=
  preservesLimitIso (forget₂ (ModuleCat S.A) Ab.{u})
      ((idealPowerQuotientTower.{u, u} S.I M ⋙ D.complement) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) 0) ≪≫
    HasLimit.isoOfNatIso (assemblyTowerIso S J hJa M D hV)

omit [Module.Finite S.A M] in
/-- The components of `Stacks.Algebraization.assemblyLimitIso`: the limit projection of the tower
of degree-zero cohomology, read in `Ab`, then the tower comparison. -/
public theorem assemblyLimitIso_hom_comp_π (n : ℕ) :
    (assemblyLimitIso S J hJa M D hV).hom ≫
        limit.π (formalSections S.A S.I S.a ((restrictedTildeFunctor S).obj M)) (op n) =
      (forget₂ (ModuleCat S.A) Ab.{u}).map
          (limit.π ((idealPowerQuotientTower.{u, u} S.I M ⋙ D.complement) ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) 0) (op n)) ≫
        (assemblyTowerIso S J hJa M D hV).hom.app (op n) :=
  trans_hom_comp_comp _ _ _ _ _ _
    (HasLimit.isoOfNatIso_hom_π (assemblyTowerIso S J hJa M D hV) (op n))
    (preservesLimitIso_hom_π (forget₂ (ModuleCat S.A) Ab.{u})
      ((idealPowerQuotientTower.{u, u} S.I M ⋙ D.complement) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) 0) (op n))

omit [Module.Finite S.A M] in
/-- The composite of the comparison at the neighbourhood `U ∖ V(J)` with a limit projection is
the corresponding leg of `Stacks.Algebraization.formalSectionsCone`. -/
private theorem comparisonAt_comp_π (n : ℕᵒᵖ) :
    comparisonAt S.A S.I S.a ((restrictedTildeFunctor S).obj M)
          (opensOffVanishingNearVanishing S J hV) ≫
        limit.π (formalSections S.A S.I S.a ((restrictedTildeFunctor S).obj M)) n =
      (formalSectionsCone S.A S.I S.a ((restrictedTildeFunctor S).obj M)
        (opensOffVanishingNearVanishing S J hV)).π.app n :=
  limit.lift_π _ _

include hJa in
/-- **The surjection onto the formal sections.** Granting Stacks 0BLX in the shape
`Stacks.Algebraization.CompletedComplementIsFormalSections`, and granting that the derived
`I`-adic completion unit is invertible on `H⁰` of the derived sections of `M̃` on
`V = Spec(A) ∖ V(J)`, every formal section of `M̃|_U` on all of `U` is realized by a section over
the single neighbourhood `U ∖ V(J)`. -/
public theorem surjective_comparisonAt_of_completedComplementIsFormalSections
    (h0BLX : CompletedComplementIsFormalSections.{u})
    (hunit : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) 0).map
      ((adicCompletionUnit S.A S.I S.I.fg_of_isNoetherianRing).app
        (D.complement.obj M)))) :
    Function.Surjective (ConcreteCategory.hom
      (comparisonAt S.A S.I S.a ((restrictedTildeFunctor S).obj M)
        (opensOffVanishingNearVanishing S J hV))) := by
  obtain ⟨hprod, p, hlim, hnorm⟩ := h0BLX S.A S.I J M D
  have := hprod
  obtain ⟨b, hb, e, i, w, he, hi, hse⟩ :=
    DerivedCategory.exists_milnor_shortExact_of_isDerivedLimitWithProjections
      (A := ModuleCat.{u} S.A)
      (idealPowerQuotientTower.{u, u} S.I M ⋙ D.complement) p hlim 0
  refine surjective_of_isIso_square_of_epi
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) 0).map
      ((adicCompletionUnit S.A S.I S.I.fg_of_isNoetherianRing).app (D.complement.obj M)))
    _ hse.epi_g _ (assemblySectionsIso S J hJa M D) (assemblyLimitIso S J hJa M D hV) ?_
  refine limit.hom_ext fun ⟨n⟩ => ?_
  rw [Category.assoc, Category.assoc, assemblyLimitIso_hom_comp_π, comparisonAt_comp_π,
    ← Category.assoc, ← (forget₂ (ModuleCat S.A) Ab.{u}).map_comp, Category.assoc,
    DerivedCategory.derivedLimitHomologyToLimit_comp_limit_π,
    ← (DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) 0).map_comp, hnorm n]
  exact (assemblySectionsIso_hom_comp_formalSectionsCone_π S J hJa M D hV (op n)).symm

include hJa hV in
/-- **The comparison map of Stacks 0EG2 is an isomorphism**, for the sheaf `M̃|_U` of a finite
module, granting Stacks 0BLX in the shape
`Stacks.Algebraization.CompletedComplementIsFormalSections` and granting that the derived
`I`-adic completion unit is invertible on `H⁰` of the derived sections on `V = Spec(A) \ V(J)`. -/
public theorem isIso_comparisonMap_of_completedComplementIsFormalSections
    (h0BLX : CompletedComplementIsFormalSections.{u})
    (hunit : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) 0).map
      ((adicCompletionUnit S.A S.I S.I.fg_of_isNoetherianRing).app
        (D.complement.obj M)))) :
    IsIso (comparisonMap S.A S.I S.a ((restrictedTildeFunctor S).obj M)) := by
  have hc : ((restrictedTildeFunctor S).obj M).IsCoherent :=
    complementTilde_eq_restrictedTildeFunctor_obj S M ▸
      Stacks.LocalCohomology.isCoherent_complementTilde S.A S.a M
  refine (@isIso_comparisonMap_iff_realized S.A _ S.I S.a
    ((restrictedTildeFunctor S).obj M) _ hc).2 fun s => ?_
  obtain ⟨t, ht⟩ :=
    surjective_comparisonAt_of_completedComplementIsFormalSections S J hJa M D hV h0BLX hunit s
  exact ⟨opensOffVanishingNearVanishing S J hV, t, ht⟩

end Milnor

/-! ### The degenerate case `𝔞 = A`

For the ideal `A` itself, `V(A) = ∅`, so the localization triangle gives `RΓ(V, M̃) = M`, on
which the completion unit is invertible when `A` is `I`-adically complete and `M` is finite. -/

section Degenerate

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- **For `J = A` the derived sections on `V = Spec(A) ∖ V(J)` are `M` itself**: the restriction
map of the localization triangle is an isomorphism. -/
public theorem isIso_restriction_app_top
    (M : ModuleCat.{u} A)
    (D : LocalizationTriangleData.{u, u} A ⊤ (⊤ : Ideal A).fg_of_isNoetherianRing) :
    IsIso (D.restriction.app M) :=
  (CategoryTheory.Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ (D.distinguished M)).1
    ((DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun i =>
      isZero_localCohomologyModule_of_zeroLocus_empty A ⊤
        (⊤ : Ideal A).fg_of_isNoetherianRing
        (PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr rfl) M i)

/-- **The completion unit is invertible on `H⁰` of an object isomorphic to a finite module**, for
`A` complete with respect to `I`. -/
public theorem isIso_homology_completionUnit_of_isIso_single [IsAdicComplete I A]
    (M : ModuleCat.{u} A) [Module.Finite A M]
    {X : DerivedCategory (ModuleCat.{u} A)}
    (r : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M ⟶ X) [IsIso r] :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app X)) := by
  have hnat := (adicCompletionUnit A I I.fg_of_isNoetherianRing).naturality r
  have heq : (adicCompletionUnit A I I.fg_of_isNoetherianRing).app X =
      inv r ≫ ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫
        (adicCompletionFunctor A I I.fg_of_isNoetherianRing).map r) := by
    rw [← hnat, ← Category.assoc, Functor.id_map, IsIso.inv_hom_id, Category.id_comp]
  rw [heq, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **The degenerate case `𝔞 = A`.** If `A` is `I`-adically complete and `M` is finite, there is
an ideal `J₀ ⊆ 𝔞` with `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` such that the unit of derived `I`-adic
completion is invertible on `H⁰` of the derived sections of `M̃` on `Spec(A) ∖ V(J₀)`, namely
`J₀ = A`. -/
public theorem exists_ideal_isIso_homology_zero_completionUnit_of_eq_top (a : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] (hcomplete : IsAdicComplete I A) (ha : a = ⊤) :
    ∃ J₀ : Ideal A, J₀ ≤ a ∧
      ∃ _hV : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A),
        ∀ D : LocalizationTriangleData.{u, u} A J₀ J₀.fg_of_isNoetherianRing,
          IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
              (D.complement.obj M))) := by
  have := hcomplete
  refine ⟨⊤, ha.ge, by rw [ha], fun D => ?_⟩
  have := isIso_restriction_app_top M D
  exact isIso_homology_completionUnit_of_isIso_single I M (D.restriction.app M)

end Degenerate

/-! ### The comparison map of `complementTilde` -/

section Assembly

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I a : Ideal A} (hle : I ≤ a)
  (M : ModuleCat.{u} A) [Module.Finite A M] {J : Ideal A} (hJa : J ≤ a)
  (D : LocalizationTriangleData.{u, u} A J J.fg_of_isNoetherianRing)
  (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
    PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))

include hle hJa hV in
/-- The comparison map of `Stacks.LocalCohomology.complementTilde A 𝔞 M` is an isomorphism,
granting `Stacks.Algebraization.CompletedComplementIsFormalSections` and that the derived
`I`-adic completion unit is invertible on `H⁰` of the derived sections on `Spec(A) ∖ V(J)`. -/
public theorem isIso_comparisonMap_complementTilde_of_completedComplementIsFormalSections
    (h0BLX : CompletedComplementIsFormalSections.{u})
    (hunit : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app (D.complement.obj M)))) :
    IsIso (comparisonMap A I a
      (complementTilde A a M : (complementZeroLocus A a : Scheme).Modules)) := by
  rw [complementTilde_eq_restrictedTildeFunctor_obj
    (⟨A, I, a, hle⟩ : AlgebraizationSituation.{u}) M]
  exact isIso_comparisonMap_of_completedComplementIsFormalSections
    (⟨A, I, a, hle⟩ : AlgebraizationSituation.{u}) J hJa M D hV h0BLX hunit

end Assembly

/-- **Stacks 0EIF under its condition (3)(a), granting Stacks 0BLX.** For ideals `I ⊆ 𝔞` of a
Noetherian ring and a coherent module `F` on `U = Spec(A) ∖ V(𝔞)` satisfying conditions (1), (2)
and (3) of Stacks 0EIF, with (3) in the form (3)(a), the comparison map is an isomorphism,
granting `Stacks.Algebraization.CompletedComplementIsFormalSections`. -/
public theorem isIso_comparisonMap_of_serreOne_of_completedComplementIsFormalSections
    (h0BLX : CompletedComplementIsFormalSections.{u})
    {B : Type u} [CommRing B] [IsNoetherianRing B] {I a : Ideal B} (hIa : I ≤ a)
    (G : (complementZeroLocus B a : Scheme).Modules) (hG : G.IsCoherent)
    (hFSH : FormalSectionsHypotheses B I a G) (hS : IsSerreOneOffVanishing B I a G) :
    IsIso (comparisonMap B I a G) := by
  have := hG
  obtain ⟨⟨N, hN, ⟨e⟩⟩, -⟩ :=
    Stacks.LocalCohomology.coherent_complement_affine B a a.fg_of_isNoetherianRing G
  have := hN
  have hex : ∃ J₀ : Ideal B, J₀ ≤ a ∧
      ∃ _hV : PrimeSpectrum.zeroLocus (J₀ : Set B) ∩ PrimeSpectrum.zeroLocus (I : Set B) =
        PrimeSpectrum.zeroLocus (a : Set B) ∩ PrimeSpectrum.zeroLocus (I : Set B),
        ∀ D : LocalizationTriangleData.{u, u} B J₀ J₀.fg_of_isNoetherianRing,
          IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).map
            ((adicCompletionUnit B I I.fg_of_isNoetherianRing).app
              (D.complement.obj N))) := by
    by_cases hane : a = ⊤
    · exact exists_ideal_isIso_homology_zero_completionUnit_of_eq_top I a N
        hFSH.adicComplete hane
    · exact exists_ideal_isIso_homology_zero_completionUnit_of_serreOne I a hG e hIa hFSH hS
        hane
  obtain ⟨J₀, hJ₀, hV, hunit⟩ := hex
  obtain ⟨D⟩ := Stacks.LocalCohomology.nonempty_localizationTriangleData.{u, u} B J₀
    J₀.fg_of_isNoetherianRing
  exact isIso_comparisonMap_of_iso B I a e.symm
    (isIso_comparisonMap_complementTilde_of_completedComplementIsFormalSections hIa N hJ₀ D
      hV h0BLX (hunit D))

end Stacks.Algebraization

end
