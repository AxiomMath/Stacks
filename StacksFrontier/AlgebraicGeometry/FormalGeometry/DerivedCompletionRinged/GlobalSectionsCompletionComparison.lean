module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.UnboundedGlobalSections
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompletionIdempotent
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompleteGlobalSection
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechSliceRestriction
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.FiniteTypeGlobalSections
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree

/-!
# Derived global sections commute with derived completion

Let `(𝒞, 𝒪)` be a ringed site, `A` a ring with `ρ : A ⟶ Γ(𝒞, 𝒪)`, `I ⊂ A` a finitely generated
ideal and `𝓘 = I𝒪` the ideal sheaf it generates. For every `K ∈ D(𝒪)` this file constructs the
canonical map
```
RΓ(𝒞, K)^∧ ⟶ RΓ(𝒞, K^∧)      in D(A)
```
and proves that it is an isomorphism. On the left `(-)^∧` is derived `I`-adic completion on
`D(A)` (`Stacks.Algebraization.adicCompletionFunctor`), on the right it is the reflector of
[Stacks, Tag 099F] along `𝓘` (`AlgebraicGeometry.RingedSite.derivedCompletion`), and `RΓ` is
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsOverUnbounded` throughout. The map is the one
the universal property of derived completion on `D(A)` produces from `RΓ(𝒞, K ⟶ K^∧)`. This is
the identity `RΓ(𝒞, ℱ)^∧ = RΓ(𝒞, ℱ^∧)` of [Stacks, Tag 0BLX], as the proof of
[Stacks, Tag 0EIF] uses it, with the map named; the case of the punctured spectrum
`U = Spec(A) ∖ V(𝔞)` of a Noetherian ring is recorded at the end.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsCompletionComparison`: the comparison map.
* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsCompletionIso`: it, as an isomorphism.
* `AlgebraicGeometry.RingedSite.idealSheafOfIdeal`: the ideal sheaf `I𝒪`.
* `Stacks.Algebraization.complementBaseRingHom`: `A ⟶ Γ(U, 𝒪_U)` for `U = Spec(A) ∖ V(𝔞)`, as
  used to make `RΓ(U, -)` take values in `D(A)`.

## Main results

* `AlgebraicGeometry.RingedSite.adicCompletionUnit_comp_derivedGlobalSectionsCompletionComparison`:
  the characterizing property of the comparison map.
* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsCompletionComparison_naturality`.
* `AlgebraicGeometry.RingedSite.isIso_derivedGlobalSectionsCompletionComparison`: **the comparison
  map is an isomorphism**, for any ringed site, any finitely generated `I` and any `K`.
* `Stacks.Algebraization.isIso_complementGlobalSectionsCompletionComparison`: the same for a sheaf
  of modules `F` on `U = Spec(A) ∖ V(𝔞)`, `A` Noetherian and `I` arbitrary.

## The argument

The source deduces the identity from [Stacks, Tag 0A0G] at the morphism `(𝒞, 𝒪) ⟶ (pt, A)`. The
argument here uses only the Čech description of the completion on `D(𝒪)` and two formal
properties of `RΓ`: it is triangulated and it carries multiplication by `ρ c` to multiplication
by `c` (`derivedGlobalSectionsOverUnbounded_map_baseSmulCenter`). Write `I = (a_1, …, a_r)`,
`f_i = ρ a_i` and `Č = Č(f)` for the extended alternating Čech complex, so that
`K^∧ = R𝑆heafHom_𝒪(Č, K)` with unit induced by the augmentation `Č ⟶ 𝒪`
(`CompletionIdempotent.lean`).

1. Both `RΓ(𝒞, K^∧)` and `RΓ(𝒞, K)^∧` are derived `I`-complete
   (`isDerivedComplete_map_of_isDerivedComplete`), so the comparison map exists and it suffices
   that precomposition with `RΓ(K ⟶ K^∧)` be bijective onto maps into every derived `I`-complete
   object of `D(A)` (`isIso_of_adicCompletionUnit_comp`).
2. By the stupid filtration of `Č` that reduces to: `RΓ(R𝑆heafHom_𝒪(Č^{≥1}, K))` admits no
   non-zero map to a derived `I`-complete object (`isCompletionAcyclicHom_stupidTruncGE_one`).
   The terms of `Č^{≥1}` are finite products of the `𝒪_{f_S}` with `S ≠ ∅`, and the class of
   objects `B` with this property for `R𝑆heafHom_𝒪(B, K)` is closed under extensions, shifts
   and finite products, so it is enough to treat `B = 𝒪_{f_S}`.
3. For `j ∈ S` multiplication by `f_j` is invertible on `𝒪_{f_S}`, hence on
   `R𝑆heafHom_𝒪(𝒪_{f_S}, K)`, hence multiplication by `a_j ∈ I` is invertible on
   `RΓ(R𝑆heafHom_𝒪(𝒪_{f_S}, K))`; and a map from an object on which an element of `I` acts
   invertibly to a derived `I`-complete object vanishes
   (`IsDerivedCompleteAt.eq_zero_of_isIso_smul`).

No nilpotence, boundedness or finiteness hypothesis enters, and no `@[stacks]` attribute is
attached: [Stacks, Tag 0BLX] also asserts two spectral sequences, and its registrations belong
with them.

## References

* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped IsMulCommutative

universe u

section Milnor

variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
  [HasProductsOfShape ℕ C]

/-- **A map into an object derived complete at `b` from an object on which `b` acts invertibly
vanishes.** If `u` is the inverse of `b` on `N`, the maps `uⁿ ≫ g` form a family `N ⟶ ∏ M`
killed by `1 - b · shift`, which is invertible on `∏ M`; its zeroth component is `g`. -/
theorem IsDerivedCompleteAt.eq_zero_of_isIso_smul {N M : C} {b : R} [IsIso (b • 𝟙 N)]
    (hM : IsDerivedCompleteAt M b) (g : N ⟶ M) : g = 0 := by
  let v : N ⟶ N := inv (b • 𝟙 N)
  let p : ℕ → (N ⟶ N) := fun n ↦ Nat.rec (𝟙 N) (fun _ q ↦ v ≫ q) n
  have hv : b • v = 𝟙 N := by
    rw [← Category.id_comp v, ← Linear.smul_comp, IsIso.hom_inv_id]
  let Φ : N ⟶ ∏ᶜ fun _ : ℕ ↦ M := Pi.lift fun n ↦ p n ≫ g
  have hΦ : Φ ≫ oneSubSmulShift M b = 0 := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul,
      Pi.lift_comp_π, Pi.lift_comp_π, zero_comp]
    change p n ≫ g - b • ((v ≫ p n) ≫ g) = 0
    rw [Category.assoc, ← Linear.smul_comp, hv, Category.id_comp, sub_self]
  rw [isDerivedCompleteAt_iff_isIso] at hM
  have h0 : Φ = 0 := by
    rw [← cancel_mono (oneSubSmulShift M b), hΦ, zero_comp]
  simpa [Φ, p] using congrArg (· ≫ Pi.π (fun _ : ℕ ↦ M) 0) h0

end Milnor

namespace Stacks.Algebraization

section Orthogonal

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- If the third vertex of a distinguished triangle of `D(A)` admits no non-zero map to a derived
`I`-complete object, then precomposition with its first map is a bijection onto maps into every
derived `I`-complete object. -/
theorem bijective_precomp_mor₁_of_leftOrthogonal_derivedComplete
    (T : Triangle (DerivedCategory (ModuleCat.{u} A))) (hT : T ∈ distTriang _)
    (h₃ : (Dualizing.derivedCompleteProperty A I).leftOrthogonal T.obj₃)
    {E : DerivedCategory (ModuleCat.{u} A)} (hE : IsDerivedComplete I E) :
    Function.Bijective (fun g : T.obj₂ ⟶ E ↦ T.mor₁ ≫ g) := by
  refine ⟨fun g g' hgg' ↦ ?_, fun g ↦ ?_⟩
  · have h0 : T.mor₁ ≫ (g - g') = 0 := by
      rwa [Preadditive.comp_sub, sub_eq_zero]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ T hT (g - g') h0
    rwa [h₃ k hE, comp_zero, sub_eq_zero] at hk
  · have h₃' : (Dualizing.derivedCompleteProperty A I).leftOrthogonal T.invRotate.obj₁ :=
      ((Dualizing.derivedCompleteProperty A I).leftOrthogonal.prop_shift_iff (-1 : ℤ) _).1
        ((Dualizing.derivedCompleteProperty A I).leftOrthogonal.le_shift (-1 : ℤ) _ h₃)
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ T.invRotate (inv_rot_of_distTriang T hT) g
      (h₃' _ hE)
    exact ⟨k, hk.symm⟩

/-- An object which is a finite product of objects admitting no non-zero map to a derived
`I`-complete object admits none either. -/
theorem leftOrthogonal_derivedComplete_pi {ι : Type*} [Finite ι]
    (Y : ι → DerivedCategory (ModuleCat.{u} A))
    (hY : ∀ i, (Dualizing.derivedCompleteProperty A I).leftOrthogonal (Y i)) :
    (Dualizing.derivedCompleteProperty A I).leftOrthogonal (∏ᶜ Y) := by
  cases nonempty_fintype ι
  intro E g hE
  rw [← cancel_epi (biproduct.isoProduct Y).hom, comp_zero]
  exact biproduct.hom_ext' _ _ fun i ↦ (hY i _ hE).trans comp_zero.symm

end Orthogonal

end Stacks.Algebraization

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard linearCatCenterRingSheaf

section Smul

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]

/-- A compatible family of local sections of the structure sheaf, read as a global section. -/
def globalSectionOfSectionsSubring
    (s : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}) :=
  (Presheaf.globalSectionsEquivSections _).symm ⟨s.1, fun g ↦ s.2 g⟩

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The value of `globalSectionOfSectionsSubring s` over `U` is `s` at `U`. -/
@[simp]
theorem globalSectionVal_globalSectionOfSectionsSubring
    (s : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) (U : X.Cᵒᵖ) :
    globalSectionVal (globalSectionOfSectionsSubring X s) U = s.1 U := by
  unfold globalSectionVal globalSectionOfSectionsSubring
  rw [Equiv.apply_symm_apply]

variable (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)

/-- Multiplication by the global section `ρ c`, as a central endomorphism of the category of
sheaves of `𝒪`-modules. -/
abbrev baseSmulCenter (c : A) :
    CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (awayFamily X (globalSectionOfSectionsSubring X (ρ c)))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- `A`-linear global sections carry multiplication by the global section `ρ c` to
multiplication by `c`: the `A`-action on `Γ(𝒞, P) = Hom_𝒪(𝒪, P)` is precomposition with
multiplication by `ρ c` on `𝒪`, and multiplication by a global section is natural. -/
theorem moduleGlobalSectionsOver_map_baseSmulCenter (c : A)
    (P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (moduleGlobalSectionsOver X A ρ).map (baseSmulCenter X A ρ c • 𝟙 P) =
      c • 𝟙 ((moduleGlobalSectionsOver X A ρ).obj P) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hfam : awayFamily X (globalSectionOfSectionsSubring X (ρ c)) = ⟨(ρ c).1, (ρ c).2⟩ := by
    ext U
    exact globalSectionVal_globalSectionOfSectionsSubring X (ρ c) U
  change x ≫ ((baseSmulCenter X A ρ c).app P ≫ 𝟙 P) =
    CatCenter.app (Stacks.SheafOfModules.globalSectionToEnd
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟨(ρ c).1, (ρ c).2⟩) _ ≫ x
  rw [Category.comp_id, baseSmulCenter, hfam]
  exact CatCenter.naturality (Stacks.SheafOfModules.globalSectionToEnd
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟨(ρ c).1, (ρ c).2⟩) x

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **Derived global sections carry multiplication by `ρ c` to multiplication by `c`.** -/
theorem derivedGlobalSectionsOverUnbounded_map_baseSmulCenter (c : A)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedGlobalSectionsOverUnbounded X A ρ).map (baseSmulCenter X A ρ c • 𝟙 K) =
      c • 𝟙 ((derivedGlobalSectionsOverUnbounded X A ρ).obj K) := by
  refine Stacks.SemilinearFunctor.map_smul_id_rightDerived
    (derivedGlobalSectionsOverUnbounded X A ρ) (derivedGlobalSectionsOverUnboundedUnit X A ρ)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) (baseSmulCenter X A ρ c) c (fun M ↦ ?_) K
  refine Stacks.SemilinearFunctor.map_smul_id_comp
    ((moduleGlobalSectionsOver X A ρ).mapHomotopyCategory (ComplexShape.up ℤ))
    DerivedCategory.Qh (baseSmulCenter X A ρ c) c (fun N ↦ ?_) M
  exact Stacks.SemilinearFunctor.map_smul_id_mapHomotopyCategory
    (moduleGlobalSectionsOver X A ρ) (baseSmulCenter X A ρ c) c
    (moduleGlobalSectionsOver_map_baseSmulCenter X A ρ c) (ComplexShape.up ℤ) N

end Smul

section Engine

attribute [local instance] hasProductsOfShape_nat_derivedCategory

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  {r : ℕ} (a : Fin r → A)

/-- The global sections `ρ a_1, …, ρ a_r` of `𝒪`. -/
abbrev baseGenerators : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}) :=
  fun i ↦ globalSectionOfSectionsSubring X (ρ (a i))

variable (G : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (ModuleCat.{u} A)) [G.CommShift ℤ] [G.IsTriangulated]
  (hG : ∀ (c : A) (L : DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
    G.map (baseSmulCenter X A ρ c • 𝟙 L) = c • 𝟙 (G.obj L))
  (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The property of an object `B` of `D(𝒪)` that `G(R𝑆heafHom_𝒪(B, K))` admits no non-zero map
to an object of `D(A)` derived complete along `(a_1, …, a_r)`. -/
def IsCompletionAcyclicHom
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    Prop :=
  (Dualizing.derivedCompleteProperty A (Ideal.span (Set.range a))).leftOrthogonal
    (G.obj (((derivedSheafHomBifunctor X).flip.obj K).obj (op B)))

variable {X A ρ a G K}

omit [HasWeakSheafify X.J CommRingCat.{u}] [G.CommShift ℤ] [G.IsTriangulated] in
/-- The property is invariant under isomorphism. -/
theorem IsCompletionAcyclicHom.of_iso
    {B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : B ≅ B') (h : IsCompletionAcyclicHom X A a G K B) :
    IsCompletionAcyclicHom X A a G K B' :=
  ObjectProperty.prop_of_iso
    (Dualizing.derivedCompleteProperty A (Ideal.span (Set.range a))).leftOrthogonal
    (G.mapIso (((derivedSheafHomBifunctor X).flip.obj K).mapIso e.symm.op)) h

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- A zero object has the property. -/
theorem IsCompletionAcyclicHom.of_isZero
    {B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hB : IsZero B) : IsCompletionAcyclicHom X A a G K B := by
  intro E g _
  exact ((G.map_isZero (((derivedSheafHomBifunctor X).flip.obj K).map_isZero hB.op))).eq_of_src _ _

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- `G(R𝑆heafHom_𝒪(-, K))` carries a distinguished triangle of `D(𝒪)` to a distinguished
triangle of `D(A)`, with the order of the vertices reversed ([Stacks, Tag 08JC]). -/
theorem exists_distinguished_map_derivedSheafHom
    (T : Triangle (DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distTriang _) :
    ∃ δ, G.mapTriangle.obj (Triangle.mk (((derivedSheafHomBifunctor X).flip.obj K).map T.mor₂.op)
        (((derivedSheafHomBifunctor X).flip.obj K).map T.mor₁.op) δ) ∈ distTriang _ := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom X K T hT
  exact ⟨δ, G.map_distinguished _ hδ⟩

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The property is closed under extensions. -/
theorem IsCompletionAcyclicHom.ext₂
    (T : Triangle (DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distTriang _) (h₁ : IsCompletionAcyclicHom X A a G K T.obj₁)
    (h₃ : IsCompletionAcyclicHom X A a G K T.obj₃) :
    IsCompletionAcyclicHom X A a G K T.obj₂ := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_map_derivedSheafHom (G := G) (K := K) T hT
  exact (Dualizing.derivedCompleteProperty A
    (Ideal.span (Set.range a))).leftOrthogonal.ext_of_isTriangulatedClosed₂ _ hδ h₃ h₁

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The property passes from the second and third vertices of a distinguished triangle to the
first. -/
theorem IsCompletionAcyclicHom.ext₁
    (T : Triangle (DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distTriang _) (h₂ : IsCompletionAcyclicHom X A a G K T.obj₂)
    (h₃ : IsCompletionAcyclicHom X A a G K T.obj₃) :
    IsCompletionAcyclicHom X A a G K T.obj₁ := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_map_derivedSheafHom (G := G) (K := K) T hT
  exact (Dualizing.derivedCompleteProperty A
    (Ideal.span (Set.range a))).leftOrthogonal.ext_of_isTriangulatedClosed₃ _ hδ h₃ h₂

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The property descends along the shift by one. -/
theorem IsCompletionAcyclicHom.of_shift_one
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : IsCompletionAcyclicHom X A a G K (B⟦(1 : ℤ)⟧)) :
    IsCompletionAcyclicHom X A a G K B :=
  IsCompletionAcyclicHom.ext₁ _ (rot_of_distTriang _ (contractible_distinguished B))
    (IsCompletionAcyclicHom.of_isZero (isZero_zero _)) h

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The property descends along the shift by a natural number. -/
theorem IsCompletionAcyclicHom.of_shift_nat
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℕ) (h : IsCompletionAcyclicHom X A a G K (B⟦(n : ℤ)⟧)) :
    IsCompletionAcyclicHom X A a G K B := by
  induction n generalizing B with
  | zero =>
      rw [Nat.cast_zero] at h
      exact h.of_iso ((shiftFunctorZero _ ℤ).app B)
  | succ n ih =>
      rw [Nat.cast_succ] at h
      exact ih B (.of_shift_one _
        (h.of_iso ((shiftFunctorAdd' _ (n : ℤ) 1 ((n : ℤ) + 1) rfl).app B)))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The degree-zero single functor to `D(𝒪)` commutes with the action of the centre. -/
private theorem singleFunctor_zero_map_smul_id
    (c : CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map (c • 𝟙 M) =
      c • 𝟙 ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M) := by
  have h1 : (CochainComplex.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map (c • 𝟙 M) =
      c • 𝟙 ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M) :=
    (Functor.linear_iff (CatCenter (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (CochainComplex.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0)).mp
      inferInstance M c
  change DerivedCategory.Q.map ((CochainComplex.singleFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map (c • 𝟙 M)) = _
  rw [h1, DerivedCategory.Q.map_smul, DerivedCategory.Q.map_id]
  rfl

omit [G.CommShift ℤ] [G.IsTriangulated] in
include hG in
/-- **The base case.** For a non-empty `S`, some `a_j` with `j ∈ S` acts invertibly on
`G(R𝑆heafHom_𝒪(𝒪_{f_S}, K))`, because `ρ a_j` is invertible on `𝒪_{f_S}`; so that object admits
no non-zero map to an object derived complete along `(a_1, …, a_r)`. -/
theorem isCompletionAcyclicHom_singleFunctor_zero_awayModule (S : Finset (Fin r))
    (hS : S.Nonempty) :
    IsCompletionAcyclicHom X A a G K
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (awayModule X (prodGlobalSection (baseGenerators X A ρ a) S))) := by
  obtain ⟨j, hj⟩ := hS
  set M := awayModule X (prodGlobalSection (baseGenerators X A ρ a) S) with hMdef
  set c := baseSmulCenter X A ρ (a j) with hc
  have hM : IsIso (c.app M) := by
    have h := isIso_awaySmul_pow_of_bijective X (baseGenerators X A ρ a j) M (fun U n ↦ by
      have hb := bijective_smul_awayModule_prodGlobalSection_of_subset X
        (baseGenerators X A ρ a) (Finset.singleton_subset_iff.2 hj) U n
      rwa [prodGlobalSection_singleton] at hb) 1
    rwa [pow_one] at h
  have h1 : IsIso (c • 𝟙 ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M)) := by
    rw [← singleFunctor_zero_map_smul_id c M]
    have : IsIso (c • 𝟙 M) := by
      change IsIso (c.app M ≫ 𝟙 M)
      infer_instance
    infer_instance
  have h2 : IsIso (c • 𝟙 (((derivedSheafHomBifunctor X).flip.obj K).obj
      (op ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M)))) := by
    have e := derivedSheafHom_map_globalSectionToEnd_source X
      (awayFamily X (globalSectionOfSectionsSubring X (ρ (a j))))
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M) K
    change IsIso (c • 𝟙 (((derivedSheafHomBifunctor X).obj (op ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M))).obj K))
    rw [hc, ← e]
    infer_instance
  have h3 : IsIso (a j • 𝟙 (G.obj (((derivedSheafHomBifunctor X).flip.obj K).obj
      (op ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M))))) := by
    rw [← hG]
    infer_instance
  intro E g hE
  exact IsDerivedCompleteAt.eq_zero_of_isIso_smul (hE (a j) (Ideal.subset_span ⟨j, rfl⟩)) g

include hG in
/-- The base case in an arbitrary non-negative degree. -/
theorem isCompletionAcyclicHom_singleFunctor_awayModule (S : Finset (Fin r))
    (hS : S.Nonempty) {p : ℤ} (hp : 0 ≤ p) :
    IsCompletionAcyclicHom X A a G K
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) p).obj
          (awayModule X (prodGlobalSection (baseGenerators X A ρ a) S))) := by
  refine IsCompletionAcyclicHom.of_shift_nat _ p.toNat ?_
  rw [Int.toNat_of_nonneg hp]
  exact (isCompletionAcyclicHom_singleFunctor_zero_awayModule hG S hS).of_iso
    (((DerivedCategory.singleFunctors
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso p 0 p
        (add_zero p)).app _).symm

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The property is stable under finite products. -/
theorem IsCompletionAcyclicHom.pi {ι : Type} [Finite ι]
    (B : ι → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ i, IsCompletionAcyclicHom X A a G K (B i)) :
    IsCompletionAcyclicHom X A a G K (∏ᶜ B) := by
  cases nonempty_fintype ι
  set H := (derivedSheafHomBifunctor X).flip.obj K with hH
  have e : (op (∏ᶜ B) : (DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ) ≅ ∏ᶜ fun i ↦ op (B i) :=
    ((biproduct.isoCoproduct B).symm ≪≫ biproduct.isoProduct B).op ≪≫
      opCoproductIsoProduct B
  have e₂ : G.obj (H.obj (op (∏ᶜ B))) ≅ ∏ᶜ fun i ↦ G.obj (H.obj (op (B i))) :=
    G.mapIso (H.mapIso e ≪≫ PreservesProduct.iso H fun i ↦ op (B i)) ≪≫
      PreservesProduct.iso G _
  exact ObjectProperty.prop_of_iso
    (Dualizing.derivedCompleteProperty A (Ideal.span (Set.range a))).leftOrthogonal e₂.symm
    (Stacks.Algebraization.leftOrthogonal_derivedComplete_pi _ _ h)

include hG in
/-- **The kernel of the augmentation.** `G(R𝑆heafHom_𝒪(Č(f)^{≥1}, K))` admits no non-zero map to
an object derived complete along `(a_1, …, a_r)`, by induction along the stupid filtration of the
bounded complex `Č(f)`, whose terms in degrees `≥ 1` are products of the `𝒪_{f_S}` with `S`
non-empty. -/
theorem isCompletionAcyclicHom_stupidTruncGE_one :
    IsCompletionAcyclicHom X A a G K (DerivedCategory.Q.obj
      ((extendedAlternatingCech X (baseGenerators X A ρ a)).stupidTrunc
        (ComplexShape.embeddingUpIntGE 1))) := by
  refine Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex_stupidTruncGE
    (IsCompletionAcyclicHom X A a G K) (fun e h ↦ h.of_iso e)
    (fun _ hB ↦ IsCompletionAcyclicHom.of_isZero hB)
    (fun T hT h₁ h₃ ↦ IsCompletionAcyclicHom.ext₂ T hT h₁ h₃)
    (extendedAlternatingCech X (baseGenerators X A ρ a))
    (finite_support_extendedAlternatingCech X _) 1 fun i hi ↦ ?_
  refine IsCompletionAcyclicHom.of_iso
    (PreservesProduct.iso
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i)
      (fun S : AlternatingCech.Idx r i ↦
        awayModule X (prodGlobalSection (baseGenerators X A ρ a) S.1))).symm ?_
  refine IsCompletionAcyclicHom.pi _ fun S ↦ ?_
  refine isCompletionAcyclicHom_singleFunctor_awayModule hG S.1
    (Finset.card_pos.1 ?_) (by omega)
  have := S.2
  omega

/-- Precomposition with `u` is bijective as soon as `u ≫ e₁ = e₂ ≫ v` for isomorphisms `e₁, e₂`
and a `v` precomposition with which is bijective. -/
private theorem bijective_precomp_of_comp_eq {C : Type*} [Category C] {P Q P' Q' E : C}
    (u : P ⟶ Q) (v : P' ⟶ Q') (e₁ : Q ⟶ Q') (e₂ : P ⟶ P') [IsIso e₁] [IsIso e₂]
    (h : u ≫ e₁ = e₂ ≫ v) (hv : Function.Bijective (fun g : Q' ⟶ E ↦ v ≫ g)) :
    Function.Bijective (fun g : Q ⟶ E ↦ u ≫ g) := by
  refine ⟨fun g g' hgg' ↦ ?_, fun k ↦ ?_⟩
  · have hgg'' : v ≫ inv e₁ ≫ g = v ≫ inv e₁ ≫ g' := by
      rwa [← cancel_epi e₂, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id_assoc,
        ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id_assoc]
    simpa using hv.1 hgg''
  · obtain ⟨g, hg⟩ := hv.2 (inv e₂ ≫ k)
    refine ⟨e₁ ≫ g, ?_⟩
    change u ≫ e₁ ≫ g = k
    change v ≫ g = inv e₂ ≫ k at hg
    rw [← Category.assoc, h, Category.assoc, hg, IsIso.hom_inv_id_assoc]

include hG in
/-- **`G` carries the Čech completion map to a map inverted by derived completion on `D(A)`**:
precomposition with `G(K ⟶ R𝑆heafHom_𝒪(Č(f), K))` is a bijection onto maps into any object of
`D(A)` derived complete along `(a_1, …, a_r)`. -/
theorem bijective_precomp_map_completionUnit
    {E : DerivedCategory (ModuleCat.{u} A)}
    (hE : _root_.IsDerivedComplete (Ideal.span (Set.range a)) E) :
    Function.Bijective (fun g : G.obj ((completionFunctor X (baseGenerators X A ρ a)).obj K) ⟶ E ↦
      G.map ((completionUnit X (baseGenerators X A ρ a)).app K) ≫ g) := by
  set f := baseGenerators X A ρ a with hf
  set H := (derivedSheafHomBifunctor X).flip.obj K with hH
  set Č := extendedAlternatingCech X f with hČ
  obtain ⟨δ, hδ⟩ := exists_distinguished_map_derivedSheafHom (G := G) (K := K)
    (StacksDraft.StupidTruncation.stupidTruncGETriangle Č 0)
    (StacksDraft.StupidTruncation.stupidTruncGETriangle_distinguished Č 0)
  have hπ := Stacks.Algebraization.bijective_precomp_mor₁_of_leftOrthogonal_derivedComplete
    (Ideal.span (Set.range a)) _ hδ
    (isCompletionAcyclicHom_stupidTruncGE_one hG) hE
  have hι : IsIso (Č.ιStupidTrunc (ComplexShape.embeddingUpIntGE 0)) :=
    isIso_ιStupidTrunc_extendedAlternatingCech X f
  have hz : IsIso (cechAugmentationZero X f) := isIso_cechAugmentationZero X f
  have hcomp : G.map (H.map (DerivedCategory.Q.map (cechAugmentation X f)).op) ≫
      G.map (H.map (DerivedCategory.Q.map
        (Č.ιStupidTrunc (ComplexShape.embeddingUpIntGE 0))).op) =
      G.map (H.map (DerivedCategory.Q.map ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).map
          (cechAugmentationZero X f))).op) ≫
      G.map (H.map (DerivedCategory.Q.map
        (StacksDraft.StupidTruncation.stupidTruncGEπ Č 0)).op) := by
    rw [← G.map_comp, ← G.map_comp, ← H.map_comp, ← H.map_comp, ← op_comp, ← op_comp,
      ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ιStupidTrunc_comp_cechAugmentation X f]
  have haug := bijective_precomp_of_comp_eq _ _ _ _ hcomp hπ
  rw [completionUnit_app]
  exact bijective_precomp_of_comp_eq _ _ (𝟙 _) (G.map (derivedStructureSheafHomIso X K).inv)
    (by rw [Category.comp_id]; exact G.map_comp _ _) haug

end Engine

section IdealSheaf

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **`I𝒪` for `I = (a_1, …, a_r)` is the ideal sheaf generated by the global sections
`ρ a_1, …, ρ a_r`.** -/
theorem isIdealSheafGeneratedBy_idealOfGlobalSections {r : ℕ} (a : Fin r → A) :
    IsIdealSheafGeneratedBy A (Ideal.span (Set.range a)) X ρ
      (idealOfGlobalSections X (baseGenerators X A ρ a)) := by
  refine ⟨fun c U hc ↦ ?_, fun 𝓙 h𝓙 ↦ ?_⟩
  · refine mem_idealOfGlobalSections_of_mem_span X _ U ?_
    let φ : A →+* (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U :=
      ((Pi.evalRingHom _ U).comp (RingCat.sectionsSubring
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).subtype).comp ρ
    have hmap : Ideal.map φ (Ideal.span (Set.range a)) =
        Ideal.span (Set.range (restrictGlobalSections X (baseGenerators X A ρ a) U)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      congr 2
    rw [← hmap]
    exact Ideal.mem_map_of_mem φ hc
  · refine idealOfGlobalSections_le X _ fun i V ↦ ?_
    rw [globalSectionVal_globalSectionOfSectionsSubring]
    exact h𝓙 (a i) V (Ideal.subset_span ⟨i, rfl⟩)

/-- **[Stacks, Tag 099F] at `I𝒪`, for a finitely generated `I`**: the inclusion of the objects
of `D(𝒪)` derived complete along the ideal sheaf generated by `I` has a left adjoint. -/
theorem isRightAdjoint_ι_isDerivedComplete_of_isIdealSheafGeneratedBy {I : Ideal A}
    (hI : I.FG)
    {𝓘 : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h𝓘 : IsIdealSheafGeneratedBy A I X ρ 𝓘) :
    (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X 𝓘)).IsRightAdjoint := by
  obtain ⟨r, a, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
  exact isRightAdjoint_ι_isDerivedComplete_of_eq_idealOfGlobalSections X
    (baseGenerators X A ρ a) 𝓘
    (eq_of_isIdealSheafGeneratedBy A _ X ρ h𝓘
      (isIdealSheafGeneratedBy_idealOfGlobalSections X A ρ a))

/-- **The ideal sheaf `I𝒪`** generated by an ideal `I` of `A` through `ρ : A ⟶ Γ(𝒞, 𝒪)`: the
smallest sheaf of ideals of `𝒪` containing every restriction of every `ρ a`, `a ∈ I`. -/
def idealSheafOfIdeal (I : Ideal A) :
    SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  SheafOfModules.Submodule.generatedBy
    (F := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (fun p : I × X.Cᵒᵖ ↦ p.2) (fun p ↦ (ρ p.1).1 p.2)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- `idealSheafOfIdeal X A ρ I` is the ideal sheaf `I𝒪` in the sense of
`AlgebraicGeometry.RingedSite.IsIdealSheafGeneratedBy`. -/
theorem isIdealSheafGeneratedBy_idealSheafOfIdeal (I : Ideal A) :
    IsIdealSheafGeneratedBy A I X ρ (idealSheafOfIdeal X A ρ I) :=
  ⟨fun c U hc ↦ SheafOfModules.Submodule.mem_generatedBy
      (F := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (fun p : I × X.Cᵒᵖ ↦ p.2) (fun p ↦ (ρ p.1).1 p.2) (⟨c, hc⟩, U),
    fun _ h𝓙 ↦ SheafOfModules.Submodule.generatedBy_le
      (F := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (fun p : I × X.Cᵒᵖ ↦ p.2) (fun p ↦ (ρ p.1).1 p.2) fun p ↦ h𝓙 p.1 p.2 p.1.2⟩

end IdealSheaf

section Comparison

attribute [local instance] hasProductsOfShape_nat_derivedCategory

variable {X : RingedSite.{u, u, u}} [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A : Type u} [CommRing A]
  {ρ : A →+* RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
  {I : Ideal A} (hI : I.FG)
  {𝓘 : SheafOfModules.Submodule
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  (h𝓘 : IsIdealSheafGeneratedBy A I X ρ 𝓘)
  {G : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (ModuleCat.{u} A)}
  (hG : ∀ (c : A) (L : DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
    G.map (baseSmulCenter X A ρ c • 𝟙 L) = c • 𝟙 (G.obj L))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
include hI h𝓘 hG in
/-- **`G` carries objects derived complete along `I𝒪` to objects derived complete along `I`.** -/
theorem isDerivedComplete_map_of_isDerivedComplete [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hL : IsDerivedComplete.{u, u, u, u} X 𝓘 L) :
    _root_.IsDerivedComplete I (G.obj L) := by
  obtain ⟨r, a, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
  have hi : ∀ i, IsDerivedCompleteAt (G.obj L) (a i) := fun i ↦
    isDerivedCompleteAt_map_of_smul_id G (hG (a i) L)
      (isDerivedCompleteAt_awayFamily_of_isDerivedComplete X L _ 𝓘 (fun U ↦ by
        rw [globalSectionVal_globalSectionOfSectionsSubring]
        exact h𝓘.1 (a i) (op U) (Ideal.subset_span ⟨i, rfl⟩)) hL)
  obtain ⟨J, -, hJ⟩ := exists_isRadical_ideal_isDerivedCompleteAt A (G.obj L)
  exact fun b hb ↦ (hJ b).1
    (Ideal.span_le.2 (Set.range_subset_iff.2 fun i ↦ (hJ _).2 (hi i)) hb)

/-- If `u ≫ c = v` and `v ≫ d = u`, then `c ≫ d = 𝟙` once precomposition with `u` is
injective. -/
private theorem comp_eq_id_of_injective_precomp {C : Type*} [Category C] {P Q R : C}
    (u : P ⟶ Q) (v : P ⟶ R) (c : Q ⟶ R) (d : R ⟶ Q) (hc : u ≫ c = v) (hd : v ≫ d = u)
    (hu : Function.Injective (fun g : Q ⟶ Q ↦ u ≫ g)) : c ≫ d = 𝟙 Q :=
  hu (by simp only [← Category.assoc, hc, hd, Category.comp_id])

include hI h𝓘 hG in
/-- **The Beck–Chevalley condition for derived completion along `G`.** A map
`c : G(K)^∧ ⟶ G(K^∧)` whose composite with the unit of derived completion on `D(A)` is
`G(K ⟶ K^∧)` is an isomorphism, for every triangulated `G : D(𝒪) ⥤ D(A)` preserving countable
products and carrying multiplication by `ρ c` to multiplication by `c`. -/
theorem isIso_of_adicCompletionUnit_comp [G.CommShift ℤ] [G.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) G]
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    letI := isRightAdjoint_ι_isDerivedComplete_of_isIdealSheafGeneratedBy X A ρ hI h𝓘
    ∀ (c : (Stacks.Algebraization.adicCompletionFunctor A I hI).obj (G.obj K) ⟶
        G.obj ((derivedCompletion X 𝓘).obj K)),
      (Stacks.Algebraization.adicCompletionUnit A I hI).app (G.obj K) ≫ c =
        G.map ((derivedCompletionUnit X 𝓘).app K) → IsIso c := by
  let := isRightAdjoint_ι_isDerivedComplete_of_isIdealSheafGeneratedBy X A ρ hI h𝓘
  intro c hc
  have hD : _root_.IsDerivedComplete I (G.obj ((derivedCompletion X 𝓘).obj K)) :=
    isDerivedComplete_map_of_isDerivedComplete hI h𝓘 hG
      (isDerivedComplete_derivedCompletion_obj X 𝓘 K)
  have hC : _root_.IsDerivedComplete I
      ((Stacks.Algebraization.adicCompletionFunctor A I hI).obj (G.obj K)) :=
    ((Dualizing.derivedCompletion A I hI).obj (G.obj K)).property
  have hbij : ∀ {E : DerivedCategory (ModuleCat.{u} A)}, _root_.IsDerivedComplete I E →
      Function.Bijective (fun g : G.obj ((derivedCompletion X 𝓘).obj K) ⟶ E ↦
        G.map ((derivedCompletionUnit X 𝓘).app K) ≫ g) := by
    intro E hE
    obtain ⟨r, a, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
    obtain rfl := eq_of_isIdealSheafGeneratedBy A _ X ρ h𝓘
      (isIdealSheafGeneratedBy_idealOfGlobalSections X A ρ a)
    obtain ⟨θ, hθ⟩ := exists_iso_derivedCompletion_of_bijective_precomp X
      (idealOfGlobalSections X (baseGenerators X A ρ a))
      (isDerivedComplete_completionFunctor X (baseGenerators X A ρ a) K)
      ((completionUnit X (baseGenerators X A ρ a)).app K)
      (fun M hM ↦ bijective_precomp_completionUnit_idealOfGlobalSections X _ K hM)
    exact bijective_precomp_of_comp_eq _ _ (G.map θ.hom) (𝟙 _)
      (by rw [Category.id_comp, ← G.map_comp]; exact congrArg G.map hθ)
      (bijective_precomp_map_completionUnit (K := K) hG hE)
  obtain ⟨d, hd⟩ := (hbij hC).2 ((Stacks.Algebraization.adicCompletionUnit A I hI).app (G.obj K))
  change G.map ((derivedCompletionUnit X 𝓘).app K) ≫ d = _ at hd
  exact ⟨d, comp_eq_id_of_injective_precomp _ _ c d hc hd
    (Stacks.Algebraization.completionUnit_comp_bijective I hI (G.obj K) _ hC).1,
    comp_eq_id_of_injective_precomp _ _ d c hd hc (hbij hD).1⟩

end Comparison

section DerivedGlobalSections

attribute [local instance] hasProductsOfShape_nat_derivedCategory

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)

omit [HasWeakSheafify X.J CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `A`-linear global sections `Hom_𝒪(𝒪, -)` preserve countable products. -/
theorem preservesLimitsOfShape_discrete_nat_moduleGlobalSectionsOver :
    PreservesLimitsOfShape (Discrete ℕ) (moduleGlobalSectionsOver X A ρ) := by
  have h₁ : PreservesLimitsOfShape (Discrete ℕ) (preadditiveCoyonedaObj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
    have hpres : PreservesLimitsOfShape (Discrete ℕ)
        (preadditiveCoyonedaObj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⋙
          forget _) :=
      inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (coyoneda.obj
        (op (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))
    have : ReflectsLimitsOfShape (Discrete ℕ) (forget (ModuleCat.{u}
        (End (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵐᵒᵖ)) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    exact preservesLimitsOfShape_of_reflects_of_preserves _ (forget _)
  have h₂ : PreservesLimitsOfShape (Discrete ℕ)
      (ModuleCat.restrictScalars.{u} ((globalSectionMulEnd X).comp ρ)) :=
    ⟨fun {_} ↦ inferInstance⟩
  exact Limits.comp_preservesLimitsOfShape _ _

/-- `RΓ(𝒞, -) : D(𝒪) ⥤ D(A)` is additive. -/
instance derivedGlobalSectionsOverUnbounded_additive :
    (derivedGlobalSectionsOverUnbounded X A ρ).Additive := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let := Functor.IsRightDerivedFunctor.commShift
    (derivedGlobalSectionsOverUnbounded X A ρ) (derivedGlobalSectionsOverUnboundedUnit X A ρ)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have : (derivedGlobalSectionsOverUnbounded X A ρ).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated (moduleGlobalSectionsOver X A ρ)
      (derivedGlobalSectionsOverUnbounded X A ρ) (derivedGlobalSectionsOverUnboundedUnit X A ρ)
  infer_instance

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- `RΓ(𝒞, -) : D(𝒪) ⥤ D(A)` preserves countable products. -/
theorem preservesLimitsOfShape_discrete_nat_derivedGlobalSectionsOverUnbounded :
    PreservesLimitsOfShape (Discrete ℕ) (derivedGlobalSectionsOverUnbounded X A ρ) := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have := preservesLimitsOfShape_discrete_nat_moduleGlobalSectionsOver X A ρ
  exact ⟨fun {K} ↦ Stacks.Injectives.preservesLimit_discrete_of_isRightDerivedFunctor
    (moduleGlobalSectionsOver X A ρ) (derivedGlobalSectionsOverUnbounded X A ρ)
    (derivedGlobalSectionsOverUnboundedUnit X A ρ) K⟩

variable {X A ρ} {I : Ideal A} (hI : I.FG)
  {𝓘 : SheafOfModules.Submodule
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  (h𝓘 : IsIdealSheafGeneratedBy A I X ρ 𝓘)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
include hI h𝓘 in
/-- **`RΓ(𝒞, -)` carries objects derived complete along `I𝒪` to objects derived complete along
`I`** ([Stacks, Tag 099J] at the morphism to the point). -/
theorem isDerivedComplete_derivedGlobalSectionsOverUnbounded_of_isDerivedComplete
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hL : IsDerivedComplete.{u, u, u, u} X 𝓘 L) :
    _root_.IsDerivedComplete I ((derivedGlobalSectionsOverUnbounded X A ρ).obj L) := by
  have := preservesLimitsOfShape_discrete_nat_derivedGlobalSectionsOverUnbounded X A ρ
  exact isDerivedComplete_map_of_isDerivedComplete hI h𝓘
    (derivedGlobalSectionsOverUnbounded_map_baseSmulCenter X A ρ) hL

/-- **The comparison map `RΓ(𝒞, K)^∧ ⟶ RΓ(𝒞, K^∧)`** in `D(A)`: the completion on the left is
derived `I`-adic completion on `D(A)`, the one on the right is the reflector of
[Stacks, Tag 099F] along `𝓘 = I𝒪`. It is the map the universal property of derived completion
on `D(A)` produces from `RΓ(𝒞, K ⟶ K^∧)`, the target being derived complete by
`isDerivedComplete_derivedGlobalSectionsOverUnbounded_of_isDerivedComplete`; it is
characterized by `adicCompletionUnit_comp_derivedGlobalSectionsCompletionComparison`. -/
def derivedGlobalSectionsCompletionComparison
    [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X 𝓘)).IsRightAdjoint]
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.Algebraization.adicCompletionFunctor A I hI).obj
        ((derivedGlobalSectionsOverUnbounded X A ρ).obj K) ⟶
      (derivedGlobalSectionsOverUnbounded X A ρ).obj ((derivedCompletion X 𝓘).obj K) :=
  (Dualizing.derivedCompleteProperty A I).ι.map
    (((Stacks.Algebraization.adicCompletionAdjunction A I hI).homEquiv _
      ⟨_, isDerivedComplete_derivedGlobalSectionsOverUnbounded_of_isDerivedComplete hI h𝓘
        (isDerivedComplete_derivedCompletion_obj X 𝓘 K)⟩).symm
      ((derivedGlobalSectionsOverUnbounded X A ρ).map ((derivedCompletionUnit X 𝓘).app K)))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The comparison map composed with the unit of derived completion on `D(A)` is
`RΓ(𝒞, K ⟶ K^∧)`. -/
@[reassoc]
theorem adicCompletionUnit_comp_derivedGlobalSectionsCompletionComparison
    [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X 𝓘)).IsRightAdjoint]
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.Algebraization.adicCompletionUnit A I hI).app
        ((derivedGlobalSectionsOverUnbounded X A ρ).obj K) ≫
      derivedGlobalSectionsCompletionComparison hI h𝓘 K =
    (derivedGlobalSectionsOverUnbounded X A ρ).map ((derivedCompletionUnit X 𝓘).app K) := by
  unfold derivedGlobalSectionsCompletionComparison
  exact ((Stacks.Algebraization.adicCompletionAdjunction A I hI).homEquiv_unit _ _ _).symm.trans
    (((Stacks.Algebraization.adicCompletionAdjunction A I hI).homEquiv _ _).apply_symm_apply _)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The comparison map is natural in `K`. -/
@[reassoc]
theorem derivedGlobalSectionsCompletionComparison_naturality
    [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X 𝓘)).IsRightAdjoint]
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : K ⟶ K') :
    (Stacks.Algebraization.adicCompletionFunctor A I hI).map
        ((derivedGlobalSectionsOverUnbounded X A ρ).map φ) ≫
      derivedGlobalSectionsCompletionComparison hI h𝓘 K' =
    derivedGlobalSectionsCompletionComparison hI h𝓘 K ≫
      (derivedGlobalSectionsOverUnbounded X A ρ).map ((derivedCompletion X 𝓘).map φ) := by
  refine (Stacks.Algebraization.completionUnit_comp_bijective I hI _ _
    (isDerivedComplete_derivedGlobalSectionsOverUnbounded_of_isDerivedComplete hI h𝓘
      (isDerivedComplete_derivedCompletion_obj X 𝓘 K'))).1 ?_
  change (Stacks.Algebraization.adicCompletionUnit A I hI).app _ ≫ _ ≫ _ =
    (Stacks.Algebraization.adicCompletionUnit A I hI).app _ ≫ _ ≫ _
  rw [← Category.assoc, ← (Stacks.Algebraization.adicCompletionUnit A I hI).naturality,
    Category.assoc, adicCompletionUnit_comp_derivedGlobalSectionsCompletionComparison,
    adicCompletionUnit_comp_derivedGlobalSectionsCompletionComparison_assoc,
    Functor.id_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact (derivedCompletionUnit X 𝓘).naturality φ

/-- **`RΓ(𝒞, K)^∧ ⟶ RΓ(𝒞, K^∧)` is an isomorphism.** -/
theorem isIso_derivedGlobalSectionsCompletionComparison
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    letI := isRightAdjoint_ι_isDerivedComplete_of_isIdealSheafGeneratedBy X A ρ hI h𝓘
    IsIso (derivedGlobalSectionsCompletionComparison hI h𝓘 K) := by
  let := isRightAdjoint_ι_isDerivedComplete_of_isIdealSheafGeneratedBy X A ρ hI h𝓘
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let := Functor.IsRightDerivedFunctor.commShift
    (derivedGlobalSectionsOverUnbounded X A ρ) (derivedGlobalSectionsOverUnboundedUnit X A ρ)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have : (derivedGlobalSectionsOverUnbounded X A ρ).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated (moduleGlobalSectionsOver X A ρ)
      (derivedGlobalSectionsOverUnbounded X A ρ) (derivedGlobalSectionsOverUnboundedUnit X A ρ)
  have := preservesLimitsOfShape_discrete_nat_derivedGlobalSectionsOverUnbounded X A ρ
  exact isIso_of_adicCompletionUnit_comp hI h𝓘
    (derivedGlobalSectionsOverUnbounded_map_baseSmulCenter X A ρ) K _
    (adicCompletionUnit_comp_derivedGlobalSectionsCompletionComparison hI h𝓘 K)

/-- **The isomorphism `RΓ(𝒞, K)^∧ ≅ RΓ(𝒞, K^∧)` in `D(A)`.** -/
def derivedGlobalSectionsCompletionIso
    [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X 𝓘)).IsRightAdjoint]
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.Algebraization.adicCompletionFunctor A I hI).obj
        ((derivedGlobalSectionsOverUnbounded X A ρ).obj K) ≅
      (derivedGlobalSectionsOverUnbounded X A ρ).obj ((derivedCompletion X 𝓘).obj K) :=
  have := isIso_derivedGlobalSectionsCompletionComparison hI h𝓘 K
  asIso (derivedGlobalSectionsCompletionComparison hI h𝓘 K)

/-- The forward map of `derivedGlobalSectionsCompletionIso` is
`derivedGlobalSectionsCompletionComparison`. -/
@[simp]
theorem derivedGlobalSectionsCompletionIso_hom
    [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X 𝓘)).IsRightAdjoint]
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedGlobalSectionsCompletionIso hI h𝓘 K).hom =
      derivedGlobalSectionsCompletionComparison hI h𝓘 K :=
  rfl

end DerivedGlobalSections

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry

open RingedSite

/-- A ring map `A ⟶ Γ(S, 𝒪_S)` read as a ring map into the compatible families of local
sections of the structure sheaf of the small Zariski ringed site of `S`. -/
def Scheme.zariskiSectionsRingHom (S : Scheme.{u}) {A : Type u} [CommRing A]
    (φ : A →+* Γ(S, ⊤)) :
    A →+* RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O).obj where
  toFun b := ⟨(Stacks.SheafOfModules.terminalSection
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O) ⊤
      Limits.isTerminalTop (φ b)).val,
    (Stacks.SheafOfModules.terminalSection
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O) ⊤
      Limits.isTerminalTop (φ b)).property⟩
  map_one' := by
    ext U
    simp only [Stacks.SheafOfModules.terminalSection, map_one]
    exact map_one _
  map_mul' _ _ := by
    ext U
    simp only [Stacks.SheafOfModules.terminalSection, map_mul]
    exact map_mul _ _ _
  map_zero' := by
    ext U
    simp only [Stacks.SheafOfModules.terminalSection, map_zero]
    exact map_zero _
  map_add' _ _ := by
    ext U
    simp only [Stacks.SheafOfModules.terminalSection, map_add]
    exact map_add _ _ _

end AlgebraicGeometry

namespace Stacks.Algebraization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.RingedSite Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- **`A ⟶ Γ(U, 𝒪_U)` for `U = Spec(A) ∖ V(𝔞)`**, as a ring map into the compatible families of
local sections of the structure sheaf of the small Zariski ringed site of `U`: the composite of
`A ≅ Γ(Spec(A), 𝒪)` with restriction to `U`. -/
def complementBaseRingHom (𝔞 : Ideal A) :
    A →+* RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf
      (complementZeroLocus A 𝔞 : Scheme).zariskiRingedSite.O).obj :=
  Scheme.zariskiSectionsRingHom _
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (complementZeroLocus A 𝔞).ι.appTop).hom

/-- **`RΓ(U, F)^∧ = RΓ(U, F^∧)` in `D(A)` on the punctured spectrum.** Let `A` be a Noetherian
ring, `I, 𝔞 ⊂ A` ideals, `U = Spec(A) ∖ V(𝔞)` and `F` an `𝒪_U`-module. The comparison map from
the derived `I`-adic completion of `RΓ(U, F)` to `RΓ(U, F^∧)`, the derived completion of `F` on
`U` being taken along `I𝒪_U`, is an isomorphism. -/
theorem isIso_complementGlobalSectionsCompletionComparison [IsNoetherianRing A] (I 𝔞 : Ideal A)
    (F : (complementZeroLocus A 𝔞 : Scheme).Modules) :
    letI := isRightAdjoint_ι_isDerivedComplete_of_isIdealSheafGeneratedBy
      (complementZeroLocus A 𝔞 : Scheme).zariskiRingedSite A (complementBaseRingHom A 𝔞)
      I.fg_of_isNoetherianRing (isIdealSheafGeneratedBy_idealSheafOfIdeal _ A _ I)
    IsIso (derivedGlobalSectionsCompletionComparison
      (X := (complementZeroLocus A 𝔞 : Scheme).zariskiRingedSite)
      (ρ := complementBaseRingHom A 𝔞) I.fg_of_isNoetherianRing
      (isIdealSheafGeneratedBy_idealSheafOfIdeal _ A _ I)
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (complementZeroLocus A 𝔞 : Scheme).zariskiRingedSite.O)) 0).obj F)) :=
  isIso_derivedGlobalSectionsCompletionComparison _ _ _

end Stacks.Algebraization
