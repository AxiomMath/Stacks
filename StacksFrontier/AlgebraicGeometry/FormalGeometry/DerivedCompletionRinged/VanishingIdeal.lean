module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LeftAdjoint
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated

/-!
# The vanishing locus of an object of the derived category of a ringed site

Let `(𝒞, 𝒪)` be a ringed site and let `K ∈ D(𝒪)`. [Stacks, Tag 0998] asserts that the sections
`f` of `𝒪` with `T(K, f) = 0` form a sheaf of ideals in `𝒪`. This file defines that locus for a
global section of the structure sheaf, proves that it is stable under multiplication by a
further global section, and proves the triangulated two-out-of-three step by which the source
obtains additivity.

## Main definitions

* `AlgebraicGeometry.RingedSite.MemVanishingIdeal`: the global section `f` of `𝒪` satisfies
  `R𝑆heafHom_𝒪(𝒪_f, K) = 0`.
* `AlgebraicGeometry.RingedSite.IsRightOrthogonalAway`: `K` is right orthogonal to `D(𝒪_f)`,
  that is, `R𝑆heafHom_𝒪(L, K) = 0` for every complex `L` of `𝒪_f`-modules.

## Main results

* `AlgebraicGeometry.RingedSite.isRightOrthogonalAway_mulGlobalSection` and
  `AlgebraicGeometry.RingedSite.memVanishingIdeal_mulGlobalSection`: the vanishing locus is
  closed under multiplication by an arbitrary global section of `𝒪`.
* `AlgebraicGeometry.RingedSite.isRightOrthogonalAway_prodGlobalSection_of_subset`: the same
  for the localization system of a finite family, namely that for `S ⊆ T` right orthogonality
  to `D(𝒪_{f_S})` implies right orthogonality to `D(𝒪_{f_T})`.
* `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_restrictScalars_of_factorization`: the
  mechanism behind those, namely that right orthogonality to the image of `D(R')` in `D(𝒪)`
  propagates to `D(R'')` along a factorization `𝒪 ⟶ R' ⟶ R''`.
* `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_obj₁_of_distTriang`,
  `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_obj₂_of_distTriang` and
  `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_obj₃_of_distTriang`: vanishing of the
  derived internal Hom into `K` on two vertices of a distinguished triangle forces it on the
  third, and `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_biprod` for a direct sum.
* `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_shift_iff`: that vanishing only depends
  on the source up to shift, which is what a dévissage along the stupid filtration of a complex
  needs, its terms appearing there in their own degrees.

## Implementation notes

The source phrases membership by the vanishing of the derived limit `T(K, f)` and trades that
for the vanishing of `R𝑆heafHom_𝒪(𝒪_f, K)` by [Stacks, Tag 0997] without further mention.
`MemVanishingIdeal` is accordingly defined by the vanishing of the derived internal Hom out of
`AlgebraicGeometry.RingedSite.awayModule`, and that this agrees with the source's condition
`T(K, f) = 0` is now proved: it is
`AlgebraicGeometry.RingedSite.memVanishingIdeal_iff_isDerivedCompleteAt` of
`VanishingFromComplete.lean` (in this file's directory,
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/`),
the equivalence of conditions (1) and (3) of [Stacks, Tag 0997]. That file imports this one, so
the equivalence is not available to the proofs below.

Closure under multiplication is proved for the right-orthogonality condition (2) rather than
for `MemVanishingIdeal` itself. The reason is the same gap: the source deduces
`R𝑆heafHom_𝒪(𝒪_{gf}, K) = 0` from `R𝑆heafHom_𝒪(𝒪_f, K) = 0` by observing that `𝒪_{gf}` is an
`𝒪_f`-module and invoking (1) ⇒ (2) of [Stacks, Tag 0997], which is not available here. Condition
(2), on the other hand, propagates along the transition map `𝒪_{f_S} ⟶ 𝒪_{f_T}` of
`AlgebraicGeometry.RingedSite.existsUnique_awayTransition` by pure functoriality: restriction
of scalars along `𝒪 ⟶ 𝒪_{f_T}` is restriction along `𝒪 ⟶ 𝒪_{f_S}` of restriction along
`𝒪_{f_S} ⟶ 𝒪_{f_T}`. On complexes that composition is an equality of functors, so the
comparison in the derived category is read off from
`CategoryTheory.Functor.mapDerivedCategoryFactors` at a complex representing the given object,
which exists because `DerivedCategory.Q` is essentially surjective.

### What remains for Tag 0998

No sheaf of ideals is constructed here, and the tag below carries a qualifier. Three inputs are
missing for the right-orthogonality route of this file; for the tag itself, see item 3.

1. **Additivity**, for which the ring-level input is now fully in hand and the sheaf-level lift
   is the remaining gap. The source's argument is the short exact sequence
   `0 → 𝒪_{f + g} → 𝒪_{f(f + g)} ⊕ 𝒪_{g(f + g)} → 𝒪_{gf(f + g)} → 0`, which holds because `f`
   and `g` generate the unit ideal in `𝒪(U)_{f + g}`; the ring-level statement is Algebra,
   Lemma 00EJ. The library already has this under
   `StacksDraft.RingTheory.Localization.Glueing.Functions.alphaLin_injective` and
   `StacksDraft.RingTheory.Localization.Glueing.Functions.ker_betaLin_eq_range_alphaLin`, in the
   `Fin n`-indexed form; it now also has the two-generator case needed here directly in product
   form, as
   `StacksDraft.RingTheory.Localization.Glueing.Functions.alphaPair_injective` and
   `StacksDraft.RingTheory.Localization.Glueing.Functions.ker_betaPair_eq_range_alphaPair`,
   stated for `Localization.Away a × Localization.Away b → Localization.Away (a * b)` rather
   than indexed by `Fin 2 × Fin 2`, which is the shape a short exact sequence of sheaves of
   modules over a ringed site wants (the `Fin 2`-indexed target of `β` carries dead diagonal
   components and a `(1, 0)`-component of a type merely isomorphic, not equal, to the
   `(0, 1)`-component's). What is still missing is the *sheaf-level* lift of that ring-level
   exact sequence: naturality of `alphaPair`/`betaPair` in the restriction maps of `𝒪`, exactness
   after sheafification, and packaging the result as a `CategoryTheory.ShortComplex.ShortExact`
   of `SheafOfModules` so as to produce a distinguished triangle in `D(𝒪)` via
   `CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished`. The terms of that
   sequence are the sheaves `AlgebraicGeometry.RingedSite.awayModule` of the products of
   `AlgebraicGeometry.RingedSite.prodGlobalSection`, so the indexing is in place. What the
   source then does with the triangle *is* available: `isZero_derivedSheafHom_obj₁_of_distTriang`
   and `isZero_derivedSheafHom_biprod` above are the vanishing on the middle and right terms
   forcing the vanishing on the left, resting on the contravariant half of [Stacks, Tag 08JC],
   `AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom`.
2. **Multiplicativity for condition (1).** The route through the implication (1) ⇒ (2) of
   [Stacks, Tag 0997], which is still open, is not the only one: the equivalence of
   conditions (1) and (3),
   `AlgebraicGeometry.RingedSite.memVanishingIdeal_iff_isDerivedCompleteAt` of
   `VanishingFromComplete.lean`, trades `MemVanishingIdeal X K g` for
   `IsDerivedCompleteAt K (globalSectionToEnd 𝒪 (awayFamily X g))`, where `𝒪` denotes
   `Stacks.SheafOfModules.Tensor.ringSheaf X.O` and `globalSectionToEnd` is
   `Stacks.SheafOfModules.globalSectionToEnd`; the latter condition is closed under
   multiplication by an arbitrary central endomorphism by the purely algebraic
   `isDerivedCompleteAt_smul` of `StacksFrontier/Homology/DerivedComplete/CompleteIdeal.lean`. What
   that route still owes is the comparison of the two scalars: that
   `globalSectionToEnd 𝒪 (awayFamily X (mulGlobalSection X g h))` is the product of
   `globalSectionToEnd 𝒪 (awayFamily X g)` and `globalSectionToEnd 𝒪 (awayFamily X h)` in
   `CatCenter (SheafOfModules.{u} 𝒪)`, which is a sectionwise `mul_smul` and is not stated
   anywhere — `Stacks.SheafOfModules.globalSectionToEnd` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GlobalSectionSmul.lean` carries only
   `globalSectionToEnd_apply` and `globalSectionToEnd_pow_apply`, and the sections of a sheaf of
   rings are not equipped with a `Mul` there.
3. **The sheaf condition**, for the locus as this file spells it. `RingedSite.awaySheaf` inverts
   a *global* section, so `f ∈ 𝒪(U)` is handled on the localized ringed site, where it is
   global; comparing the locus over `U` with the one over `V` for `V ⟶ U` then needs the base
   change of `𝒪_{U, f}` along `Over V ⥤ Over U`, which nothing provides, and locality needs the
   same for a covering. In the equivalent Milnor spelling the tag is now proved outright, as
   `AlgebraicGeometry.RingedSite.derivedCompleteIdealSheaf` of `VanishingIdealSheafCondition.lean`.

## References

* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 0997](https://stacks.math.columbia.edu/tag/0997)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 00EJ](https://stacks.math.columbia.edu/tag/00EJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

section Exactness

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{u}}

/-- Restriction of scalars along a morphism of sheaves of rings preserves finite limits,
because it does not change the underlying sheaf of abelian groups. -/
instance preservesFiniteLimits_restrictScalars (α : R ⟶ R') :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} α) := by
  have : PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.toSheaf R) := by
    change PreservesFiniteLimits (SheafOfModules.toSheaf.{u} R')
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf R)

/-- Restriction of scalars along a morphism of sheaves of rings preserves finite colimits,
because it does not change the underlying sheaf of abelian groups. -/
instance preservesFiniteColimits_restrictScalars (α : R ⟶ R') :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} α) := by
  have : PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{u} R') :=
    preservesColimitsOfSize_shrink _
  have : PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.toSheaf R) := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R')
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf R)

end Exactness

section GlobalSections

variable (X : RingedSite.{u, u, u})

/-- A global section of the structure sheaf is determined by its values. -/
theorem globalSections_ext
    {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}
    (H : ∀ U, globalSectionVal h U = globalSectionVal h' U) : h = h' :=
  (Presheaf.globalSectionsEquivSections _).injective (Subtype.ext (funext H))

/-- The product of a one-element subfamily of global sections is its unique member. -/
theorem prodGlobalSection_singleton {r : ℕ}
    (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (i : Fin r) :
    prodGlobalSection f {i} = f i :=
  globalSections_ext X fun U ↦ by
    rw [globalSectionVal_prodGlobalSection, Finset.prod_singleton]

/-- The product of two global sections of the structure sheaf; this is the two-element case of
`AlgebraicGeometry.RingedSite.prodGlobalSection`. -/
abbrev mulGlobalSection (g h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}) :=
  prodGlobalSection ![g, h] {0, 1}

/-- The value of the product of two global sections on an object `U` is the product of their
values on `U`. -/
@[simp]
theorem globalSectionVal_mulGlobalSection
    (g h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) :
    globalSectionVal (mulGlobalSection X g h) U =
      globalSectionVal g U * globalSectionVal h U := by
  change globalSectionVal (prodGlobalSection ![g, h] {0, 1}) U = _
  rw [globalSectionVal_prodGlobalSection]
  simp

end GlobalSections

section Derived

attribute [local instance] HasDerivedCategory.standard

section Tower

variable (X : RingedSite.{u, u, u})

/-- Right orthogonality propagates along a tower of sheaves of rings over `𝒪`: if the derived
internal Hom into `K` out of the image of `D(R')` vanishes and `𝒪 ⟶ R''` factors through `R'`,
then it vanishes out of the image of `D(R'')` as well. -/
theorem isZero_derivedSheafHom_restrictScalars_of_factorization
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {R' R'' : Sheaf X.J RingCat.{u}} (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶ R')
    (b : R' ⟶ R'')
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶ R'') (hc : a ≫ b = c)
    (H : ∀ L : DerivedCategory (SheafOfModules.{u} R'),
      IsZero (((derivedSheafHomBifunctor X).obj
        (op ((SheafOfModules.restrictScalars.{u} a).mapDerivedCategory.obj L))).obj K))
    (L : DerivedCategory (SheafOfModules.{u} R'')) :
    IsZero (((derivedSheafHomBifunctor X).obj
      (op ((SheafOfModules.restrictScalars.{u} c).mapDerivedCategory.obj L))).obj K) := by
  subst hc
  set L₀ := DerivedCategory.Q.objPreimage L with hL₀
  have eL : DerivedCategory.Q.obj L₀ ≅ L := DerivedCategory.Q.objObjPreimageIso L
  set A := SheafOfModules.restrictScalars.{u} a with hA
  set B := SheafOfModules.restrictScalars.{u} b with hB
  have e : (SheafOfModules.restrictScalars.{u} (a ≫ b)).mapDerivedCategory.obj L ≅
      A.mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj L₀)) :=
    (SheafOfModules.restrictScalars.{u} (a ≫ b)).mapDerivedCategory.mapIso eL.symm ≪≫
      (SheafOfModules.restrictScalars.{u} (a ≫ b)).mapDerivedCategoryFactors.app L₀ ≪≫
        (A.mapDerivedCategoryFactors.app
          ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj L₀)).symm
  exact IsZero.of_iso (H _) (((derivedSheafHomBifunctor X).mapIso e.symm.op).app K)

end Tower

section Triangles

variable (X : RingedSite.{u, u, u})
  (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (T : Triangle (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- The derived internal Hom into `K` is an exact functor of triangulated categories in its
source, so its vanishing on the second and third vertices of a distinguished triangle forces
its vanishing on the first. -/
theorem isZero_derivedSheafHom_obj₁_of_distTriang
    (hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (h₂ : IsZero (((derivedSheafHomBifunctor X).obj (op T.obj₂)).obj K))
    (h₃ : IsZero (((derivedSheafHomBifunctor X).obj (op T.obj₃)).obj K)) :
    IsZero (((derivedSheafHomBifunctor X).obj (op T.obj₁)).obj K) := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom X K T hT
  exact Triangle.isZero₃_of_isZero₁₂ _ hδ h₃ h₂

/-- Vanishing of the derived internal Hom into `K` on the first and third vertices of a
distinguished triangle forces its vanishing on the second. -/
theorem isZero_derivedSheafHom_obj₂_of_distTriang
    (hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (h₁ : IsZero (((derivedSheafHomBifunctor X).obj (op T.obj₁)).obj K))
    (h₃ : IsZero (((derivedSheafHomBifunctor X).obj (op T.obj₃)).obj K)) :
    IsZero (((derivedSheafHomBifunctor X).obj (op T.obj₂)).obj K) := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom X K T hT
  exact Triangle.isZero₂_of_isZero₁₃ _ hδ h₃ h₁

/-- Vanishing of the derived internal Hom into `K` on the first and second vertices of a
distinguished triangle forces its vanishing on the third. -/
theorem isZero_derivedSheafHom_obj₃_of_distTriang
    (hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (h₁ : IsZero (((derivedSheafHomBifunctor X).obj (op T.obj₁)).obj K))
    (h₂ : IsZero (((derivedSheafHomBifunctor X).obj (op T.obj₂)).obj K)) :
    IsZero (((derivedSheafHomBifunctor X).obj (op T.obj₃)).obj K) := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom X K T hT
  exact Triangle.isZero₁_of_isZero₂₃ _ hδ h₂ h₁

open scoped ZeroObject

/-- Derived internal Hom into `K` out of a zero object vanishes, that functor being additive. -/
theorem isZero_derivedSheafHom_zero :
    IsZero (((derivedSheafHomBifunctor X).obj
      (op (0 : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))).obj K) :=
  Functor.map_isZero ((derivedSheafHomBifunctor X).flip.obj K)
    (IsZero.op (isZero_zero
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))

/-- **Vanishing of the derived internal Hom into `K` is stable under shifting the source by
one.** The triangle `A ⟶ 0 ⟶ A⟦1⟧` whose third morphism is the identity is distinguished, its
middle vertex being zero, so the vanishing on `A` and the vanishing on `A⟦1⟧` imply each
other. -/
theorem isZero_derivedSheafHom_shift_one_iff
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsZero (((derivedSheafHomBifunctor X).obj (op (A⟦(1 : ℤ)⟧))).obj K) ↔
      IsZero (((derivedSheafHomBifunctor X).obj (op A)).obj K) := by
  have hT : Triangle.mk
      (0 : A ⟶ (0 : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (0 : (0 : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶ A⟦(1 : ℤ)⟧)
      (𝟙 (A⟦(1 : ℤ)⟧)) ∈ distTriang
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
    rw [Triangle.distinguished_iff_of_isZero₂ _ (isZero_zero _)]
    exact IsIso.id _
  exact ⟨fun h ↦ isZero_derivedSheafHom_obj₁_of_distTriang X K _ hT
      (isZero_derivedSheafHom_zero X K) h,
    fun h ↦ isZero_derivedSheafHom_obj₃_of_distTriang X K _ hT h
      (isZero_derivedSheafHom_zero X K)⟩

/-- Vanishing of the derived internal Hom into `K` only depends on the isomorphism class of the
source. -/
theorem isZero_derivedSheafHom_iff_of_iso
    {A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : A ≅ B) :
    IsZero (((derivedSheafHomBifunctor X).obj (op A)).obj K) ↔
      IsZero (((derivedSheafHomBifunctor X).obj (op B)).obj K) :=
  ⟨fun h ↦ IsZero.of_iso h (((derivedSheafHomBifunctor X).mapIso e.op).app K),
    fun h ↦ IsZero.of_iso h (((derivedSheafHomBifunctor X).mapIso e.symm.op).app K)⟩

/-- **Vanishing of the derived internal Hom into `K` is stable under shifting the source**, for
an arbitrary shift, by induction from the case of a shift by one. This is what a dévissage along
the stupid filtration of a complex needs, the `p`-th term appearing there in degree `p`; no
`CategoryTheory.Functor.CommShift` is available for the derived internal Hom in either
variable, and this statement does not need one. -/
theorem isZero_derivedSheafHom_shift_iff
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) :
    IsZero (((derivedSheafHomBifunctor X).obj (op (A⟦n⟧))).obj K) ↔
      IsZero (((derivedSheafHomBifunctor X).obj (op A)).obj K) := by
  have hstep : ∀ m k : ℤ, m + 1 = k →
      (IsZero (((derivedSheafHomBifunctor X).obj (op (A⟦k⟧))).obj K) ↔
        IsZero (((derivedSheafHomBifunctor X).obj (op (A⟦m⟧))).obj K)) := by
    intro m k hk
    subst hk
    exact (isZero_derivedSheafHom_iff_of_iso X K
        ((shiftFunctorAdd
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            m 1).app A)).trans
      (isZero_derivedSheafHom_shift_one_iff X K (A⟦m⟧))
  induction n using Int.induction_on with
  | zero => exact isZero_derivedSheafHom_iff_of_iso X K ((shiftFunctorZero _ ℤ).app A)
  | succ i hi => exact (hstep i (i + 1) rfl).trans hi
  | pred i hi => exact (hstep (-(i : ℤ) - 1) (-(i : ℤ)) (by ring)).symm.trans hi

/-- Vanishing of the derived internal Hom into `K` is stable under direct sums in the source,
because `A ⟶ A ⊞ B ⟶ B ⟶ A⟦1⟧` is a distinguished triangle. -/
theorem isZero_derivedSheafHom_biprod
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hA : IsZero (((derivedSheafHomBifunctor X).obj (op A)).obj K))
    (hB : IsZero (((derivedSheafHomBifunctor X).obj (op B)).obj K)) :
    IsZero (((derivedSheafHomBifunctor X).obj (op (A ⊞ B))).obj K) :=
  isZero_derivedSheafHom_obj₂_of_distTriang X K (binaryBiproductTriangle A B)
    (binaryBiproductTriangle_distinguished A B) hA hB

/-- Vanishing of the derived internal Hom out of a fixed source only depends on the isomorphism
class of the target. -/
private theorem isZero_derivedSheafHom_iff_of_iso_right
    {K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : K ≅ K') (A : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsZero (((derivedSheafHomBifunctor X).obj (op A)).obj K) ↔
      IsZero (((derivedSheafHomBifunctor X).obj (op A)).obj K') :=
  ⟨fun H ↦ H.of_iso (((derivedSheafHomBifunctor X).obj _).mapIso e.symm),
    fun H ↦ H.of_iso (((derivedSheafHomBifunctor X).obj _).mapIso e)⟩

end Triangles

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]

/-- The canonical map `𝒪 ⟶ 𝒪_f`, read as a morphism of sheaves of rings. -/
abbrev toAwayRingSheaf (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O) :=
  (sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map (toAwaySheaf h)

/-- A map `𝒪_f ⟶ 𝒪_g` of structure sheaves, read as a morphism of sheaves of rings. -/
abbrev awayRingSheafMap
    {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}
    (φ : awaySheaf h ⟶ awaySheaf h') :
    (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h').O) :=
  (sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

/-- A factorization of `𝒪 ⟶ 𝒪_g` through `𝒪_f` is one of the corresponding morphisms of
sheaves of rings. -/
theorem toAwayRingSheaf_comp_awayRingSheafMap
    {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}
    (φ : awaySheaf h ⟶ awaySheaf h') (hφ : toAwaySheaf h ≫ φ = toAwaySheaf h') :
    toAwayRingSheaf X h ≫ awayRingSheafMap X φ = toAwayRingSheaf X h' :=
  (Functor.map_comp _ _ _).symm.trans (by rw [hφ])

/-- The global section `f` of `𝒪` lies in the vanishing locus of `K` when the derived internal
Hom `R𝑆heafHom_𝒪(𝒪_f, K)` is zero. This is the membership condition of the sheaf of ideals of
[Stacks, Tag 0998], which the source phrases as `T(K, f) = 0`; the two agree by
[Stacks, Tag 0997]. -/
def MemVanishingIdeal
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) : Prop :=
  IsZero (((derivedSheafHomBifunctor X).obj (op (derivedAwayModule X h))).obj K)

/-- `K` is right orthogonal to `D(𝒪_f)`: the derived internal Hom over `𝒪` out of every complex
of `𝒪_f`-modules into `K` vanishes. This is condition (2) of [Stacks, Tag 0997]. -/
def IsRightOrthogonalAway
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) : Prop :=
  ∀ L : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (awayRingedSite X h).O)),
    IsZero (((derivedSheafHomBifunctor X).obj
      (op ((awayRestrictScalarsDerived X h).obj L))).obj K)

/-- Right orthogonality to `D(𝒪_f)` places `f` in the vanishing locus. This is the implication
(2) ⇒ (1) of [Stacks, Tag 0997]. -/
theorem MemVanishingIdeal.of_isRightOrthogonalAway
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}
    (H : IsRightOrthogonalAway X K h) : MemVanishingIdeal X K h :=
  isZero_derivedSheafHom_derivedAwayModule_of_forall X h K H

/-- Right orthogonality to `D(𝒪_f)` passes to `D(𝒪_g)` whenever the canonical map `𝒪 ⟶ 𝒪_g`
factors through `𝒪_f`. -/
theorem isRightOrthogonalAway_of_lift
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}
    (φ : awaySheaf h ⟶ awaySheaf h') (hφ : toAwaySheaf h ≫ φ = toAwaySheaf h')
    (H : IsRightOrthogonalAway X K h) : IsRightOrthogonalAway X K h' := fun L ↦
  isZero_derivedSheafHom_restrictScalars_of_factorization X K (toAwayRingSheaf X h)
    (awayRingSheafMap X φ) (toAwayRingSheaf X h')
    (toAwayRingSheaf_comp_awayRingSheafMap X φ hφ) H L

/-- For global sections `f_1, …, f_r` of `𝒪` and `S ⊆ T`, right orthogonality of `K` to
`D(𝒪_{f_S})` implies right orthogonality to `D(𝒪_{f_T})`: the canonical map `𝒪 ⟶ 𝒪_{f_T}`
factors through `𝒪_{f_S}` because `f_S` divides `f_T`. -/
theorem isRightOrthogonalAway_prodGlobalSection_of_subset
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) {r : ℕ}
    (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hS : IsRightOrthogonalAway X K (prodGlobalSection f S)) :
    IsRightOrthogonalAway X K (prodGlobalSection f T) := by
  obtain ⟨φ, hφ, -⟩ := existsUnique_awayTransition f hST
  exact isRightOrthogonalAway_of_lift X K φ hφ hS

/-- **The vanishing locus is closed under multiplication.** If `K` is right orthogonal to
`D(𝒪_f)` and `g` is any global section of `𝒪`, then `K` is right orthogonal to `D(𝒪_{gf})`.
This is the first half of the proof of [Stacks, Tag 0998]: the source observes that `𝒪_{gf}` is
an `𝒪_f`-module, which here is the factorization of `𝒪 ⟶ 𝒪_{gf}` through `𝒪_f`. -/
@[stacks 0998 "closure under multiplication, for the right-orthogonality condition of 0997"]
theorem isRightOrthogonalAway_mulGlobalSection
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (g h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (H : IsRightOrthogonalAway X K h) :
    IsRightOrthogonalAway X K (mulGlobalSection X g h) := by
  refine isRightOrthogonalAway_prodGlobalSection_of_subset X K ![g, h]
    (S := {1}) (T := {0, 1}) (by decide) ?_
  have h1 : prodGlobalSection ![g, h] {1} = h := by
    rw [prodGlobalSection_singleton]; simp
  rw [h1]
  exact H

/-- If `K` is right orthogonal to `D(𝒪_f)` then `gf` lies in the vanishing locus of `K`, for
every global section `g` of `𝒪`. -/
theorem memVanishingIdeal_mulGlobalSection
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (g h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (H : IsRightOrthogonalAway X K h) :
    MemVanishingIdeal X K (mulGlobalSection X g h) :=
  .of_isRightOrthogonalAway X K (isRightOrthogonalAway_mulGlobalSection X K g h H)

/-- For `S ⊆ T`, right orthogonality of `K` to `D(𝒪_{f_S})` places `f_T` in the vanishing
locus of `K`. -/
theorem memVanishingIdeal_prodGlobalSection_of_subset
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) {r : ℕ}
    (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hS : IsRightOrthogonalAway X K (prodGlobalSection f S)) :
    MemVanishingIdeal X K (prodGlobalSection f T) :=
  .of_isRightOrthogonalAway X K
    (isRightOrthogonalAway_prodGlobalSection_of_subset X K f hST hS)

/-- The vanishing locus depends on `K` only through its isomorphism class in `D(𝒪)`. -/
theorem memVanishingIdeal_iff_of_iso
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : K ≅ K')
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    MemVanishingIdeal X K h ↔ MemVanishingIdeal X K' h :=
  isZero_derivedSheafHom_iff_of_iso_right X K e _

/-- Right orthogonality depends on `K` only through its isomorphism class in `D(𝒪)`. -/
theorem isRightOrthogonalAway_iff_of_iso
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : K ≅ K')
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    IsRightOrthogonalAway X K h ↔ IsRightOrthogonalAway X K' h :=
  forall_congr' fun _ ↦ isZero_derivedSheafHom_iff_of_iso_right X K e _

end Derived

end AlgebraicGeometry.RingedSite

end
