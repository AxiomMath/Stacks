module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforwardSheafHomExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensorUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorCone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodAcyclicDifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedGoodResolutionDataConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedHomKInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftFunctorFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionTower
public import StacksFrontier.CategoryTheory.Functor.Derived.RightDerivedComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCohomologyDerivedHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDeltaFunctorTriangle

/-!
# The right derived extension of `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`

Let `f` be a morphism of ringed sites, presented as a continuous functor `f : 𝒟 ⥤ 𝒞` in the
direction opposite to it together with the structure map `σ : O_𝒟 ⟶ f_*O_𝒞`. Let `𝒜` and `𝒜'` be
sheaves of differential graded algebras on `𝒞`, let `ℬ` be one on `𝒟`, let `φ : ℬ ⟶ f_*𝒜` be a
homomorphism and let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule. Let
`RT : D(𝒜', d) ⥤ D(ℬ, d)` be the right derived extension of the exact functor
`ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of [Stacks, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS).
Then

`RT(ℳ) = Rf_* RSheafHom^dg_{𝒜'}(𝒩, ℳ)`

functorially in `ℳ`. This is [Stacks, Tag 0FTT](https://stacks.math.columbia.edu/tag/0FTT) for a
morphism of ringed topoi induced by a continuous functor of sites; the tag for an arbitrary
morphism of ringed topoi is proved in `DifferentialGradedToposPushforwardSheafHomDerived.lean`
from the general lemmas here.

## Main results

* `CategoryTheory.Localization.eq_zero_of_isLocalOn_of_distinguished`: in a triangulated category
  localized at a class `W` of morphisms, every morphism from an object with a shift-stable
  property `P` into the cone of a morphism of `W` between objects local for the morphisms of `W`
  between objects with `P` is zero.
* `SheafOfModules.acyclic_of_forall_exists_preimage`: a complex of sheaves of modules whose
  cocycles on sections are coboundaries on sections is acyclic.
* `SheafOfModules.DifferentialGradedModule.isLocalOn_sheafHom`: `SheafHom^dg_{𝒜'}(𝒩, ℐ)` is local
  for the quasi-isomorphisms between flat and K-flat modules when `ℐ` is graded injective and
  K-injective.
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_homotopyPushforwardFunctor_map`: the
  direct image carries a quasi-isomorphism between such local objects to a quasi-isomorphism.
* `SheafOfModules.DifferentialGradedModule.isIso_app_sheafHom`: the derived pushforward is
  computed by the direct image on `SheafHom^dg_{𝒜'}(𝒩, ℐ)`.
* `SheafOfModules.DifferentialGradedModule.exists_iso_rightDerived_pushforwardSheafHom`: the
  identification for arbitrary right derived functors with their comparison maps.
* `SheafOfModules.DifferentialGradedModule.exists_iso_derivedPushforwardSheafHom`: the same for
  the constructed functors `RT = derivedPushforwardSheafHom φ 𝒩`,
  `RSheafHom^dg_{𝒜'}(𝒩, -) = derivedSheafHom 𝒩` and `Rf_* = rightDerivedPushforward φ`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedPushforwardSheafHom`: the right derived
  extension `RT` of the functor of Tag 0FTS.
* `SheafOfModules.DifferentialGradedModule.rightDerivedPushforward`: the derived pushforward
  `Rf_*` along `φ`.

## Implementation notes

**The proof.** The source deduces the tag from the uniqueness of adjoints: both functors are
right adjoint to `Lf^*(-) ⊗^{L}_𝒜 𝒩`. The argument here stays on the side of the right adjoints
and compares the two functors directly. Both `RT` and `RSheafHom^dg_{𝒜'}(𝒩, -) ⋙ Rf_*` are right
derived functors of `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`, the second as soon as `Rf_*` is computed by
the direct image on `ℋ = SheafHom^dg_{𝒜'}(𝒩, ℐ)` for every graded injective K-injective `ℐ`.
The module `ℋ` need not be K-injective, but by the tensor-hom adjunction of
[Stacks, Tag 0FRS] and clause (1) of [Stacks, Tag 0FSI] it is local for the quasi-isomorphisms
between flat and K-flat modules; so is a graded injective K-injective resolution `ℋ ⟶ 𝒥`. The
cone `𝒞` of `ℋ ⟶ 𝒥` then receives only the zero morphism from a flat and K-flat module, and
applying this to the free module on the closed sections of `𝒞` shows that every cocycle of `𝒞`
over an object of the site is a coboundary over that object. Since the sections of `f_*𝒞` over
`V` are those of `𝒞` over `f(V)`, the cone `f_*𝒞` of `f_*ℋ ⟶ f_*𝒥` is acyclic. This is the same
mathematics as the source's adjunction `Lf^* ⊣ Rf_*` read on the free modules `𝒜[S]`, whose
pullbacks are free, and it needs neither a pullback functor nor the derived tensor product.

**The derived functors.** The tag is stated for the right derived extensions constructed in
[Stacks, Tag 0FTN] (`SheafOfModules.DifferentialGradedModule.rightDerivedExtension`): `RT` of the
functor of Tag 0FTS, the derived internal hom `derivedSheafHom` of Tag 0FTQ, and the derived
pushforward. It is deduced from the same statement for arbitrary right derived functors with
their comparison maps. The equality of the source is an isomorphism of functors, compatible with
the comparison maps.

**Universes.** The sites, the algebras, the bimodule and the modules are in one universe, the
setting of the resolutions of [Stacks, Tag 0FT0] and [Stacks, Tag 0FSH].

## References

* [Stacks Project, Tag 0FTT](https://stacks.math.columbia.edu/tag/0FTT)
* [Stacks Project, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS)
* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
* [Stacks Project, Tag 0FTN](https://stacks.math.columbia.edu/tag/0FTN)
* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v₁ v₂ u₁ u₂

namespace CategoryTheory.Localization

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  [W.HasRightCalculusOfFractions] [W.IsMultiplicative]

include L in
/-- **Morphisms into the third vertex of a triangle on a morphism between local objects
vanish.** Let `P` be a property of objects stable under the shift by `-1` such that every object
receives a morphism of `W` from an object with `P`, and let `T` be a distinguished triangle whose
first morphism lies in `W` and whose first two vertices are local for the morphisms of `W`
between objects with `P`. Then every morphism from an object with `P` into the third vertex of
`T` is zero. -/
theorem eq_zero_of_isLocalOn_of_distinguished (P : C → Prop)
    (hres : ∀ X : C, ∃ (Y : C) (s : Y ⟶ X), W s ∧ P Y)
    (hshift : ∀ X : C, P X → P ((shiftFunctor C (-1 : ℤ)).obj X))
    (T : Triangle C) (hT : T ∈ distTriang C) (hs : W T.mor₁)
    (h₁ : W.IsLocalOn P T.obj₁) (h₂ : W.IsLocalOn P T.obj₂)
    {X : C} (hX : P X) (g : X ⟶ T.obj₃) : g = 0 := by
  have hb := fun {Z : C} (hZ : P Z) =>
    bijective_comp_map_of_isLocalOn L W P hres h₁ h₂ T.mor₁ hs hZ
  have h3 : g ≫ T.mor₃ = 0 := by
    let e := shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)
    let b : (shiftFunctor C (-1 : ℤ)).obj X ⟶ T.obj₁ :=
      (shiftFunctor C (-1 : ℤ)).map (g ≫ T.mor₃) ≫ e.hom.app T.obj₁
    have hb0 : b ≫ T.mor₁ = 0 ≫ T.mor₁ := by
      have hn := e.hom.naturality T.mor₁
      simp only [Functor.id_map, Functor.comp_map] at hn
      rw [zero_comp]
      change ((shiftFunctor C (-1 : ℤ)).map (g ≫ T.mor₃) ≫ e.hom.app T.obj₁) ≫ T.mor₁ = 0
      rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, Category.assoc,
        comp_distTriang_mor_zero₃₁ T hT, comp_zero, Functor.map_zero, zero_comp]
    have : (shiftFunctor C (-1 : ℤ)).map (g ≫ T.mor₃) = (shiftFunctor C (-1 : ℤ)).map 0 := by
      rw [Functor.map_zero]
      simpa [b] using congrArg (· ≫ e.inv.app T.obj₁) ((hb (hshift X hX)).1 hb0)
    exact (shiftFunctor C (-1 : ℤ)).map_injective this
  obtain ⟨h, rfl⟩ := Triangle.coyoneda_exact₃ T hT g h3
  obtain ⟨k, rfl⟩ := (hb hX).2 h
  simp [comp_distTriang_mor_zero₁₂ T hT]

end CategoryTheory.Localization

namespace SheafOfModules

section Sectionwise

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A short complex of sheaves of modules which is exact on sections is exact.** Exactness on
sections is exactness of the underlying short complex of presheaves of modules, and
sheafification, which is exact, carries that short complex back to the given one. -/
theorem exact_of_forall_exists_preimage (S : ShortComplex (SheafOfModules.{u} R))
    (h : ∀ (T : Cᵒᵖ) (x : S.X₂.val.obj T), S.g.val.app T x = 0 →
      ∃ y : S.X₁.val.obj T, S.f.val.app T y = x) : S.Exact := by
  let F := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let a := PresheafOfModules.sheafification (𝟙 R.obj)
  have hF : (S.map F).Exact := PresheafOfModules.exact_of_sectionwise _ fun T x =>
    ⟨fun hx => h T x hx, by
      rintro ⟨y, rfl⟩
      exact (S.map (evaluation R T)).moduleCat_zero_apply y⟩
  have hlim : PreservesFiniteLimits a := inferInstance
  have hzero : a.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have hcolim : PreservesFiniteColimits a := ⟨fun _ _ _ =>
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape⟩
  have : a.PreservesHomology := Functor.preservesHomologyOfExact _
  have e : F ⋙ a ≅ 𝟭 _ := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit
  exact (ShortComplex.exact_iff_of_iso (ShortComplex.mapNatIso S e)).1 (hF.map a)

/-- **A complex of sheaves of modules all of whose cocycles on sections are coboundaries on
sections is acyclic.** -/
theorem acyclic_of_forall_exists_preimage (K : CochainComplex (SheafOfModules.{u} R) ℤ)
    (h : ∀ (n : ℤ) (T : Cᵒᵖ) (x : (K.X n).val.obj T), (K.d n (n + 1)).val.app T x = 0 →
      ∃ y : (K.X (n - 1)).val.obj T, (K.d (n - 1) n).val.app T y = x) : K.Acyclic := fun n =>
  (K.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).2
    (exact_of_forall_exists_preimage _ fun T x hx => h n T x hx)

end Sectionwise

end SheafOfModules

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

section Flat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- An object of the homotopy category is *flat* when the right differential graded module it is
is flat as a graded module and K-flat. -/
def IsFlatObj (Z : HomotopyCategory.{u, u, u} A) : Prop :=
  RelativeTensor.IsGradedFlat (Osharp := X.O) (GradedModule.ofDifferentialGraded Z.as) ∧
    RelativeTensor.IsKFlat (Osharp := X.O) Z.as

/-- **A module into which every morphism out of a flat module is null-homotopic has exact
complexes of sections.** A cocycle `x` of `M` over `U` is the image of the generator it names in
the free module on the closed sections of `M`; that free module is flat, so its morphism to `M`
is null-homotopic, and a null-homotopy carries the generator, which is closed, to a primitive
of `x`. -/
theorem exists_d_eq_of_forall_eq_zero (M : DifferentialGradedModule.{u, u, u} A)
    (h : ∀ P : DifferentialGradedModule.{u, u, u} A,
      IsFlatObj ((HomotopyCategory.quotient A).obj P) →
        ∀ g : (HomotopyCategory.quotient A).obj P ⟶ (HomotopyCategory.quotient A).obj M, g = 0)
    (n : ℤ) (U : X.Cᵒᵖ) (x : (M.complex.X n).val.obj U)
    (hx : (M.complex.d n (n + 1)).val.app U x = 0) :
    ∃ y : (M.complex.X (n - 1)).val.obj U, (M.complex.d (n - 1) n).val.app U y = x := by
  obtain ⟨z, hz, rfl⟩ := exists_closed_preimage_freeOnClosedSectionsHom M n U x hx
  have h0 := h _ ⟨freeDGModule_isGradedFlat (Osharp := X.O) A (closedSections M.complex),
    freeDGModule_isKFlat (Osharp := X.O) (closedSections M.complex) A⟩
    ((HomotopyCategory.quotient A).map (freeOnClosedSectionsHom M))
  have h0' : (HomotopyCategory.quotient A).map (freeOnClosedSectionsHom M) =
      (HomotopyCategory.quotient A).map 0 := h0.trans (Functor.map_zero _ _ _).symm
  obtain ⟨H⟩ := (HomotopyCategory.quotient_map_eq_iff _ _).1 h0'
  refine ⟨(H.app n).val.app U z, ?_⟩
  have hc := congrArg (fun φ => homSections φ U z) (H.comm n)
  simp only [homSections_sub, homSections_add, homSections_comp] at hc
  rw [hz] at hc
  simp only [map_zero, add_zero, zero_f, homSections_zero, sub_zero] at hc
  exact hc.symm

variable (A) in
/-- **Tag 0FSH in the homotopy category**: every object receives a quasi-isomorphism from a flat
one. -/
theorem exists_quasiIso_isFlatObj (Z : HomotopyCategory.{u, u, u} A) :
    ∃ (Y : HomotopyCategory.{u, u, u} A) (s : Y ⟶ Z),
      quasiIsomorphisms.{u, u, u} A s ∧ IsFlatObj Y := by
  obtain ⟨P, s, hs, h₁, h₂⟩ := exists_flat_quasiIso (Osharp := X.O) Z.as
  exact ⟨(HomotopyCategory.quotient A).obj P, (HomotopyCategory.quotient A).map s,
    (quasiIsomorphisms_quotient_map_iff s).2 hs, h₁, h₂⟩

/-- A translate of a flat object of the homotopy category is flat. -/
theorem isFlatObj_shift {Z : HomotopyCategory.{u, u, u} A} (hZ : IsFlatObj Z) (k : ℤ) :
    IsFlatObj ((shiftFunctor (HomotopyCategory.{u, u, u} A) k).obj Z) := by
  have e := congrArg CategoryTheory.Quotient.as
    (HomotopyCategory.shiftFunctor_obj_eq.{u, u, u} A k Z.as)
  change IsFlatObj ((shiftFunctor (HomotopyCategory.{u, u, u} A) k).obj
    ((HomotopyCategory.quotient A).obj Z.as))
  unfold IsFlatObj
  rw [e]
  exact ⟨isGradedFlat_dgShiftFunctor_obj A k Z.as hZ.1, isKFlat_dgShiftFunctor_obj A k Z.as hZ.2⟩

/-- A morphism from a flat object into the third vertex of a distinguished triangle whose first
morphism is a quasi-isomorphism between local objects is zero. -/
private theorem eq_zero_of_isLocalOn_flat {T : Triangle (HomotopyCategory.{u, u, u} A)}
    (hT : T ∈ distTriang (HomotopyCategory.{u, u, u} A)) (hs : quasiIsomorphisms.{u, u, u} A T.mor₁)
    (h₁ : (quasiIsomorphisms.{u, u, u} A).IsLocalOn IsFlatObj T.obj₁)
    (h₂ : (quasiIsomorphisms.{u, u, u} A).IsLocalOn IsFlatObj T.obj₂)
    {P : HomotopyCategory.{u, u, u} A} (hP : IsFlatObj P) (g : P ⟶ T.obj₃) : g = 0 :=
  Localization.eq_zero_of_isLocalOn_of_distinguished (toDerivedCategory.{u, u, u} A)
    (quasiIsomorphisms.{u, u, u} A) IsFlatObj (exists_quasiIso_isFlatObj A)
    (fun _ hW => isFlatObj_shift hW (-1)) T hT hs h₁ h₂ hP g

/-- **The cone of a quasi-isomorphism between objects local for the quasi-isomorphisms between
flat objects receives only the zero morphism from a flat object.** -/
theorem eq_zero_of_isLocalOn_cone {H J : DifferentialGradedModule.{u, u, u} A}
    (hH : (quasiIsomorphisms.{u, u, u} A).IsLocalOn IsFlatObj ((HomotopyCategory.quotient A).obj H))
    (hJ : (quasiIsomorphisms.{u, u, u} A).IsLocalOn IsFlatObj ((HomotopyCategory.quotient A).obj J))
    (s : H ⟶ J) (hs : QuasiIso s.toHomologicalComplex) (P : DifferentialGradedModule.{u, u, u} A)
    (hP : IsFlatObj ((HomotopyCategory.quotient A).obj P))
    (g : (HomotopyCategory.quotient A).obj P ⟶ (HomotopyCategory.quotient A).obj (cone s)) :
    g = 0 :=
  eq_zero_of_isLocalOn_flat (homotopyConeTriangle_distinguished s)
    ((quasiIsomorphisms_quotient_map_iff s).2 hs) hH hJ hP g

end Flat

/-! ### The internal hom into a K-injective module is local for the flat objects -/

section SheafHom

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A A' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- **The tensor product with a bimodule carries a quasi-isomorphism between flat modules to a
quasi-isomorphism.** The cone is flat, K-flat and acyclic, so its tensor product is acyclic by
clause (1) of Tag 0FSI, and that tensor product is the cone of the tensored homomorphism. -/
theorem quasiIso_tensorFunctorData_map {N : DifferentialGradedBimodule.{u, u, u} A A'}
    (D : TensorFunctorData.{u, u, u, u, u} A A' N)
    {P Q : DifferentialGradedModule.{u, u, u} A} (s : P ⟶ Q)
    (hP : IsFlatObj ((HomotopyCategory.quotient A).obj P))
    (hQ : IsFlatObj ((HomotopyCategory.quotient A).obj Q))
    (hs : QuasiIso s.toHomologicalComplex) :
    QuasiIso (D.functor.map s).toHomologicalComplex := by
  have hc := isGradedFlat_and_isKFlat_cone (Osharp := X.O) s hP hQ
  have hac : (cone s).complex.Acyclic := (acyclic_cone_iff_quasiIso _ s).2 hs
  have hE : (D.functor.obj (cone s)).complex.Acyclic :=
    acyclic_of_isTensorProduct_of_isKFlat_of_acyclic hc.2 hac (D.isTensorProduct (cone s))
  have hcone : (cone (D.functor.map s)).complex.Acyclic := fun i =>
    (hE i).of_iso (D.coneComplexIso s).symm
  exact (acyclic_cone_iff_quasiIso _ _).1 hcone

/-- **`SheafHom^dg_{𝒜'}(𝒩, ℐ)` is local for the quasi-isomorphisms between flat objects** when
`ℐ` is graded injective and K-injective. Through the adjunction `- ⊗_𝒜 𝒩 ⊣ SheafHom^dg_{𝒜'}(𝒩, -)`
of homotopy categories (Tag 0FRS), precomposition with a quasi-isomorphism `s` of flat modules
is precomposition with `s ⊗ 𝒩`, a quasi-isomorphism, on morphisms into `ℐ`, and `ℐ` is local for
all quasi-isomorphisms (Tag 0FSX). -/
theorem isLocalOn_sheafHom (N : DifferentialGradedBimodule.{u, u, u} A A')
    {I : DifferentialGradedModule.{u, u, u} A'} (hI : IsDGInjective I) :
    (quasiIsomorphisms.{u, u, u} A).IsLocalOn IsFlatObj
      ((HomotopyCategory.quotient A).obj ((sheafHomFunctor N).obj I)) := by
  intro Y Z t ht hY hZ
  let D := RelativeTensor.tensorFunctorDataDgTensorRight (Osharp := X.O) N
  let L : HomotopyCategory.{u, u, u} A ⥤ HomotopyCategory.{u, u, u} A' := homotopyTensorFunctor D
  let R : HomotopyCategory.{u, u, u} A' ⥤ HomotopyCategory.{u, u, u} A :=
    homotopySheafHomFunctor (sheafHomHomotopyExtension N)
  let adj : L ⊣ R := homotopyTensorSheafHomAdjunction D (sheafHomHomotopyExtension N)
  obtain ⟨t₀, rfl⟩ := (HomotopyCategory.quotient A).map_surjective t
  have hLt : quasiIsomorphisms.{u, u, u} A' (L.map ((HomotopyCategory.quotient A).map t₀)) :=
    (quasiIsomorphisms_quotient_map_iff _).2
      (quasiIso_tensorFunctorData_map D t₀ hY hZ ((quasiIsomorphisms_quotient_map_iff t₀).1 ht))
  have hb := isLocal_quotient_obj_of_isKInjective hI.2 hI.1 _ hLt
  have key : (fun g : (HomotopyCategory.quotient A).obj Z.as ⟶
        (HomotopyCategory.quotient A).obj ((sheafHomFunctor N).obj I) =>
      (HomotopyCategory.quotient A).map t₀ ≫ g) =
      (adj.homEquiv _ _) ∘ (fun h => L.map ((HomotopyCategory.quotient A).map t₀) ≫ h) ∘
        (adj.homEquiv _ _).symm := by
    funext g
    exact ((adj.homEquiv _ _).apply_symm_apply _).symm.trans
      (congrArg (adj.homEquiv _ _) (adj.homEquiv_naturality_left_symm _ _))
  exact key ▸ (adj.homEquiv _ _).bijective.comp (hb.comp (adj.homEquiv _ _).symm.bijective)

end SheafHom

/-! ### The direct image of a quasi-isomorphism between local objects -/

section Pushforward

variable {X Y : AlgebraicGeometry.RingedSite.{u, u, u}} {f : Y.C ⥤ X.C} [f.IsContinuous Y.J X.J]
  {σ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj ⟶
    f.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
  {A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
  (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)

/-- **The direct image carries a quasi-isomorphism between objects local for the
quasi-isomorphisms between flat objects to a quasi-isomorphism.** Complete the quasi-isomorphism
`s : ℋ ⟶ 𝒥` to a distinguished triangle `ℋ ⟶ 𝒥 ⟶ 𝒞 ⟶ ℋ[1]`. Every morphism from a flat object
into `𝒞` vanishes, so every cocycle of `𝒞` over an object of the site is a coboundary there.
The sections of `f_*𝒞` over `V` are those of `𝒞` over `f(V)`, so `f_*𝒞` is acyclic; and it is the
third vertex of the image of the triangle under the triangulated functor `K(f_*)`. -/
theorem quasiIsomorphisms_homotopyPushforwardFunctor_map {H J : HomotopyCategory.{u, u, u} A}
    (hH : (quasiIsomorphisms.{u, u, u} A).IsLocalOn IsFlatObj H)
    (hJ : (quasiIsomorphisms.{u, u, u} A).IsLocalOn IsFlatObj J) (s : H ⟶ J)
    (hs : quasiIsomorphisms.{u, u, u} A s) :
    quasiIsomorphisms.{u, u, u} B ((homotopyPushforwardFunctor φ).map s) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle s
  have hT' := (pushforwardConcreteDGFunctor φ).homotopyFunctor.map_distinguished _ hT
  rw [← acyclic_trW_eq_quasiIsomorphisms.{u, u, u} B]
  have := acyclic_isClosedUnderIsomorphisms.{u, u, u} B
  refine ((acyclic.{u, u, u} B).trW_iff_of_distinguished _ hT').2 ?_
  change ((pushforwardFunctor φ).obj Z.as).complex.Acyclic
  exact SheafOfModules.acyclic_of_forall_exists_preimage _ fun n V x hx =>
    exists_d_eq_of_forall_eq_zero Z.as
      (fun _ hP g => eq_zero_of_isLocalOn_flat hT hs hH hJ hP g)
      n (f.op.obj V) x hx

end Pushforward

/-! ### Right derived functors are computed on graded injective K-injective modules -/

section Computed

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- **The comparison map of any right derived functor out of `D(𝒜, d)` is invertible at a graded
injective K-injective module**, the right derived functor being given as an explicit argument. It
differs from that of the right derived extension of [Stacks, Tag 0FTN] by the canonical
isomorphism between two right derived functors. -/
theorem isIso_app_of_isRightDerivedFunctor' {H : Type*} [Category H]
    {F : HomotopyCategory.{u, u, u} A ⥤ H} (RF : derivedCategory.{u, u, u} A ⥤ H)
    (α : F ⟶ toDerivedCategory.{u, u, u} A ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α (quasiIsomorphisms.{u, u, u} A))
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsDGInjective I) :
    IsIso (α.app ((HomotopyCategory.quotient A).obj I)) := by
  have := isRightDerivedFunctor_rightDerivedExtension.{u, u, u} F
  have := isIso_rightDerivedExtensionUnit_app.{u, u, u} F hI
  let e := Functor.rightDerivedNatIso (rightDerivedExtension.{u, u, u} F) RF
    (rightDerivedExtensionUnit.{u, u, u} F) α (quasiIsomorphisms.{u, u, u} A) (Iso.refl F)
  have hfac := Functor.rightDerivedNatTrans_app (rightDerivedExtension.{u, u, u} F) RF
    (rightDerivedExtensionUnit.{u, u, u} F) α (quasiIsomorphisms.{u, u, u} A) (Iso.refl F).hom
    ((HomotopyCategory.quotient A).obj I)
  rw [Iso.refl_hom, NatTrans.id_app, Category.id_comp] at hfac
  rw [← hfac]
  exact IsIso.comp_isIso' inferInstance (inferInstanceAs (IsIso (e.hom.app _)))

/-- **The comparison map of any right derived functor out of `D(𝒜, d)` is invertible at a graded
injective K-injective module.** -/
theorem isIso_app_of_isRightDerivedFunctor {H : Type*} [Category H]
    {F : HomotopyCategory.{u, u, u} A ⥤ H} (RF : derivedCategory.{u, u, u} A ⥤ H)
    (α : F ⟶ toDerivedCategory.{u, u, u} A ⋙ RF)
    [RF.IsRightDerivedFunctor α (quasiIsomorphisms.{u, u, u} A)]
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsDGInjective I) :
    IsIso (α.app ((HomotopyCategory.quotient A).obj I)) :=
  isIso_app_of_isRightDerivedFunctor' RF α inferInstance hI

end Computed

/-! ### Stacks 0FTT -/

section Main

variable {X Y : AlgebraicGeometry.RingedSite.{u, u, u}} {f : Y.C ⥤ X.C} [f.IsContinuous Y.J X.J]
  {σ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj ⟶
    f.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
  {A A' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}

/-- The functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of homotopy categories of
[Stacks, Tag 0FTS] is `K(SheafHom^dg_{𝒜'}(𝒩, -))` followed by `K(f_*)`. -/
theorem homotopyPushforwardSheafHom_eq_comp
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    homotopyPushforwardSheafHom.{u, u, u, u, u} φ N =
      homotopySheafHomFunctor (sheafHomHomotopyExtension N) ⋙ homotopyPushforwardFunctor φ :=
  (HomotopyCategory.eq_descend _ (PreservesHomotopic.comp
      (sheafHomHomotopyExtension N).preservesHomotopic
      (preservesHomotopic_pushforwardFunctor φ)) _
      (quotient_comp_homotopyPushforwardSheafHom φ N)).trans
    (HomotopyCategory.descend_comp _ _ _ _)

/-- **The derived pushforward is computed on `SheafHom^dg_{𝒜'}(𝒩, ℐ)`** for `ℐ` graded injective
and K-injective: the comparison map of `Rf_*` is invertible there. Resolve
`SheafHom^dg_{𝒜'}(𝒩, ℐ)` by a graded injective K-injective module `𝒥`; both are local for the
quasi-isomorphisms between flat objects, so the direct image of the resolution is a
quasi-isomorphism, and the comparison map is invertible at `𝒥`. -/
theorem isIso_app_sheafHom (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (Rf : derivedCategory.{u, u, u} A ⥤ derivedCategory.{u, u, u} B)
    (βf : homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, u, u} B ⟶
      toDerivedCategory.{u, u, u} A ⋙ Rf)
    [Rf.IsRightDerivedFunctor βf (quasiIsomorphisms.{u, u, u} A)]
    (N : DifferentialGradedBimodule.{u, u, u} A A')
    {I : DifferentialGradedModule.{u, u, u} A'} (hI : IsDGInjective I) :
    IsIso (βf.app ((HomotopyCategory.quotient A).obj ((sheafHomFunctor N).obj I))) := by
  obtain ⟨J, s, hs, hKJ, hGJ⟩ := exists_quasiIso_isDGInjective.{u, u, u} A
    ((HomotopyCategory.quotient A).obj ((sheafHomFunctor N).obj I))
  have h₁ : IsIso (βf.app J) := isIso_app_of_isRightDerivedFunctor Rf βf (I := J.as) ⟨hGJ, hKJ⟩
  have h₂ : IsIso ((homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, u, u} B).map s) :=
    Localization.inverts (toDerivedCategory.{u, u, u} B) (quasiIsomorphisms.{u, u, u} B) _
      (quasiIsomorphisms_homotopyPushforwardFunctor_map φ (isLocalOn_sheafHom N hI)
        (fun _ _ t ht _ _ => isLocal_quotient_obj_of_isKInjective hKJ hGJ t ht) s hs)
  have h₃ : IsIso ((toDerivedCategory.{u, u, u} A ⋙ Rf).map s) := by
    have := Localization.inverts (toDerivedCategory.{u, u, u} A)
      (quasiIsomorphisms.{u, u, u} A) s hs
    exact inferInstanceAs (IsIso (Rf.map ((toDerivedCategory.{u, u, u} A).map s)))
  have : IsIso (βf.app _ ≫ (toDerivedCategory.{u, u, u} A ⋙ Rf).map s) := by
    rw [← βf.naturality s]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((toDerivedCategory.{u, u, u} A ⋙ Rf).map s)

/-- **`RT(ℳ) = Rf_* RSheafHom^dg_{𝒜'}(𝒩, ℳ)` for arbitrary right derived functors.** Let `RT`,
`RSheafHom^dg_{𝒜'}(𝒩, -)` and `Rf_*` be any right derived functors, with their comparison maps,
of `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`, of `SheafHom^dg_{𝒜'}(𝒩, -)` and of `f_*` on homotopy
categories followed by the localizations. Then `RT ≅ RSheafHom^dg_{𝒜'}(𝒩, -) ⋙ Rf_*` by the
canonical isomorphism, compatible with the comparison maps. The constructed functors are treated
in `exists_iso_derivedPushforwardSheafHom`, which is Tag 0FTT. -/
theorem exists_iso_rightDerived_pushforwardSheafHom
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, u, u} A A')
    (RT : derivedCategory.{u, u, u} A' ⥤ derivedCategory.{u, u, u} B)
    (βT : homotopyPushforwardSheafHom.{u, u, u, u, u} φ N ⋙ toDerivedCategory.{u, u, u} B ⟶
      toDerivedCategory.{u, u, u} A' ⋙ RT)
    [RT.IsRightDerivedFunctor βT (quasiIsomorphisms.{u, u, u} A')]
    (RH : derivedCategory.{u, u, u} A' ⥤ derivedCategory.{u, u, u} A)
    (βH : homotopySheafHomFunctor (sheafHomHomotopyExtension N) ⋙ toDerivedCategory.{u, u, u} A ⟶
      toDerivedCategory.{u, u, u} A' ⋙ RH)
    [RH.IsRightDerivedFunctor βH (quasiIsomorphisms.{u, u, u} A')]
    (Rf : derivedCategory.{u, u, u} A ⥤ derivedCategory.{u, u, u} B)
    (βf : homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, u, u} B ⟶
      toDerivedCategory.{u, u, u} A ⋙ Rf)
    [Rf.IsRightDerivedFunctor βf (quasiIsomorphisms.{u, u, u} A)] :
    ∃ e : RT ≅ RH ⋙ Rf, ∀ K : HomotopyCategory.{u, u, u} A',
      βT.app K ≫ e.hom.app ((toDerivedCategory.{u, u, u} A').obj K) =
        βf.app ((homotopySheafHomFunctor (sheafHomHomotopyExtension N)).obj K) ≫
          Rf.map (βH.app K) := by
  have : (RH ⋙ Rf).IsRightDerivedFunctor (Functor.rightDerivedCompUnit βH βf)
      (quasiIsomorphisms.{u, u, u} A') :=
    Functor.isRightDerivedFunctor_comp_of_isIso (quasiIsomorphisms.{u, u, u} A') βH βf
      (fun Z => IsKInjective Z.as ∧ GradedInjective Z.as)
      (exists_quasiIso_isDGInjective.{u, u, u} A')
      (fun I hI Z => bijective_toDerivedCategory_map (hasKInjectiveResolutions_dg.{u, u, u} A')
        Z hI.1 hI.2)
      (fun I hI => isIso_app_of_isRightDerivedFunctor RH βH (I := I.as) ⟨hI.2, hI.1⟩)
      (fun I hI => isIso_app_sheafHom φ Rf βf N (I := I.as) ⟨hI.2, hI.1⟩)
  refine ⟨Functor.rightDerivedNatIso RT (RH ⋙ Rf) βT (Functor.rightDerivedCompUnit βH βf)
    (quasiIsomorphisms.{u, u, u} A')
    (eqToIso (by rw [homotopyPushforwardSheafHom_eq_comp φ N])), fun K => ?_⟩
  rw [Functor.rightDerivedNatIso_hom, Functor.rightDerivedNatTrans_app,
    Functor.rightDerivedCompUnit_app, eqToIso.hom, eqToHom_app]
  exact Category.id_comp _

/-- **The right derived extension `RT : D(𝒜', d) ⥤ D(ℬ, d)` of the functor
`ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of [Stacks, Tag 0FTS]**, followed by the localization, as
constructed in [Stacks, Tag 0FTN]. -/
noncomputable def derivedPushforwardSheafHom
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    derivedCategory.{u, u, u} A' ⥤ derivedCategory.{u, u, u} B :=
  rightDerivedExtension.{u, u, u}
    (homotopyPushforwardSheafHom.{u, u, u, u, u} φ N ⋙ toDerivedCategory.{u, u, u} B)

/-- The comparison map `f_*SheafHom^dg_{𝒜'}(𝒩, ℳ) ⟶ RT(ℳ)`. -/
noncomputable def derivedPushforwardSheafHomUnit
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    homotopyPushforwardSheafHom.{u, u, u, u, u} φ N ⋙ toDerivedCategory.{u, u, u} B ⟶
      toDerivedCategory.{u, u, u} A' ⋙ derivedPushforwardSheafHom φ N :=
  rightDerivedExtensionUnit.{u, u, u} _

/-- **The derived pushforward `Rf_* : D(𝒜, d) ⥤ D(ℬ, d)`** of [Stacks, Tag 0FTP] (2): the right
derived extension of the direct image on homotopy categories followed by the localization, as
constructed in [Stacks, Tag 0FTN]. -/
noncomputable def rightDerivedPushforward
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A) :
    derivedCategory.{u, u, u} A ⥤ derivedCategory.{u, u, u} B :=
  rightDerivedExtension.{u, u, u} (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, u, u} B)

/-- The comparison map `f_*ℳ ⟶ Rf_*ℳ`. -/
noncomputable def rightDerivedPushforwardUnit
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A) :
    homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, u, u} B ⟶
      toDerivedCategory.{u, u, u} A ⋙ rightDerivedPushforward φ :=
  rightDerivedExtensionUnit.{u, u, u} _

/-- **`RT(ℳ) = Rf_* RSheafHom^dg_{𝒜'}(𝒩, ℳ)` along a morphism of ringed sites.** This is
[Stacks, Tag 0FTT] in the special case of a morphism of ringed topoi induced by a continuous
functor of sites; the tag itself, along an arbitrary morphism of ringed topoi, is
`SheafOfModules.DifferentialGradedModule.exists_iso_derivedToposPushforwardSheafHom`. Let `f` be a
morphism of ringed sites, let `𝒜` and `𝒜'` be sheaves of
differential graded algebras on its source and `ℬ` one on its target, let `φ : ℬ ⟶ f_*𝒜` be a
homomorphism and let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule. Let
`RT : D(𝒜', d) ⥤ D(ℬ, d)` be the right derived extension of the functor
`ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of [Stacks, Tag 0FTS], `RSheafHom^dg_{𝒜'}(𝒩, -)` the derived
internal hom and `Rf_*` the derived pushforward of [Stacks, Tag 0FTP]. Then

`RT(ℳ) = Rf_* RSheafHom^dg_{𝒜'}(𝒩, ℳ)`

functorially in `ℳ`: there is an isomorphism of functors `RT ≅ RSheafHom^dg_{𝒜'}(𝒩, -) ⋙ Rf_*`,
and it is the canonical one, compatible with the comparison maps.

The morphism of ringed sites is read, as throughout, as a continuous functor `f : 𝒟 ⥤ 𝒞` in the
direction opposite to it together with the structure map `σ : O_𝒟 ⟶ f_*O_𝒞`. -/
theorem exists_iso_derivedPushforwardSheafHom
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    ∃ e : derivedPushforwardSheafHom φ N ≅ derivedSheafHom N ⋙ rightDerivedPushforward φ,
      ∀ K : HomotopyCategory.{u, u, u} A',
        (derivedPushforwardSheafHomUnit φ N).app K ≫
            e.hom.app ((toDerivedCategory.{u, u, u} A').obj K) =
          (rightDerivedPushforwardUnit φ).app ((homotopySheafHom N).obj K) ≫
            (rightDerivedPushforward φ).map ((derivedSheafHomUnit N).app K) :=
  have : (derivedPushforwardSheafHom φ N).IsRightDerivedFunctor
      (derivedPushforwardSheafHomUnit φ N) (quasiIsomorphisms.{u, u, u} A') :=
    isRightDerivedFunctor_rightDerivedExtension.{u, u, u} _
  have : (rightDerivedPushforward φ).IsRightDerivedFunctor (rightDerivedPushforwardUnit φ)
      (quasiIsomorphisms.{u, u, u} A) :=
    isRightDerivedFunctor_rightDerivedExtension.{u, u, u} _
  exists_iso_rightDerived_pushforwardSheafHom φ N _ (derivedPushforwardSheafHomUnit φ N) _
    (derivedSheafHomUnit N) _ (rightDerivedPushforwardUnit φ)

end Main

end SheafOfModules.DifferentialGradedModule
