module

public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySections
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of `Ext` may be checked locally

Let `(X, 𝒪_X)` be a ringed space, let `N` and `E` be `𝒪_X`-modules and let `q` be a natural
number. If the opens `V` over which `Ext^n(N|_V, E|_V)` vanishes for every `n ≤ q` form a family
which is a basis near every point of `X`, then `Ext^q(N, E)` vanishes.

The argument runs through the internal Hom complex. Choose a K-injective resolution `I` of `E`
placed in degree zero. The internal Hom complex `SheafHom^•(N, I⟦q⟧)` of [Stacks, Tag 0A8S] is a
complex of `𝒪_X`-modules whose complex of sections over an open `V` is the ordinary Hom complex
of the restrictions, so by [Stacks, Tag 0A8R] its degree-`n` cohomology over `V` is the group of
degree-`n` morphisms `N|_V ⟶ I|_V⟦q⟧` in the derived category of `𝒪_V`-modules. Exactness of a
complex of sheaves is a local condition, so the hypothesis makes that complex live in degree
`≥ 1`; derived global sections are left t-exact, so its degree-zero hypercohomology vanishes; and
that group is `Hom_{D(𝒪_X)}(N, I⟦q⟧) = Ext^q(N, E)` by [Stacks, Tag 08DK].

Nothing here needs a shift of the *derived* internal hom, which this development does not have:
the shift `I⟦q⟧` is taken on the K-injective complex itself, where it is again K-injective, and
`DerivedCategory.Q.commShiftIso` carries it to the derived category.

## Main results

* `Stacks.SheafOfModules.exact_of_locally_surjective_sections` and
  `Stacks.SheafOfModules.moduleExact_of_locally_surjective_sections`: a short complex of sheaves
  whose sections are exact on a family of opens which is a basis near every point is exact.
* `Stacks.SheafOfModules.isGE_of_locally_exactAt_sections`: the same, for a cochain complex and
  the bound on its cohomology.
* `Stacks.SheafOfModules.homComplexHomologyEquivDerivedExt`: for `I` K-injective, cohomology of
  the Hom complex `Hom^•(K, I)` is the group of morphisms in the derived category.
* `Stacks.SheafOfModules.isGE_sheafHomComplex_of_locally_subsingleton` and
  `Stacks.SheafOfModules.subsingleton_hom_of_isGE_sheafHomComplex`: the two halves of the
  argument, local vanishing bounding the internal Hom complex below and that bound killing the
  global morphisms.
* `Stacks.SheafOfModules.subsingleton_shiftedHom_single_of_locally_over`: **the reduction**, on a
  ringed space, with the local condition read on the slice sites.
* `Stacks.SheafOfModules.subsingleton_shiftedHom_single_of_locally_restrict`: **the reduction on
  a scheme**, with the local condition read on open subschemes.

## Implementation notes

No declaration here carries a `@[stacks]` attribute. The statement proved is step 1 of the proof
of [Stacks, Tag 0G5I] — the reduction of that lemma to the affine case — and the source performs
that reduction with the local-to-global spectral sequence of `Ext`, [Stacks, Tag 0BQP], of which
this library has the Ext sheaves and the second page `H^p(X, SheafExt^q(K, L))`
(`Stacks.SheafOfModules.derivedSheafExt` and
`Stacks.SheafOfModules.hypercohomologySpectralSequence_e₂_derivedSheafExt`) but not the
convergence to `Ext^{p + q}` that the reduction consumes; what is proved here is the reduction
itself, not either tag.

The local condition of `subsingleton_shiftedHom_single_of_locally_restrict` is stated in all
degrees `n ≤ q` rather than in degree `q` alone, because the induction that bounds the internal
Hom complex below sees the shifted complex `I⟦q⟧` in every degree `n < 1`, which is degree
`q + n ≤ q` for the unshifted one. Negative degrees cost nothing: there is no morphism of
negative degree between two objects placed in degree zero
(`Stacks.SheafOfModules.subsingleton_shiftedHom_single_of_neg`).

Morphism groups are written as `CategoryTheory.ShiftedHom` in the derived category rather than as
`CategoryTheory.Abelian.Ext`, since that is the form the comparisons of Tags 0A8R and 08DK land
in; `CategoryTheory.Abelian.Ext.homEquiv` converts.

On a scheme the local condition is about the open subscheme `U`, while the sections of the
internal Hom complex are indexed by the slice site `Opens X / U`. The two are identified by
`AlgebraicGeometry.Scheme.Modules.overEquiv` and
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`, which is what
`Stacks.SheafOfModules.subsingleton_shiftedHom_over_of_restrict` does.

## References

* [Stacks Project, Tag 0A8S](https://stacks.math.columbia.edu/tag/0A8S)
* [Stacks Project, Tag 0A8R](https://stacks.math.columbia.edu/tag/0A8R)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0G5I](https://stacks.math.columbia.edu/tag/0G5I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

/-! ### Exactness of a complex of sheaves of modules from its sections on a basis -/

/-- A short complex of sheaves of abelian groups whose sections are exact on a family of opens
which is a basis near every point is exact. -/
theorem exact_of_locally_surjective_sections
    {X : TopCat.{u}} (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (P : Opens X → Prop)
    (hP : ∀ (x : X) (U : Opens X), x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧ P V)
    (hS : ∀ U, P U → ∀ s : S.X₂.obj.obj (op U),
      S.g.hom.app (op U) s = 0 → ∃ t : S.X₁.obj.obj (op U), S.f.hom.app (op U) t = s) :
    S.Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro s hs
  obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.obj s
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g.hom
    (TopCat.Presheaf.germ S.X₂.obj U x hxU t) = 0 at hs
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hs
  have hz : (TopCat.Presheaf.germ S.X₃.obj U x hxU) (0 : S.X₃.obj.obj (op U)) = 0 :=
    map_zero _
  obtain ⟨V, hxV, fVU, _, he⟩ := TopCat.Presheaf.germ_eq S.X₃.obj x hxU hxU _ _ (hs.trans hz.symm)
  obtain ⟨W, hxW, hWV, hW⟩ := hP x V hxV
  let fWU : W ⟶ U := homOfLE hWV ≫ fVU
  have ht : S.g.hom.app (op W) (S.X₂.obj.map fWU.op t) = 0 := by
    rw [← ConcreteCategory.comp_apply, S.g.hom.naturality]
    show S.X₃.obj.map fWU.op (S.g.hom.app (op U) t) = 0
    dsimp [fWU]
    rw [Functor.map_comp]
    show S.X₃.obj.map (homOfLE hWV).op
      (S.X₃.obj.map fVU.op (S.g.hom.app (op U) t)) = 0
    simpa using congrArg (fun a => S.X₃.obj.map (homOfLE hWV).op a) he
  obtain ⟨v, hv⟩ := hS W hW _ ht
  refine ⟨TopCat.Presheaf.germ S.X₁.obj W x hxW v, ?_⟩
  show (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
    (TopCat.Presheaf.germ S.X₁.obj W x hxW v) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hv]
  exact TopCat.Presheaf.germ_res_apply S.X₂.obj fWU x hxW _

/-- A short complex of sheaves of modules whose sections are exact on a family of opens which is
a basis near every point is exact: exactness is reflected by the faithful left exact functor to
sheaves of abelian groups. -/
theorem moduleExact_of_locally_surjective_sections
    {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (S : ShortComplex (_root_.SheafOfModules.{u} O))
    (P : Opens X → Prop)
    (hP : ∀ (x : X) (U : Opens X), x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧ P V)
    (hS : ∀ U, P U → ∀ s : S.X₂.val.obj (op U),
      S.g.val.app (op U) s = 0 → ∃ t : S.X₁.val.obj (op U), S.f.val.app (op U) t = s) :
    S.Exact :=
  (S.exact_map_iff_of_faithful (AlgebraicGeometry.SheafOfModules.toTopSheaf O)).mp
    (exact_of_locally_surjective_sections _ P hP hS)

/-- Taking sections over an open and forgetting the module structure preserves zero morphisms. -/
instance sectionAbelianFunctor_preservesZeroMorphisms
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    ((_root_.SheafOfModules.evaluation O (op U)) ⋙
      forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u}).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

/-- A complex of sheaves of modules has no cohomology below `c` as soon as its complexes of
sections are exact below `c` on a family of opens which is a basis near every point. -/
theorem isGE_of_locally_exactAt_sections
    {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (K : CochainComplex (_root_.SheafOfModules.{u} O) ℤ) (c : ℤ)
    (P : Opens X → Prop)
    (hP : ∀ (x : X) (U : Opens X), x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧ P V)
    (hK : ∀ U, P U → ∀ n < c,
      ((((_root_.SheafOfModules.evaluation O (op U)) ⋙
        forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).ExactAt n) :
    K.IsGE c := by
  rw [CochainComplex.isGE_iff]
  exact fun n hn => moduleExact_of_locally_surjective_sections (K.sc n) P hP
    fun U hU => (ShortComplex.ab_exact_iff _).mp (hK U hU n hn)

/-! ### Cohomology of a Hom complex into a K-injective complex -/

/-- For `I` K-injective, degree-`n` cohomology of the Hom complex `Hom^•(K, I)` is the group of
degree-`n` morphisms in the derived category between the objects `K` and `I` represent. -/
def homComplexHomologyEquivDerivedExt
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasDerivedCategory C]
    (K I : CochainComplex C ℤ) [I.IsKInjective] (n : ℤ) :
    ((K.HomComplex I).homology n : Type u) ≃
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I) n := by
  refine (CochainComplex.HomComplex.homologyAddEquiv K I n).toEquiv.trans ?_
  refine (Equiv.ofBijective _
    (CochainComplex.HomComplex.CohomologyClass.toHom_bijective K I n)).trans ?_
  refine (Equiv.ofBijective _
    (CochainComplex.IsKInjective.Qh_map_bijective _ (I⟦n⟧))).trans ?_
  exact Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
    ((DerivedCategory.quotientCompQhIso C).app (I⟦n⟧) ≪≫
      (DerivedCategory.Q.commShiftIso n).app I)

/-! ### The internal Hom complex has no cohomology below a locally established bound -/

attribute [local instance] HasDerivedCategory.standard

/-- Sections over `U` of the internal Hom complex from `K` to a K-injective `I` have no
cohomology in degree `n` as soon as there is no degree-`n` morphism in the derived category
between the restrictions of `K` and `I` to the slice site over `U`. -/
theorem subsingleton_homology_sectionComplex_sheafHomComplex
    {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
    (K I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective]
    (U : Opens X) (n : ℤ)
    (h : Subsingleton (ShiftedHom (DerivedCategory.Q.obj (restrictComplex Rc K U))
      (DerivedCategory.Q.obj (restrictComplex Rc I U)) n)) :
    Subsingleton ((sectionComplex Rc (sheafHomComplex Rc K I).obj U).homology n : Type u) := by
  let _ : (restrictComplex Rc I U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over _ (structureSheaf Rc) U I
  have h' : Subsingleton
      (((restrictComplex Rc K U).HomComplex (restrictComplex Rc I U)).homology n : Type u) :=
    (Equiv.subsingleton_congr (homComplexHomologyEquivDerivedExt _ _ n)).mpr h
  exact AddCommGrpCat.isZero_iff_subsingleton.mp
    ((AddCommGrpCat.isZero_iff_subsingleton.mpr h').of_iso
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).mapIso
        ((sheafHomComplex Rc K I).sectionsIso U)))

/-- **The internal Hom complex is bounded below by a local bound.** If on a family of opens
which is a basis near every point there is no degree-`n` morphism in the derived category
between the restrictions of `K` and of the K-injective complex `I`, for every `n < c`, then the
internal Hom complex from `K` to `I` has no cohomology below `c`. -/
theorem isGE_sheafHomComplex_of_locally_subsingleton
    {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
    (K I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective] (c : ℤ)
    (P : Opens X → Prop)
    (hP : ∀ (x : X) (U : Opens X), x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧ P V)
    (h : ∀ U, P U → ∀ n < c,
      Subsingleton (ShiftedHom (DerivedCategory.Q.obj (restrictComplex Rc K U))
        (DerivedCategory.Q.obj (restrictComplex Rc I U)) n)) :
    (sheafHomComplex Rc K I).obj.IsGE c :=
  isGE_of_locally_exactAt_sections _ c P hP fun U hU n hn =>
    ((sectionComplex Rc (sheafHomComplex Rc K I).obj U).exactAt_iff_isZero_homology n).mpr
      (AddCommGrpCat.isZero_iff_subsingleton.mpr
        (subsingleton_homology_sectionComplex_sheafHomComplex Rc K I U n (h U hU n hn)))

/-! ### Transport along an exact functor and along an equivalence -/

/-- An exact additive functor carries a complex representing an object placed in degree zero to
a complex representing the image of that object placed in degree zero. -/
def mapComplexSingleIso {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) (N : C)
    (e : DerivedCategory.Q.obj K ≅ (DerivedCategory.singleFunctor C 0).obj N) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      (DerivedCategory.singleFunctor D 0).obj (F.obj N) :=
  (F.mapDerivedCategoryFactors.app K).symm ≪≫
    F.mapDerivedCategory.mapIso e ≪≫ (F.mapDerivedCategorySingleFunctor 0).app N

/-- The derived functor of an equivalence of abelian categories is an equivalence. -/
theorem mapDerivedCategory_isEquivalence {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] :
    e.functor.mapDerivedCategory.IsEquivalence := by
  let Φ := e.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let Ψ := e.inverse.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let ec := e.mapHomologicalComplex (ComplexShape.up ℤ)
  have hΦ : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_unit_of_unit Ψ ec.unitIso.hom ec.counitIso.inv
      (fun K => by
        show QuasiIso (ec.unitIso.app K).hom
        infer_instance)
      (fun K => by
        show QuasiIso (ec.counitIso.app K).inv
        infer_instance)
  let _ : CatCommSq Φ.functor DerivedCategory.Q DerivedCategory.Q
      e.functor.mapDerivedCategory := ⟨e.functor.mapDerivedCategoryFactors.symm⟩
  exact Φ.isEquivalence DerivedCategory.Q DerivedCategory.Q e.functor.mapDerivedCategory

/-- Vanishing of a group of degree-`n` morphisms in the derived category may be checked after
applying an equivalence of abelian categories. -/
theorem subsingleton_shiftedHom_of_equivalence {C D : Type (u + 1)} [Category.{u} C]
    [Category.{u} D] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
    (A B : DerivedCategory C) (n : ℤ)
    (h : Subsingleton (ShiftedHom (e.functor.mapDerivedCategory.obj A)
      (e.functor.mapDerivedCategory.obj B) n)) :
    Subsingleton (ShiftedHom A B n) := by
  have := mapDerivedCategory_isEquivalence e
  have h' : Subsingleton (e.functor.mapDerivedCategory.obj A ⟶
      e.functor.mapDerivedCategory.obj (B⟦n⟧)) :=
    (Equiv.subsingleton_congr (Iso.homCongr (Iso.refl _)
      ((e.functor.mapDerivedCategory.commShiftIso n).app B))).mpr h
  exact (e.functor.mapDerivedCategory.map_injective (X := A) (Y := B⟦n⟧)).subsingleton

/-- There is no morphism of negative degree in the derived category between two objects placed
in degree zero. -/
theorem subsingleton_shiftedHom_single_of_neg {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (A B : C) (k : ℤ) (hk : k < 0) :
    Subsingleton (ShiftedHom ((DerivedCategory.singleFunctor C 0).obj A)
      ((DerivedCategory.singleFunctor C 0).obj B) k) := by
  have _ : (((DerivedCategory.singleFunctor C 0).obj B)⟦k⟧).IsGE (-k) :=
    DerivedCategory.TStructure.t.isGE_shift ((DerivedCategory.singleFunctor C 0).obj B) 0 k (-k)
      (by omega)
  exact ⟨fun f g => (DerivedCategory.TStructure.t.zero f 0 (-k) (by omega)).trans
    (DerivedCategory.TStructure.t.zero g 0 (-k) (by omega)).symm⟩

/-! ### From the bound on the internal Hom complex to vanishing of global morphisms -/

section Global

-- `_root_` is needed: inside `namespace Stacks.SheafOfModules` an unqualified
-- `open AlgebraicGeometry` picks up `Stacks.AlgebraicGeometry` instead.
open _root_.AlgebraicGeometry Stacks.Cohomology.ModuleSections

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ K₁ K₂ : CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ,
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **Global morphisms vanish when the internal Hom complex has no cohomology below `1`.**
Derived global sections are left t-exact, so an internal Hom complex in `D^{≥ 1}` has vanishing
degree-zero hypercohomology, and that group is the group of morphisms `K ⟶ I` in the derived
category by Stacks 08DK. -/
theorem subsingleton_hom_of_isGE_sheafHomComplex
    (K I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective]
    (h : (sheafHomComplex Rc K I).obj.IsGE 1) :
    Subsingleton (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj I) := by
  have hW : (DerivedCategory.Q.obj (sheafHomComplex Rc K I).obj).IsGE 1 := by
    rwa [DerivedCategory.isGE_Q_obj_iff]
  have hW' : (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj
      (op (DerivedCategory.Q.obj K))).obj (DerivedCategory.Q.obj I)).IsGE 1 :=
    DerivedCategory.TStructure.t.isGE_of_iso (derivedSheafHomComparison Rc K I).symm 1
  let _ : (RingedSite.abelianGlobalSectionsFunctor (ringedSite Rc)).Additive :=
    RingedSite.abelianGlobalSectionsFunctor_additive _
  have hGE := Stacks.DerivedFunctor.isGE_totalRightDerived_obj
    (moduleGlobalSections (ringedSite Rc))
    (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj
      (op (DerivedCategory.Q.obj K))).obj (DerivedCategory.Q.obj I)) 1
  exact (Equiv.subsingleton_congr
    (derivedSheafHomGlobalSectionsEquiv Rc (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj I)).toEquiv).mp
    (AddCommGrpCat.isZero_iff_subsingleton.mp
      ((DerivedCategory.isGE_iff _ 1).mp hGE 0 (by omega)))

/-- **Local to global for morphisms in the derived category, in the slice model.** If on a
family of opens which is a basis near every point there is no degree-`n` morphism from the
restriction of `K` to the restriction of `I⟦q⟧` for any `n < 1`, then there is no degree-`q`
morphism from `K` to `I`. -/
theorem subsingleton_shiftedHom_of_locally_subsingleton
    (K I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective] (q : ℕ)
    (P : Opens X → Prop)
    (hP : ∀ (x : X) (U : Opens X), x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧ P V)
    (hlocal : ∀ U, P U → ∀ n < (1 : ℤ),
      Subsingleton (ShiftedHom (DerivedCategory.Q.obj (restrictComplex Rc K U))
        (DerivedCategory.Q.obj (restrictComplex Rc (I⟦(q : ℤ)⟧) U)) n)) :
    Subsingleton (ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I) (q : ℤ)) :=
  (Equiv.subsingleton_congr (Iso.homCongr (Iso.refl _)
    ((DerivedCategory.Q.commShiftIso (q : ℤ)).app I))).mp
    (subsingleton_hom_of_isGE_sheafHomComplex Rc K (I⟦(q : ℤ)⟧)
      (isGE_sheafHomComplex_of_locally_subsingleton Rc K (I⟦(q : ℤ)⟧) 1 P hP hlocal))

/-- **Local to global for `Ext`, on a ringed space.** Let `N` and `E` be `𝒪_X`-modules. If on a
family of opens which is a basis near every point there is no degree-`k` morphism, for every
`k ≤ q`, between the restrictions of `N` and `E` to the slice site over that open, then there is
no degree-`q` morphism from `N` to `E`.

This is the reduction "it suffices to prove the vanishing locally on `X`", which is step 1 of the
proof of [Stacks, Tag 0G5I]. -/
theorem subsingleton_shiftedHom_single_of_locally_over
    (N E : StructureSheafModules Rc) (q : ℕ) (P : Opens X → Prop)
    (hP : ∀ (x : X) (U : Opens X), x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧ P V)
    (hlocal : ∀ U, P U → ∀ k : ℤ, k ≤ q →
      Subsingleton (ShiftedHom
        ((DerivedCategory.singleFunctor _ 0).obj
          ((_root_.SheafOfModules.overFunctor (structureSheaf Rc) U).obj N))
        ((DerivedCategory.singleFunctor _ 0).obj
          ((_root_.SheafOfModules.overFunctor (structureSheaf Rc) U).obj E)) k)) :
    Subsingleton (ShiftedHom ((DerivedCategory.singleFunctor (StructureSheafModules Rc) 0).obj N)
      ((DerivedCategory.singleFunctor (StructureSheafModules Rc) 0).obj E) (q : ℤ)) := by
  let K : CochainComplex (StructureSheafModules Rc) ℤ :=
    (CochainComplex.singleFunctor (StructureSheafModules Rc) 0).obj N
  obtain ⟨R, -, hRGE⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE (0 : ℤ)
    ((CochainComplex.singleFunctor (StructureSheafModules Rc) 0).obj E)
  have hinj : ∀ n, Injective (R.cocomplex.X n) := R.injective
  have hstrict : R.cocomplex.IsStrictlyGE 0 := hRGE
  have _ : R.cocomplex.IsKInjective := CochainComplex.isKInjective_of_injective R.cocomplex 0
  have _ : QuasiIso R.ι := R.quasiIso
  let eM : DerivedCategory.Q.obj R.cocomplex ≅
      (DerivedCategory.singleFunctor (StructureSheafModules Rc) 0).obj E :=
    (asIso (DerivedCategory.Q.map R.ι)).symm
  have hloc : ∀ U : Opens X, P U → ∀ n < (1 : ℤ),
      Subsingleton (ShiftedHom (DerivedCategory.Q.obj (restrictComplex Rc K U))
        (DerivedCategory.Q.obj (restrictComplex Rc (R.cocomplex⟦(q : ℤ)⟧) U)) n) := by
    intro U hU n hn
    let F := _root_.SheafOfModules.overFunctor (structureSheaf Rc) U
    let _ : PreservesFiniteLimits F := LocalCokernel.overFunctor_preservesFiniteLimits U
    let _ : PreservesFiniteColimits F := LocalCokernel.overFunctor_preservesFiniteColimits U
    let _ : F.Additive := ⟨fun {_ _} _ _ => rfl⟩
    let eN := mapComplexSingleIso F K N (Iso.refl _)
    let eI := mapComplexSingleIso F R.cocomplex E eM
    let eIq : DerivedCategory.Q.obj (restrictComplex Rc (R.cocomplex⟦(q : ℤ)⟧) U) ≅
        ((DerivedCategory.singleFunctor _ 0).obj (F.obj E))⟦(q : ℤ)⟧ :=
      DerivedCategory.Q.mapIso
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (q : ℤ)).app
            R.cocomplex) ≪≫
        (DerivedCategory.Q.commShiftIso (q : ℤ)).app _ ≪≫
        (shiftFunctor _ (q : ℤ)).mapIso eI
    exact (Equiv.subsingleton_congr (Iso.homCongr eN
      ((shiftFunctor _ n).mapIso eIq ≪≫
        ((shiftFunctorAdd' _ (q : ℤ) n ((q : ℤ) + n) rfl).app
          ((DerivedCategory.singleFunctor _ 0).obj (F.obj E))).symm))).mpr
      (hlocal U hU ((q : ℤ) + n) (by omega))
  exact (Equiv.subsingleton_congr (Iso.homCongr (Iso.refl _)
    ((shiftFunctor _ (q : ℤ)).mapIso eM))).mp
    (subsingleton_shiftedHom_of_locally_subsingleton Rc K R.cocomplex q P hP hloc)

end Global

/-! ### Local to global for `Ext` on a scheme -/

section SchemeCase

-- `_root_` is needed: inside `namespace Stacks.SheafOfModules` an unqualified
-- `open AlgebraicGeometry` picks up `Stacks.AlgebraicGeometry` instead.
open _root_.AlgebraicGeometry

attribute [local instance]
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

variable (X : Scheme.{u})

/-- Restriction to the slice site over an open, as a functor on `𝒪_X`-modules, is additive. -/
instance overFunctor_additive (U : X.Opens) :
    (_root_.SheafOfModules.overFunctor X.ringCatSheaf U).Additive :=
  ⟨fun {_ _} _ _ => rfl⟩

/-- The equivalence between modules on the slice site over `U` and `𝒪_U`-modules is additive. -/
instance overEquiv_functor_additive (U : X.Opens) :
    (Scheme.Modules.overEquiv U).functor.Additive :=
  Functor.additive_of_preserves_binary_products (Scheme.Modules.overEquiv U).functor

/-- The inverse equivalence is additive. -/
instance overEquiv_inverse_additive (U : X.Opens) :
    (Scheme.Modules.overEquiv U).inverse.Additive :=
  Functor.additive_of_preserves_binary_products (Scheme.Modules.overEquiv U).inverse

/-- Degree-`m` morphisms in the derived category out of a module placed in degree zero on the
slice site over `U` are the ones on the open subscheme `U`. -/
theorem subsingleton_shiftedHom_over_of_restrict (U : X.Opens) (N E : X.Modules) (m : ℤ)
    (h : Subsingleton (ShiftedHom
      ((DerivedCategory.singleFunctor U.toScheme.Modules 0).obj (N.restrict U.ι))
      ((DerivedCategory.singleFunctor U.toScheme.Modules 0).obj (E.restrict U.ι)) m)) :
    Subsingleton (ShiftedHom
      ((DerivedCategory.singleFunctor _ 0).obj
        ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).obj N))
      ((DerivedCategory.singleFunctor _ 0).obj
        ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).obj E)) m) := by
  refine subsingleton_shiftedHom_of_equivalence (Scheme.Modules.overEquiv U) _ _ m ?_
  let e := Scheme.Modules.overEquiv U
  let eM (M : X.Modules) := (e.functor.mapDerivedCategorySingleFunctor 0).app
      ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).obj M) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso ((Scheme.Modules.overFunctorEquiv U).app M)
  exact (Equiv.subsingleton_congr
    (Iso.homCongr (eM N) ((shiftFunctor _ m).mapIso (eM E)))).mpr h

/-- **Local to global vanishing of `Ext` on a scheme.** Let `N` and `E` be `𝒪_X`-modules and let
`q` be a natural number. If the opens `V` on which `Ext^n(N|_V, E|_V)` vanishes for every `n ≤ q`
form a family which is a basis near every point of `X`, then `Ext^q(N, E)` vanishes.

This is the reduction "it suffices to prove the vanishing locally on `X`", which is step 1 of the
proof of [Stacks, Tag 0G5I]. -/
theorem subsingleton_shiftedHom_single_of_locally_restrict
    (N E : X.Modules) (q : ℕ) (P : X.Opens → Prop)
    (hP : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧ P V)
    (hlocal : ∀ U, P U → ∀ n : ℕ, n ≤ q →
      Subsingleton (ShiftedHom
        ((DerivedCategory.singleFunctor U.toScheme.Modules 0).obj (N.restrict U.ι))
        ((DerivedCategory.singleFunctor U.toScheme.Modules 0).obj (E.restrict U.ι)) (n : ℤ))) :
    Subsingleton (ShiftedHom ((DerivedCategory.singleFunctor X.Modules 0).obj N)
      ((DerivedCategory.singleFunctor X.Modules 0).obj E) (q : ℤ)) := by
  have _ : (Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive :=
    Tensor.sheafTensor_additive.{u, u, u, u, u} (J := Opens.grothendieckTopology (X : TopCat.{u}))
      X.sheaf
  have _ : ∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj A).Additive :=
    Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
      (J := Opens.grothendieckTopology (X : TopCat.{u})) X.sheaf
  have _ : ∀ K₁ K₂ : CochainComplex
      (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ,
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.sheaf)
        (ComplexShape.up ℤ) := fun K₁ K₂ =>
    Tensor.hasMapBifunctor_sheafTensor (J := Opens.grothendieckTopology (X : TopCat.{u}))
      X.sheaf K₁ K₂
  refine subsingleton_shiftedHom_single_of_locally_over X.sheaf N E q P hP fun U hU k hk => ?_
  rcases lt_or_ge k 0 with hneg | hpos
  · exact subsingleton_shiftedHom_single_of_neg _ _ _ hneg
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    exact subsingleton_shiftedHom_over_of_restrict X U N E m (hlocal U hU m (by omega))

end SchemeCase

end Stacks.SheafOfModules

end
