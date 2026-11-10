module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ClosedBiduality
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDuality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLocality.InvertibilityOnACovering
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Coherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSourceTriangulated
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentationSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated

/-!
# Duality on a ringed site that is étale-locally the étale site of an affine Noetherian scheme

Let `(C, O)` be a ringed site and `K` an object of `D(O)`. Suppose given a family of objects
`V i` of `C` covering the final object, and, over each slice site `C/V i`, a *duality chart*:
an affine Noetherian scheme `T`, a dualizing complex `ω` on `T`, and an exact functor
`ε^* : Mod(𝒪_T) ⥤ Mod(O|_{V i})` which is an equivalence from `D_QCoh(𝒪_T)` onto the objects
of `D(O|_{V i})` with quasi-coherent cohomology, matches coherence, carries `ω` to `K|_{V i}`
and carries `R𝓗om_{𝒪_T}(-, ω)` to `R𝓗om(-, K|_{V i})` on `D_Coh(𝒪_T)`.

Then `K` lies in `D_Coh(O)`, `D = R𝓗om(-, K)` preserves `D_Coh(O)`, and the biduality
morphism `L ⟶ D(D(L))` is an isomorphism for every `L` in `D_Coh(O)`. This is the shape of the
proof of Stacks 0E51: for an algebraic space `X`, the slices of the small étale site at the
affine étale charts are the small étale sites of affine Noetherian schemes, on which Stacks
0A89 and Stacks 0E50 hold.

## The argument

Every claim is local on the covering, by the comparison of Stacks 08JB of the derived internal
Hom with restriction to a slice. Coherence of `D(L)` and the vanishing statements are read on
each chart, where they become the corresponding statements of Stacks 0A89 on `T`.

For the biduality morphism `β_L : L ⟶ D(D(L))` no compatibility of `β` with restriction is
used. The triangle identity `β_{D(L)} ≫ D(β_L) = 𝟙` makes `D(β_L)` a split epimorphism from
`D(D(D(L)))` onto `D(L)`; over each chart both are the image of one object of `D_Coh(𝒪_T)`,
and a split epimorphism from an object of `D_Coh(𝒪_T)` to an isomorphic one is an isomorphism,
because a surjective endomorphism of a finite module is injective. So `D(β_L)` is an
isomorphism, and since `D` reflects isomorphisms on `D_Coh(O)` (again read on the charts) so is
`β_L`.

## Main definitions

* `AlgebraicGeometry.RingedSite.coherentDerived`: `D_Coh(O)`, the objects whose cohomology
  sheaves are quasi-coherent and coherent.
* `AlgebraicGeometry.RingedSite.DualityChart`: a duality chart.

## Main results

* `AlgebraicGeometry.RingedSite.coherentDerived_of_charts`,
  `AlgebraicGeometry.RingedSite.coherentDerived_derivedDualInto_of_charts` and
  `AlgebraicGeometry.RingedSite.isIso_derivedBiduality_of_charts`.

## References

* [Stacks Project, Tag 0E51](https://stacks.math.columbia.edu/tag/0E51)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

/-! ### Affine Noetherian schemes -/

/-- `D(𝒪_T)` at the standard model, the model at which Stacks 0A89 is stated. -/
abbrev SchemeStdDerived (T : Scheme.{u}) : Type (u + 1) :=
  @DerivedCategory T.Modules _ _ (HasDerivedCategory.standard _)

/-- The cohomology sheaves on `D(𝒪_T)` at the standard model. -/
abbrev schemeStdHomology (T : Scheme.{u}) (n : ℤ) : SchemeStdDerived T ⥤ T.Modules :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n

/-- `R𝓗om_{𝒪_T}(X, ω)`. -/
abbrev schemeDual (T : Scheme.{u}) (ω X : SchemeStdDerived T) : SchemeStdDerived T :=
  ((Stacks.SheafOfModules.derivedSheafHom T.sheaf).obj (op X)).obj ω

/-- An object of `D(𝒪_T)` has coherent cohomology sheaves. -/
def SchemeCoherent (T : Scheme.{u}) (X : SchemeStdDerived T) : Prop :=
  ∀ n : ℤ, ((schemeStdHomology T n).obj X).IsCoherent

/-- An object with coherent cohomology sheaves has quasi-coherent cohomology sheaves. -/
private theorem isQuasicoherent_homology_of_schemeCoherent {T : Scheme.{u}}
    [IsLocallyNoetherian T] {X : SchemeStdDerived T} (hX : SchemeCoherent T X) (n : ℤ) :
    ((schemeStdHomology T n).obj X).IsQuasicoherent :=
  have := hX n
  isQuasicoherent_of_isCoherent _

/-- A split epimorphism from an object of `D_Coh(𝒪_T)` to itself is an isomorphism, on an
affine Noetherian scheme `T`. On cohomology it is a split epimorphism of coherent modules; on
global sections it is a surjective endomorphism of a finite module, hence injective, and a
morphism of quasi-coherent modules on an affine scheme which is bijective on global sections is
invertible. -/
theorem isIso_of_isSplitEpi_of_schemeCoherent {T : Scheme.{u}} [IsAffine T] [IsNoetherian T]
    {X : SchemeStdDerived T} (hX : SchemeCoherent T X) (r : X ⟶ X) [IsSplitEpi r] :
    IsIso r := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  rw [DerivedCategory.isIso_iff]
  intro n
  let M := (schemeStdHomology T n).obj X
  let e : M ⟶ M := (schemeStdHomology T n).map r
  have hs : IsSplitEpi e := inferInstanceAs (IsSplitEpi ((schemeStdHomology T n).map r))
  have hcoh : M.IsCoherent := hX n
  have : M.IsQuasicoherent := isQuasicoherent_homology_of_schemeCoherent hX n
  have : M.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have : Module.Finite Γ(T, ⊤) Γ(M, ⊤) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections M (isAffineOpen_top T)
  let f : Γ(M, ⊤) →ₗ[Γ(T, ⊤)] Γ(M, ⊤) :=
    { toFun := e.app ⊤
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => Scheme.Modules.Hom.app_smul e a x }
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨(section_ e).app ⊤ y, ?_⟩
    change (((section_ e) ≫ e).app ⊤) y = y
    rw [IsSplitEpi.id e]
    rfl
  exact Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top e
    ((ConcreteCategory.isIso_iff_bijective _).mpr
      (OrzechProperty.bijective_of_surjective_endomorphism f hsurj))

/-- A dualizing complex on a locally Noetherian scheme has coherent cohomology (Stacks 0A89). -/
theorem schemeCoherent_of_isDualizingComplex {T : Scheme.{u}} [IsLocallyNoetherian T]
    {ω : SchemeStdDerived T}
    (hω : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) :
    SchemeCoherent T ω :=
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  Stacks.Duality.mem_coherentDerivedCategory_of_isDualizingComplex T hω

/-- The dual of an object with coherent cohomology has coherent cohomology (Stacks 0A89). -/
theorem schemeCoherent_schemeDual {T : Scheme.{u}} [IsLocallyNoetherian T]
    {ω : SchemeStdDerived T}
    (hω : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) {X : SchemeStdDerived T}
    (hX : SchemeCoherent T X) : SchemeCoherent T (schemeDual T ω X) :=
  fun n => Stacks.Duality.isCoherent_homology_derivedSheafHom_of_isDualizingComplex hω hX n

/-- **Biduality on a locally Noetherian scheme** (Stacks 0A89): `X ≅ R𝓗om(R𝓗om(X, ω), ω)` for
`X` with coherent cohomology. -/
def schemeBidualityIso {T : Scheme.{u}} [IsLocallyNoetherian T]
    {ω : SchemeStdDerived T}
    (hω : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) {X : SchemeStdDerived T}
    (hX : SchemeCoherent T X) : X ≅ schemeDual T ω (schemeDual T ω X) :=
  @asIso _ _ _ _ (RingedSite.derivedBiduality (Stacks.SheafOfModules.ringedSite T.sheaf) ω X)
    (Stacks.Duality.isIso_derivedBiduality_of_isDualizingComplex ω X hω hX)

/-- `D_Coh(𝒪_T)` is closed under cones on a locally Noetherian scheme: coherent modules form a
weak Serre subcategory (Stacks 01BY). -/
theorem schemeCoherent_obj₃ {T : Scheme.{u}} [IsLocallyNoetherian T]
    (Tr : Triangle (SchemeStdDerived T))
    (hTr : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Tr ∈ distTriang (SchemeStdDerived T))
    (h₁ : SchemeCoherent T Tr.obj₁) (h₂ : SchemeCoherent T Tr.obj₂) :
    SchemeCoherent T Tr.obj₃ := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  have : (Stacks.Duality.isCoherentSheaf T).IsWeakSerreClass := by
    rw [show Stacks.Duality.isCoherentSheaf T =
        Stacks.SheafOfModules.coherentModules T.ringCatSheaf from
      AlgebraicGeometry.CoherentAbelian.coherentModules_eq]
    exact Stacks.SheafOfModules.coherentModules_isWeakSerreClass
  have : (DerivedCategoryB.derivedCategoryB (Stacks.Duality.isCoherentSheaf T)).IsTriangulated :=
    DerivedCategoryB.isTriangulated_derivedCategoryB _
  have := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms
    (Stacks.Duality.isCoherentSheaf T) (WeakSerre.isWeakSerre_of_isWeakSerreClass _)
  exact ObjectProperty.ext_of_isTriangulatedClosed₃
    (DerivedCategoryB.derivedCategoryB (Stacks.Duality.isCoherentSheaf T)) Tr hTr h₁ h₂

/-- The dual of a zero object is zero. -/
theorem isZero_schemeDual {T : Scheme.{u}} (ω : SchemeStdDerived T) {Z : SchemeStdDerived T}
    (hZ : IsZero Z) : IsZero (schemeDual T ω Z) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  let := HasDerivedCategory.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (Stacks.SheafOfModules.ringedSite T.sheaf).O))
  let D := (Stacks.SheafOfModules.derivedSheafHom T.sheaf).flip.obj ω
  obtain ⟨δ, hδ⟩ := @RingedSite.exists_distinguished_derivedSheafHom
    (Stacks.SheafOfModules.ringedSite T.sheaf) _ (HasDerivedCategory.standard _) ω _
    (contractible_distinguished Z)
  have h0 : IsZero (D.obj (op (contractibleTriangle Z).obj₃)) :=
    (Triangle.isZero₁_iff_isIso₂ _ hδ).2 (D.mapIso (Iso.refl _)).isIso_hom
  exact h0.of_iso (D.mapIso (hZ.iso (isZero_zero _)).op).symm

/-! ### Ringed sites -/

variable (Y : RingedSite.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **`D_Coh(O)`** on a ringed site: the objects of `D(O)` all of whose cohomology sheaves are of
finite presentation. On the small étale site of a locally Noetherian algebraic space, whose
structure sheaf is coherent, these are exactly the coherent modules. -/
def coherentDerived : ObjectProperty (StdDerived Y) :=
  fun L => ∀ n : ℤ, ((stdHomology Y n).obj L).IsFinitePresentation

/-- The functor part of a duality chart: an affine Noetherian scheme `T` and an exact functor
from `𝒪_T`-modules to `O`-modules. -/
structure ChartFunctor where
  /-- The scheme of the chart. -/
  T : Scheme.{u}
  /-- The scheme of the chart is affine. -/
  isAffine : IsAffine T
  /-- The scheme of the chart is Noetherian. -/
  isNoetherian : IsNoetherian T
  /-- The comparison of modules, `ε^*` in the application. -/
  Φ : T.Modules ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)
  /-- The comparison of modules is additive. -/
  additive : Φ.Additive
  /-- The comparison of modules preserves finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits Φ
  /-- The comparison of modules preserves finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits Φ

variable {Y} in
/-- The functor on derived categories induced by the comparison of a chart. -/
def ChartFunctor.derived (c : ChartFunctor Y) : SchemeStdDerived c.T ⥤ StdDerived Y :=
  letI := c.additive
  letI := c.preservesFiniteLimits
  letI := c.preservesFiniteColimits
  letI : HasDerivedCategory c.T.Modules := HasDerivedCategory.standard _
  letI : HasDerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :=
    HasDerivedCategory.standard _
  c.Φ.mapDerivedCategory

/-- A class of objects of `D(𝒪_T)`, one for every scheme `T`: the objects at which a duality
chart is asked to compare the duals. -/
abbrev ChartClass : Type (u + 1) := ∀ T : Scheme.{u}, SchemeStdDerived T → Prop

/-- The class of all objects. -/
def ChartClass.all : ChartClass.{u} := fun _ _ => True

/-- The class of objects with bounded cohomology sheaves. -/
def ChartClass.bounded : ChartClass.{u} := fun T X =>
  ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) → IsZero ((schemeStdHomology T i).obj X)

/-- A class of objects is *stable* when, on an affine Noetherian scheme with a dualizing complex,
it is closed under the dual of objects with coherent cohomology and under cones of morphisms
between objects with coherent cohomology. -/
structure ChartClass.IsStable (P : ChartClass.{u}) : Prop where
  /-- The dual `R𝓗om(X, ω)` of an object `X` of the class with coherent cohomology lies in the
  class. -/
  dual : ∀ {T : Scheme.{u}} [IsAffine T] [IsNoetherian T] (ω : SchemeStdDerived T)
    (_ : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω)
    {X : SchemeStdDerived T}, SchemeCoherent T X → P T X → P T (schemeDual T ω X)
  /-- The third vertex of a distinguished triangle whose first two vertices have coherent
  cohomology and lie in the class lies in the class. -/
  obj₃ : ∀ {T : Scheme.{u}} [IsAffine T] [IsNoetherian T] (Tr : Triangle (SchemeStdDerived T))
    (_ : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Tr ∈ distTriang (SchemeStdDerived T)),
    SchemeCoherent T Tr.obj₁ → SchemeCoherent T Tr.obj₂ → P T Tr.obj₁ → P T Tr.obj₂ →
      P T Tr.obj₃

/-- **A duality chart** for `K ∈ D(O)` at a class `P` of objects: a chart functor `ε^*` from an
affine Noetherian scheme `T` with a dualizing complex `ω`, such that `ε^*` is an equivalence from
`D_QCoh(𝒪_T)` onto the objects with quasi-coherent cohomology, matches quasi-coherence, coherence
and vanishing of quasi-coherent modules, carries `ω` to `K`, and carries `R𝓗om_{𝒪_T}(X, ω)` to
`R𝓗om(ε^* X, K)` for `X` in `P` with coherent cohomology. -/
structure DualityChart (K : StdDerived Y) (P : ChartClass.{u}) extends ChartFunctor Y where
  /-- The dualizing complex on the scheme of the chart. -/
  ω : SchemeStdDerived T
  /-- `ω` is a dualizing complex on `T`. -/
  isDualizing : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
    Stacks.Duality.IsDualizingComplex ω
  /-- A quasi-coherent `𝒪_T`-module is coherent if and only if its image under `ε^*` is of
  finite presentation. -/
  isCoherent_iff : ∀ M : T.Modules, M.IsQuasicoherent →
    (M.IsCoherent ↔ (Φ.obj M).IsFinitePresentation)
  /-- A quasi-coherent `𝒪_T`-module whose image under `ε^*` is zero is zero. -/
  isZero_of_isZero : ∀ M : T.Modules, M.IsQuasicoherent → IsZero (Φ.obj M) → IsZero M
  /-- Every object of `D(O)` whose cohomology sheaves are of finite presentation is isomorphic
  to the image under `ε^*` of an object of `D(𝒪_T)` with quasi-coherent cohomology. -/
  exists_iso : ∀ L : StdDerived Y,
    (∀ n : ℤ, ((stdHomology Y n).obj L).IsFinitePresentation) →
      ∃ L' : SchemeStdDerived T, (∀ n : ℤ, ((schemeStdHomology T n).obj L').IsQuasicoherent) ∧
        Nonempty (toChartFunctor.derived.obj L' ≅ L)
  /-- `ε^*` is bijective on morphisms between objects of `D(𝒪_T)` with quasi-coherent
  cohomology. -/
  map_bijective : ∀ A B : SchemeStdDerived T,
    (∀ n : ℤ, ((schemeStdHomology T n).obj A).IsQuasicoherent) →
    (∀ n : ℤ, ((schemeStdHomology T n).obj B).IsQuasicoherent) →
      Function.Bijective (fun f : A ⟶ B => toChartFunctor.derived.map f)
  /-- `ε^* ω ≅ K`. -/
  isoDualizing : Nonempty (toChartFunctor.derived.obj ω ≅ K)
  /-- `R𝓗om(ε^* X, K) ≅ ε^* R𝓗om_{𝒪_T}(X, ω)` for `X` in `P` with coherent cohomology. -/
  dualIso : ∀ X : SchemeStdDerived T, SchemeCoherent T X → P T X →
    Nonempty (((stdSheafHom Y).obj (op (toChartFunctor.derived.obj X))).obj K ≅
      toChartFunctor.derived.obj (schemeDual T ω X))

variable {Y} in
/-- A duality chart for `K` is one for every object isomorphic to `K`. -/
def DualityChart.ofIso {K K' : StdDerived Y} {P : ChartClass.{u}} (c : DualityChart Y K P)
    (e : K ≅ K') : DualityChart Y K' P where
  toChartFunctor := c.toChartFunctor
  ω := c.ω
  isDualizing := c.isDualizing
  isCoherent_iff := c.isCoherent_iff
  isZero_of_isZero := c.isZero_of_isZero
  exists_iso := c.exists_iso
  map_bijective := c.map_bijective
  isoDualizing := c.isoDualizing.map (· ≪≫ e)
  dualIso X hX hP :=
    (c.dualIso X hX hP).map (((stdSheafHom Y).obj (op (c.derived.obj X))).mapIso e.symm ≪≫ ·)

/-! ### Restriction to a slice -/

/-- Restriction `Mod(O) ⥤ Mod(O|_U)` to the slice site over `U`, with target spelled as the
modules of the ringed site `Y.over U`. -/
abbrev restrictModules (U : Y.C) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O) :=
  SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) U

/-- Restriction `D(O) ⥤ D(O|_U)` to the slice site over `U`, at the standard models. -/
abbrev stdRestrict (U : Y.C) : StdDerived Y ⥤ StdDerived (Y.over U) :=
  letI : HasDerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O).over U)) :=
    HasDerivedCategory.standard _
  (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) U).mapDerivedCategory

/-- Restriction of modules to a slice is additive. -/
instance restrictModules_additive (U : Y.C) : (restrictModules Y U).Additive :=
  inferInstanceAs
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) U).Additive

/-- Restriction of modules to a slice preserves finite limits. -/
instance restrictModules_preservesFiniteLimits (U : Y.C) :
    PreservesFiniteLimits (restrictModules Y U) :=
  inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) U))

/-- Restriction of modules to a slice preserves finite colimits. -/
instance restrictModules_preservesFiniteColimits (U : Y.C) :
    PreservesFiniteColimits (restrictModules Y U) :=
  inferInstanceAs (PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) U))

/-- Restriction to a slice after the derived functor of an exact functor `G` is the derived
functor of `G` followed by restriction. -/
def stdRestrictCompIso (U : Y.C) {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (G : A ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O))
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    letI : HasDerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) :=
      HasDerivedCategory.standard _
    G.mapDerivedCategory ⋙ stdRestrict Y U ≅ (G ⋙ restrictModules Y U).mapDerivedCategory :=
  letI : HasDerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O).over U)) :=
    HasDerivedCategory.standard _
  Stacks.DerivedFunctor.mapDerivedCategoryCompIso G
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) U)

/-- The cohomology sheaves of a restriction are the restrictions of the cohomology sheaves. -/
def stdRestrictHomologyIso (U : Y.C) (n : ℤ) (L : StdDerived Y) :
    (stdHomology (Y.over U) n).obj ((stdRestrict Y U).obj L) ≅
      ((stdHomology Y n).obj L).over U :=
  letI : HasDerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O).over U)) :=
    HasDerivedCategory.standard _
  ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    U).mapDerivedCategoryHomologyIso n).app L

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- Vanishing in `D(O)` is local on a covering family. -/
theorem isZero_of_isZero_stdRestrict {ι : Type*} {V : ι → Y.C} (hV : Y.J.CoversTop V)
    (L : StdDerived Y) (h : ∀ i, IsZero ((stdRestrict Y (V i)).obj L)) : IsZero L := by
  let : HasDerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :=
    HasDerivedCategory.standard _
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  refine Stacks.SheafOfModules.isZero_of_coversTop hV _ fun i => ?_
  exact (Functor.map_isZero (stdHomology (Y.over (V i)) n) (h i)).of_iso
    (stdRestrictHomologyIso Y (V i) n L).symm

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- A morphism of `D(O)` is an isomorphism as soon as its restrictions to the members of a covering
family are. -/
theorem isIso_of_isIso_stdRestrict {ι : Type*} {V : ι → Y.C} (hV : Y.J.CoversTop V)
    {L M : StdDerived Y} (f : L ⟶ M) (h : ∀ i, IsIso ((stdRestrict Y (V i)).map f)) :
    IsIso f := by
  let : HasDerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :=
    HasDerivedCategory.standard _
  rw [DerivedCategory.isIso_iff]
  intro n
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hV _ fun i => ?_
  let : HasDerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O).over (V i))) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over (V i)).O)) :=
    HasDerivedCategory.standard _
  have := h i
  have h' : IsIso (((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (V i)).mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ n).map f) :=
    inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((stdRestrict Y (V i)).map f)))
  exact (NatIso.isIso_map_iff ((SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (V i)).mapDerivedCategoryHomologyIso n) f).1 h'

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The restriction of an object of `D_Coh(O)` to a slice lies in `D_Coh` of the slice. -/
theorem coherentDerived_stdRestrict (U : Y.C) {L : StdDerived Y} (hL : coherentDerived Y L) :
    coherentDerived (Y.over U) ((stdRestrict Y U).obj L) := fun n =>
  Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    (stdRestrictHomologyIso Y U n L).symm
    (Stacks.SheafOfModules.isFinitePresentation_over _ (hL n) U)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- `D_Coh(O)` is local on a covering family. -/
theorem coherentDerived_of_stdRestrict {ι : Type u} {V : ι → Y.C} (hV : Y.J.CoversTop V)
    {L : StdDerived Y} (h : ∀ i, coherentDerived (Y.over (V i)) ((stdRestrict Y (V i)).obj L)) :
    coherentDerived Y L := fun n =>
  (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_isFinitePresentation.{u, u, u}
    _).2
    ⟨ι, V, hV, fun i => Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      (stdRestrictHomologyIso Y (V i) n L) (h i n)⟩

variable {Y} in
/-- The cohomology sheaves of the image of an object under the functor of a chart. -/
def ChartFunctor.derivedHomologyIso (c : ChartFunctor Y) (n : ℤ) (X : SchemeStdDerived c.T) :
    (stdHomology Y n).obj (c.derived.obj X) ≅ c.Φ.obj ((schemeStdHomology c.T n).obj X) :=
  letI := c.additive
  letI := c.preservesFiniteLimits
  letI := c.preservesFiniteColimits
  letI : HasDerivedCategory c.T.Modules := HasDerivedCategory.standard _
  letI : HasDerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :=
    HasDerivedCategory.standard _
  (c.Φ.mapDerivedCategoryHomologyIso n).app X

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- **Every object of `D_Coh` over a chart is the image of an object of `D_Coh(𝒪_T)`.** -/
theorem DualityChart.exists_coherent_model {K : StdDerived Y} {P : ChartClass.{u}}
    (c : DualityChart Y K P)
    (M : StdDerived Y) (hM : coherentDerived Y M) :
    ∃ M' : SchemeStdDerived c.T, SchemeCoherent c.T M' ∧
      (∀ n : ℤ, ((schemeStdHomology c.T n).obj M').IsQuasicoherent) ∧
        Nonempty (c.derived.obj M' ≅ M) := by
  obtain ⟨M', hq, ⟨e⟩⟩ := c.exists_iso M hM
  refine ⟨M', fun n => ?_, hq, ⟨e⟩⟩
  refine (c.isCoherent_iff _ (hq n)).2 ?_
  exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    ((stdHomology Y n).mapIso e.symm ≪≫ c.derivedHomologyIso n M') (hM n)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- `D_Coh(O)` is closed under isomorphisms. -/
theorem coherentDerived_of_iso {L M : StdDerived Y} (e : L ≅ M) (hL : coherentDerived Y L) :
    coherentDerived Y M := fun n =>
  Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso ((stdHomology Y n).mapIso e)
    (hL n)

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The image under a chart of an object of `D_Coh(𝒪_T)` lies in `D_Coh`. -/
theorem DualityChart.coherentDerived_derived {K : StdDerived Y} {P : ChartClass.{u}}
    (c : DualityChart Y K P)
    {X : SchemeStdDerived c.T} (hX : SchemeCoherent c.T X) :
    coherentDerived Y (c.derived.obj X) := by
  have := c.isNoetherian
  intro n
  exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    (c.derivedHomologyIso n X).symm
    ((c.isCoherent_iff _ (isQuasicoherent_homology_of_schemeCoherent hX n)).1 (hX n))

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The functor of a chart reflects vanishing on objects with quasi-coherent cohomology. -/
theorem DualityChart.isZero_of_isZero_derived {K : StdDerived Y} {P : ChartClass.{u}}
    (c : DualityChart Y K P)
    {X : SchemeStdDerived c.T} (hX : ∀ n : ℤ, ((schemeStdHomology c.T n).obj X).IsQuasicoherent)
    (h : IsZero (c.derived.obj X)) : IsZero X := by
  let : HasDerivedCategory c.T.Modules := HasDerivedCategory.standard _
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  exact c.isZero_of_isZero _ (hX n)
    ((Functor.map_isZero (stdHomology Y n) h).of_iso (c.derivedHomologyIso n X).symm)

section Slices

variable [∀ U : Y.C, HasSheafify (Y.over U).J AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)]

variable {Y} in
/-- An object `M` of `D(O)` is *modelled in `P`* by a chart when it is `ε^*` of an object of `P`
with coherent and quasi-coherent cohomology sheaves. -/
def DualityChart.Models {K : StdDerived Y} {P : ChartClass.{u}} (c : DualityChart Y K P)
    (M : StdDerived Y) : Prop :=
  ∃ M' : SchemeStdDerived c.T, SchemeCoherent c.T M' ∧ P c.T M' ∧
    (∀ n : ℤ, ((schemeStdHomology c.T n).obj M').IsQuasicoherent) ∧
      Nonempty (c.derived.obj M' ≅ M)

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, HasSheafify (Y.over U).J AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- Being modelled by a chart only depends on its chart functor. -/
theorem DualityChart.models_ofIso {K K' : StdDerived Y} {P : ChartClass.{u}}
    (c : DualityChart Y K P) (e : K ≅ K') (M : StdDerived Y) :
    (c.ofIso e).Models M ↔ c.Models M :=
  Iff.rfl

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, HasSheafify (Y.over U).J AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- The image under a chart of an object of the class with coherent, quasi-coherent cohomology is
modelled by the chart. -/
theorem DualityChart.models_derived {K : StdDerived Y} {P : ChartClass.{u}}
    (c : DualityChart Y K P) {M' : SchemeStdDerived c.T} (h₁ : SchemeCoherent c.T M')
    (h₂ : P c.T M') (h₃ : ∀ n : ℤ, ((schemeStdHomology c.T n).obj M').IsQuasicoherent) :
    c.Models (c.derived.obj M') :=
  ⟨M', h₁, h₂, h₃, ⟨Iso.refl _⟩⟩

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, HasSheafify (Y.over U).J AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- Being modelled by a chart is invariant under isomorphism. -/
theorem DualityChart.models_of_iso {K : StdDerived Y} {P : ChartClass.{u}}
    (c : DualityChart Y K P) {M M' : StdDerived Y} (h : c.Models M) (e : M ≅ M') :
    c.Models M' := by
  obtain ⟨L', h₁, h₂, h₃, ⟨d⟩⟩ := h
  exact ⟨L', h₁, h₂, h₃, ⟨d ≪≫ e⟩⟩

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, HasSheafify (Y.over U).J AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- At the class of all objects, every object of `D_Coh` is modelled by a chart. -/
theorem DualityChart.models_of_coherentDerived {K : StdDerived Y}
    (c : DualityChart Y K ChartClass.all) {M : StdDerived Y} (hM : coherentDerived Y M) :
    c.Models M := by
  obtain ⟨M', h₁, h₂, h₃⟩ := c.exists_coherent_model M hM
  exact ⟨M', h₁, trivial, h₂, h₃⟩

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, HasSheafify (Y.over U).J AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- An object modelled by a chart lies in `D_Coh`. -/
theorem DualityChart.coherentDerived_of_models {K : StdDerived Y} {P : ChartClass.{u}}
    (c : DualityChart Y K P) {M : StdDerived Y} (hM : c.Models M) : coherentDerived Y M := by
  obtain ⟨M', h₁, -, -, ⟨e⟩⟩ := hM
  exact coherentDerived_of_iso _ e (c.coherentDerived_derived h₁)

/-- The class of all objects is stable. -/
theorem ChartClass.all_isStable : ChartClass.IsStable ChartClass.all.{u} where
  dual := by intros; trivial
  obj₃ := by intros; trivial

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- **The derived dual over a chart.** If `ε^* A' ≅ A|_U` with `A'` in `D_Coh(𝒪_T)`, then
`R𝓗om(A, K)|_U ≅ ε^* R𝓗om_{𝒪_T}(A', ω)`: restriction to the slice commutes with the derived
internal Hom (Stacks 08JB), and the chart carries the dual of `𝒪_T` to the dual over `U`. -/
theorem DualityChart.restrict_dual_iso {U : Y.C} {K : StdDerived Y} {P : ChartClass.{u}}
    (c : DualityChart (Y.over U) ((stdRestrict Y U).obj K) P) {A : StdDerived Y}
    {A' : SchemeStdDerived c.T} (hA' : SchemeCoherent c.T A') (hP : P c.T A')
    (e : c.derived.obj A' ≅ (stdRestrict Y U).obj A) :
    Nonempty ((stdRestrict Y U).obj (((stdSheafHom Y).obj (op A)).obj K) ≅
      c.derived.obj (schemeDual c.T c.ω A')) := by
  obtain ⟨d⟩ := c.dualIso A' hA' hP
  exact ⟨(derivedHomRestriction Y U).iso A K ≪≫
    ((stdSheafHom (Y.over U)).mapIso e.op).app ((stdRestrict Y U).obj K) ≪≫ d⟩

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, HasSheafify (Y.over U).J AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- **A dualizing complex is in `D_Coh`**, read on the charts. -/
theorem coherentDerived_of_charts {ι : Type u} {V : ι → Y.C} (hV : Y.J.CoversTop V)
    {K : StdDerived Y} {P : ChartClass.{u}}
    (c : ∀ i, DualityChart (Y.over (V i)) ((stdRestrict Y (V i)).obj K) P) :
    coherentDerived Y K := by
  refine coherentDerived_of_stdRestrict Y hV fun i => ?_
  have := (c i).isNoetherian
  obtain ⟨e⟩ := (c i).isoDualizing
  exact coherentDerived_of_iso _ e
    ((c i).coherentDerived_derived (schemeCoherent_of_isDualizingComplex (c i).isDualizing))

variable {Y} in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- **The dual of a modelled object is modelled**: `R𝓗om(L, K)|_U ≅ ε^* R𝓗om_{𝒪_T}(L', ω)`. -/
theorem DualityChart.models_dual {U : Y.C} {K : StdDerived Y} {P : ChartClass.{u}}
    (hP : ChartClass.IsStable P) (c : DualityChart (Y.over U) ((stdRestrict Y U).obj K) P)
    {L : StdDerived Y} (hL : c.Models ((stdRestrict Y U).obj L)) :
    c.Models ((stdRestrict Y U).obj (((stdSheafHom Y).obj (op L)).obj K)) := by
  have := c.isNoetherian
  have := c.isAffine
  obtain ⟨L', hL', hPL, -, ⟨e⟩⟩ := hL
  obtain ⟨d⟩ := c.restrict_dual_iso hL' hPL e
  have h₁ := schemeCoherent_schemeDual c.isDualizing hL'
  exact ⟨_, h₁, hP.dual c.ω c.isDualizing hL' hPL,
    isQuasicoherent_homology_of_schemeCoherent h₁, ⟨d.symm⟩⟩

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- **`D = R𝓗om(-, K)` carries modelled objects to `D_Coh`**, read on the charts. -/
theorem coherentDerived_dual_of_models {ι : Type u} {V : ι → Y.C} (hV : Y.J.CoversTop V)
    {K : StdDerived Y} {P : ChartClass.{u}} (hP : ChartClass.IsStable P)
    (c : ∀ i, DualityChart (Y.over (V i)) ((stdRestrict Y (V i)).obj K) P)
    {L : StdDerived Y} (hL : ∀ i, (c i).Models ((stdRestrict Y (V i)).obj L)) :
    coherentDerived Y (((stdSheafHom Y).obj (op L)).obj K) :=
  coherentDerived_of_stdRestrict Y hV fun i =>
    (c i).coherentDerived_of_models ((c i).models_dual hP (hL i))

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- **`D = R𝓗om(-, K)` preserves `D_Coh`**, read on the charts. -/
theorem coherentDerived_dual_of_charts {ι : Type u} {V : ι → Y.C} (hV : Y.J.CoversTop V)
    {K : StdDerived Y}
    (c : ∀ i, DualityChart (Y.over (V i)) ((stdRestrict Y (V i)).obj K) ChartClass.all)
    {L : StdDerived Y} (hL : coherentDerived Y L) :
    coherentDerived Y (((stdSheafHom Y).obj (op L)).obj K) :=
  coherentDerived_dual_of_models Y hV ChartClass.all_isStable c fun i =>
    (c i).models_of_coherentDerived (coherentDerived_stdRestrict Y (V i) hL)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- **A split epimorphism `D(D(D(L))) ⟶ D(L)` is an isomorphism** for `L` modelled on the
charts: over each chart both objects are `ε^*` of `R𝓗om_{𝒪_T}(L', ω)`, and a split epimorphism
of an object of `D_Coh(𝒪_T)` onto itself is an isomorphism. -/
theorem isIso_of_isSplitEpi_dual_of_models {ι : Type u} {V : ι → Y.C} (hV : Y.J.CoversTop V)
    {K : StdDerived Y} {P : ChartClass.{u}} (hP : ChartClass.IsStable P)
    (c : ∀ i, DualityChart (Y.over (V i)) ((stdRestrict Y (V i)).obj K) P)
    {L : StdDerived Y} (hL : ∀ i, (c i).Models ((stdRestrict Y (V i)).obj L))
    (r : ((stdSheafHom Y).obj (op (((stdSheafHom Y).obj (op
        (((stdSheafHom Y).obj (op L)).obj K))).obj K))).obj K ⟶ ((stdSheafHom Y).obj (op L)).obj K)
    [IsSplitEpi r] : IsIso r := by
  refine isIso_of_isIso_stdRestrict Y hV r fun i => ?_
  have := (c i).isNoetherian
  have := (c i).isAffine
  have hω := (c i).isDualizing
  obtain ⟨L', hL', hPL, -, ⟨e⟩⟩ := hL i
  obtain ⟨d₁⟩ := (c i).restrict_dual_iso hL' hPL e
  have h₁ := schemeCoherent_schemeDual hω hL'
  have hP₁ := hP.dual (c i).ω hω hL' hPL
  obtain ⟨d₂⟩ := (c i).restrict_dual_iso h₁ hP₁ d₁.symm
  have h₂ := schemeCoherent_schemeDual hω h₁
  have hP₂ := hP.dual (c i).ω hω h₁ hP₁
  obtain ⟨d₃⟩ := (c i).restrict_dual_iso h₂ hP₂ d₂.symm
  let M := schemeDual (c i).T (c i).ω L'
  have hqM := isQuasicoherent_homology_of_schemeCoherent h₁
  let a := d₃ ≪≫ (c i).derived.mapIso (schemeBidualityIso hω h₁).symm
  let ρ := stdRestrict Y (V i)
  obtain ⟨rT, hrT⟩ := ((c i).map_bijective M M hqM hqM).2 (a.inv ≫ ρ.map r ≫ d₁.hom)
  obtain ⟨sT, hsT⟩ := ((c i).map_bijective M M hqM hqM).2
    (d₁.inv ≫ ρ.map (section_ r) ≫ a.hom)
  dsimp only at hrT hsT
  have hsr : sT ≫ rT = 𝟙 M := by
    apply ((c i).map_bijective M M hqM hqM).1
    simp only [Functor.map_comp]
    rw [hrT, hsT]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← ρ.map_comp_assoc, IsSplitEpi.id, ρ.map_id, Category.id_comp, Iso.inv_hom_id]
    exact ((c i).derived.map_id M).symm
  have : IsSplitEpi rT := IsSplitEpi.mk' ⟨sT, hsr⟩
  have := isIso_of_isSplitEpi_of_schemeCoherent h₁ rT
  have hiso : IsIso ((c i).derived.map rT) := inferInstance
  rw [hrT] at hiso
  rw [show ρ.map r = a.hom ≫ (a.inv ≫ ρ.map r ≫ d₁.hom) ≫ d₁.inv by simp]
  infer_instance

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- **`D = R𝓗om(-, K)` reflects isomorphisms between modelled objects**, read on the charts:
the cone `C` of `f : A ⟶ B` has `D(C) = 0`, over each chart `C` is `ε^*` of the cone `C'` of a
morphism between models, so `ε^* R𝓗om_{𝒪_T}(C', ω) = 0`, hence `R𝓗om_{𝒪_T}(C', ω) = 0` and
`C' = 0` by biduality on `T`. -/
theorem isIso_of_isIso_dual_of_models {ι : Type u} {V : ι → Y.C} (hV : Y.J.CoversTop V)
    {K : StdDerived Y} {P : ChartClass.{u}} (hP : ChartClass.IsStable P)
    (c : ∀ i, DualityChart (Y.over (V i)) ((stdRestrict Y (V i)).obj K) P)
    {A B : StdDerived Y} (hA : ∀ i, (c i).Models ((stdRestrict Y (V i)).obj A))
    (hB : ∀ i, (c i).Models ((stdRestrict Y (V i)).obj B)) (f : A ⟶ B)
    (hf : IsIso (((stdSheafHom Y).map f.op).app K)) : IsIso f := by
  let : HasDerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :=
    HasDerivedCategory.standard _
  obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom Y K _ hT
  have hDC : IsZero (((stdSheafHom Y).obj (op C)).obj K) :=
    (Triangle.isZero₁_iff_isIso₂ _ hδ).2 hf
  refine isZero_of_isZero_stdRestrict Y hV C fun i => ?_
  have := (c i).isNoetherian
  have := (c i).isAffine
  have hω := (c i).isDualizing
  let : HasDerivedCategory (c i).T.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O).over (V i))) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over (V i)).O)) :=
    HasDerivedCategory.standard _
  obtain ⟨A', hA', hPA, hqA, ⟨eA⟩⟩ := hA i
  obtain ⟨B', hB', hPB, hqB, ⟨eB⟩⟩ := hB i
  let := (c i).additive
  let := (c i).preservesFiniteLimits
  let := (c i).preservesFiniteColimits
  let Φ : SchemeStdDerived (c i).T ⥤ StdDerived (Y.over (V i)) := (c i).Φ.mapDerivedCategory
  let ρ : StdDerived Y ⥤ StdDerived (Y.over (V i)) :=
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (V i)).mapDerivedCategory
  obtain ⟨f', hf'⟩ := ((c i).map_bijective A' B' hqA hqB).2 (eA.hom ≫ ρ.map f ≫ eB.inv)
  dsimp only at hf'
  obtain ⟨C', g', h', hT'⟩ := Pretriangulated.distinguished_cocone_triangle f'
  have hw : (c i).derived.map f' ≫ eB.hom = eA.hom ≫ ρ.map f := by rw [hf']; simp
  obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _ (Φ.map_distinguished _ hT')
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (V i)).mapDerivedCategory.map_distinguished _ hT) (Arrow.isoMk eA eB hw.symm)
  have hC' : SchemeCoherent (c i).T C' := schemeCoherent_obj₃ _ hT' hA' hB'
  let eC : (c i).derived.obj C' ≅ (stdRestrict Y (V i)).obj C := Triangle.π₃.mapIso e
  obtain ⟨d⟩ := (c i).restrict_dual_iso hC' (hP.obj₃ _ hT' hA' hB' hPA hPB) eC
  have hz : IsZero ((c i).derived.obj (schemeDual (c i).T (c i).ω C')) :=
    (Functor.map_isZero (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (V i)).mapDerivedCategory hDC).of_iso d.symm
  have hDC' := (c i).isZero_of_isZero_derived
    (isQuasicoherent_homology_of_schemeCoherent (schemeCoherent_schemeDual hω hC')) hz
  exact (Functor.map_isZero Φ ((isZero_schemeDual (c i).ω hDC').of_iso
    (schemeBidualityIso hω hC'))).of_iso eC.symm

omit [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- **Biduality at a modelled object.** For `L` modelled in a stable class on every chart, the
biduality morphism `L ⟶ R𝓗om(R𝓗om(L, K), K)` is an isomorphism. By the triangle identity
`R𝓗om(β_L, K)` is a split epimorphism `D(D(D(L))) ⟶ D(L)`, hence an isomorphism
(`isIso_of_isSplitEpi_dual_of_models`), and `D` reflects isomorphisms between modelled objects
(`isIso_of_isIso_dual_of_models`). -/
theorem isIso_derivedBiduality_of_models {ι : Type u} {V : ι → Y.C} (hV : Y.J.CoversTop V)
    {K : StdDerived Y} {P : ChartClass.{u}} (hP : ChartClass.IsStable P)
    (c : ∀ i, DualityChart (Y.over (V i)) ((stdRestrict Y (V i)).obj K) P)
    {L : StdDerived Y} (hL : ∀ i, (c i).Models ((stdRestrict Y (V i)).obj L)) :
    IsIso (derivedBiduality Y K L) := by
  have hDDL : ∀ i, (c i).Models ((stdRestrict Y (V i)).obj
      (((stdSheafHom Y).obj (op (((stdSheafHom Y).obj (op L)).obj K))).obj K)) := fun i =>
    (c i).models_dual hP ((c i).models_dual hP (hL i))
  have : IsSplitEpi (((stdSheafHom Y).map (derivedBiduality Y K L).op).app K) :=
    IsSplitEpi.mk' ⟨_, derivedBiduality_comp_map_derivedBiduality Y K L⟩
  exact isIso_of_isIso_dual_of_models Y hV hP c hL hDDL _
    (isIso_of_isSplitEpi_dual_of_models Y hV hP c hL
      (((stdSheafHom Y).map (derivedBiduality Y K L).op).app K))

omit [∀ U : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).Additive]
  [∀ U : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over U).O).obj A).Additive]
  [∀ U : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over U).O) (ComplexShape.up ℤ)] in
/-- **Biduality on a ringed site with duality charts.** For `L` in `D_Coh(O)` the biduality
morphism `L ⟶ R𝓗om(R𝓗om(L, K), K)` is an isomorphism. -/
theorem isIso_derivedBiduality_of_charts {ι : Type u} {V : ι → Y.C} (hV : Y.J.CoversTop V)
    {K : StdDerived Y}
    (c : ∀ i, DualityChart (Y.over (V i)) ((stdRestrict Y (V i)).obj K) ChartClass.all)
    {L : StdDerived Y} (hL : coherentDerived Y L) : IsIso (derivedBiduality Y K L) :=
  isIso_derivedBiduality_of_models Y hV ChartClass.all_isStable c fun i =>
    (c i).models_of_coherentDerived (coherentDerived_stdRestrict Y (V i) hL)

end Slices

end AlgebraicGeometry.RingedSite

end
