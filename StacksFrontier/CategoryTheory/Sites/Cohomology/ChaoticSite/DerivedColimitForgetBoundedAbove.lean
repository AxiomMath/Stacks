module

public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitForgetModuleStructure

/-!
# Derived lower shriek and forgetting the module structure, for bounded above complexes

`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedColimitForgetModuleStructure.lean`
compares the two derived lower shrieks of a `B̲`-module placed in cohomological degree zero. This
file does the same for an arbitrary cochain complex of `B̲`-modules bounded above by `0`:

`forget(Lπ_!^{B}(K^•)) ≅ Lπ_!^{Ab}(forget K^•)` in `D(Ab)`, naturally in `K^•`.

The degree-zero statement does not imply this one and is not a special case of it in any usable
sense: the complexes a consumer must invert are not concentrated in a degree. The unit
`ℱ ⟶ ℱ ⊗^𝐋_𝒪 B̲` of a change of coefficients has a source with homology `Tor_n(ℱ, B)` in every
degree `n ≥ 0`, and those `Tor` being nonzero is the whole reason [Stacks, Tag 08QJ] is a theorem;
so no morphism of that shape is the image under `HomologicalComplex.single` of a morphism of
`B̲`-modules.

Both sides are computed by the total complex of the Moore bicomplex of the evaluation on a point
resolution — `Stacks.ChaoticSite.ModuleValued.totalQIsoDerivedColimitOfResolution` and
`Stacks.ChaoticSite.AbelianValued.totalQIsoDerivedColimitOfResolution`, the two derived forms of
[Stacks, Tag 08Q9] for a bounded above complex — and that bicomplex does not see the module
structure. Passing from the bicomplex to its total complex is
`HomologicalComplex₂.TotalMap.totalIso`: the total complex is a coproduct in each degree, and
forgetting the module structure preserves coproducts.

## No variance is fixed

As in the degree-zero file, the consumer-facing statement is an `IsIso ↔ IsIso` which mentions no
comparison map of its own, so there is nothing in it to orient. It applies to the derived unit of
[Stacks, Tag 08QJ] and to the counit demanded by a triangle identity alike, in either direction,
with no inverse to thread through.

## Why the universal property does not give this

The composite `Lπ_!^{B} ⋙ forget` is a left derived functor of `colim ⋙ forget` for free, by the
absoluteness of Stacks 0794
(`Stacks.CategoryHomology.isLeftDerivedFunctor_comp_of_enoughProjectives`), so the canonical
comparison exists with no hypothesis at all. Its invertibility is equivalent to the *other*
composite, `forget ⋙ Lπ_!^{Ab}`, being a left derived functor of the same functor, and that is
not formal: it would require the diagramwise forgetful functor to carry projective diagrams of
`B`-modules to `colim`-acyclic diagrams of abelian groups. It does not carry them to projective
ones — a projective `B`-module need not be projective over `ℤ`, as `B = ZMod 2` shows — so the
route that discharges every other acyclicity hypothesis in this library, namely that a bounded
above acyclic complex of projectives is K-projective and hence zero in the homotopy category, is
unavailable. The missing input would be the bounded above dual of [Stacks, Tag 05T8], which
`StacksFrontier/Algebra/Homology/DerivedCategory/AcyclicObjects.lean` explicitly declines to state.
The point resolution replaces that input.

The same obstruction blocks the two other routes to a bounded above statement: a dévissage along
triangles needs a comparison *map* of triangles, which the universal property does not supply in
the absence of that acyclicity; and killing the `Tor` terms of the source one at a time is not
available either, since [Stacks, Tag 08QJ] gives only that the total object is right.

## Main definitions

* `Stacks.ChaoticSite.mooreBicomplexForgetNatIso`: the Moore bicomplex of the underlying complex
  of abelian diagrams is the Moore bicomplex of the complex of module diagrams with the module
  structure forgotten, as an isomorphism of functors.
* `Stacks.ChaoticSite.totalMooreBicomplexForgetIso`: **the comparison** — the same after
  totalization, which is where the preservation of coproducts by the forgetful functor enters,
  with its naturality in the complex
  `Stacks.ChaoticSite.totalMooreBicomplexForgetIso_naturality`.
* `Stacks.ChaoticSite.ModuleValued.boundedAboveProjectiveResolution` and its abelian twin: the
  degreewise epimorphic projective resolution of [Stacks, Tag 0646] that the two criteria below
  are read through.

## Main results

* `Stacks.ChaoticSite.ModuleValued.isIso_totalDerivedColimit_map_iff` and
  `Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_map_iff`: derived lower shriek
  inverts a morphism of bounded above complexes exactly when the induced morphism of total Moore
  complexes is a quasi-isomorphism, at module and at abelian coefficients.
* `Stacks.ChaoticSite.isIso_totalDerivedColimit_map_forget_iff`: **the statement a consumer
  uses** — a morphism of bounded above complexes of `B̲`-modules is inverted by `Lπ_!` in `D(B)`
  exactly when the underlying morphism of complexes of abelian diagrams is inverted by `Lπ_!` in
  `D(Ab)`.

## Implementation notes

The interchange of the total complex with an additive functor is not reproved here: it is
`HomologicalComplex₂.TotalMap.totalIso` in
`StacksFrontier/Algebra/Homology/MapTotalComplex.lean`, with its naturality in the bicomplex. What
this file supplies is the identification of the two Moore bicomplexes, which is the degreewise
application of the comparison of Moore complexes from the degree-zero file, and the `HasTotal`
instance for the image bicomplex, which no lemma derives from preservation of coproducts and is
obtained here by transporting the abelian one along that identification.

**A universe pitfall in the conservativity instance used below.** Instance search for
`CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory` at
`forget₂ (ModuleCat.{v} B) AddCommGrpCat.{v}` with `B : Type w` and `v`, `w` independent fails,
with `stuck at solving universe constraint … PreservesColimits (forget₂ (ModuleCat B)
AddCommGrpCat)`: Mathlib's colimit-preservation instances for that forgetful functor are stated
at `ModuleCat.{max w w'} R`, and the mixed shape does not unify with them. It resolves at
`ModuleCat.{max v w} B` and at the `ModuleCat.{u} B`, `B : Type u` used throughout this file.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 0646](https://stacks.math.columbia.edu/tag/0646)
* [Stacks Project, Tag 0649](https://stacks.math.columbia.edu/tag/0649)
* [Stacks Project, Tag 07AE](https://stacks.math.columbia.edu/tag/07AE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ChaoticSite

variable {C : Type u} [SmallCategory C] {B : Type u} [Ring B] (U : CosimplicialObject C)

/-! ### A projective resolution of a bounded above complex -/

/-- A morphism in `D(𝒜)` that is conjugate by isomorphisms to the image of `g` is invertible
exactly when `g` is a quasi-isomorphism. -/
private theorem isIso_iff_quasiIso_of_comp_eq {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    [HasDerivedCategory 𝒜] {P P' : CochainComplex 𝒜 ℤ} {g : P ⟶ P'}
    {X Y : DerivedCategory 𝒜} {u : X ⟶ Y} (e : DerivedCategory.Q.obj P ≅ X)
    (e' : DerivedCategory.Q.obj P' ≅ Y) (h : DerivedCategory.Q.map g ≫ e'.hom = e.hom ≫ u) :
    IsIso u ↔ QuasiIso g := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (Arrow.isIso_iff_isIso_of_isIso (Arrow.isoMk e e' h.symm).hom).symm

namespace ModuleValued

/-- A resolution of a bounded above complex of `B̲`-modules by a bounded above complex of
projective diagrams whose structure morphism is epimorphic in every degree, as produced by
[Stacks, Tag 0646]. -/
def boundedAboveProjectiveResolution (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ)
    [K.IsStrictlyLE 0] : ProjectiveResolutionLemma.ProjectiveResolutionComplex K 0 :=
  (ProjectiveResolutionLemma.statement3 (0 : ℤ) K inferInstance).choose

/-- The structure morphism of
`Stacks.ChaoticSite.ModuleValued.boundedAboveProjectiveResolution` is epimorphic in every
degree. -/
lemma epi_boundedAboveProjectiveResolution_α (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ)
    [K.IsStrictlyLE 0] (n : ℤ) : Epi ((boundedAboveProjectiveResolution K).α.f n) :=
  (ProjectiveResolutionLemma.statement3 (0 : ℤ) K inferInstance).choose_spec n

/-- **Derived lower shriek in `D(B)` inverts a morphism of bounded above complexes of
`B̲`-modules exactly when the induced morphism of total Moore complexes is a
quasi-isomorphism.** -/
theorem isIso_totalDerivedColimit_map_iff (hU : IsPointResolution U)
    {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (f : K ⟶ L) :
    IsIso ((totalDerivedColimit C (ModuleCat.{u} B)).map (DerivedCategory.Q.map f)) ↔
      QuasiIso (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map f)
        (ComplexShape.up ℤ)) := by
  have := (boundedAboveProjectiveResolution K).projective
  have := (boundedAboveProjectiveResolution K).boundedAbove
  have := (boundedAboveProjectiveResolution K).quasiIso
  have := (boundedAboveProjectiveResolution L).projective
  have := (boundedAboveProjectiveResolution L).boundedAbove
  have := (boundedAboveProjectiveResolution L).quasiIso
  have hnat := totalQIsoDerivedColimitOfResolution_naturality_of_epi U hU
    (boundedAboveProjectiveResolution K).α (boundedAboveProjectiveResolution L).α
    (epi_boundedAboveProjectiveResolution_α L) f
  exact isIso_iff_quasiIso_of_comp_eq
    (totalQIsoDerivedColimitOfResolution U hU K _ (boundedAboveProjectiveResolution K).α)
    (totalQIsoDerivedColimitOfResolution U hU L _ (boundedAboveProjectiveResolution L).α) hnat

end ModuleValued

namespace AbelianValued

/-- A resolution of a bounded above complex of abelian presheaves by a bounded above complex of
projective presheaves whose structure morphism is epimorphic in every degree. -/
def boundedAboveProjectiveResolution (K : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ)
    [K.IsStrictlyLE 0] : ProjectiveResolutionLemma.ProjectiveResolutionComplex K 0 :=
  (ProjectiveResolutionLemma.statement3 (0 : ℤ) K inferInstance).choose

/-- The structure morphism of
`Stacks.ChaoticSite.AbelianValued.boundedAboveProjectiveResolution` is epimorphic in every
degree. -/
lemma epi_boundedAboveProjectiveResolution_α (K : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ)
    [K.IsStrictlyLE 0] (n : ℤ) : Epi ((boundedAboveProjectiveResolution K).α.f n) :=
  (ProjectiveResolutionLemma.statement3 (0 : ℤ) K inferInstance).choose_spec n

/-- **Derived lower shriek in `D(Ab)` inverts a morphism of bounded above complexes of abelian
presheaves exactly when the induced morphism of total Moore complexes is a
quasi-isomorphism.** -/
theorem isIso_totalDerivedColimit_map_iff (hU : IsPointResolution U)
    {K L : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (f : K ⟶ L) :
    IsIso ((totalDerivedColimit C AddCommGrpCat.{u}).map (DerivedCategory.Q.map f)) ↔
      QuasiIso (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map f)
        (ComplexShape.up ℤ)) := by
  have := (boundedAboveProjectiveResolution K).projective
  have := (boundedAboveProjectiveResolution K).boundedAbove
  have := (boundedAboveProjectiveResolution K).quasiIso
  have := (boundedAboveProjectiveResolution L).projective
  have := (boundedAboveProjectiveResolution L).boundedAbove
  have := (boundedAboveProjectiveResolution L).quasiIso
  have hnat := totalQIsoDerivedColimitOfResolution_naturality_of_epi U hU
    (boundedAboveProjectiveResolution K).α (boundedAboveProjectiveResolution L).α
    (epi_boundedAboveProjectiveResolution_α L) f
  exact isIso_iff_quasiIso_of_comp_eq
    (totalQIsoDerivedColimitOfResolution U hU K _ (boundedAboveProjectiveResolution K).α)
    (totalQIsoDerivedColimitOfResolution U hU L _ (boundedAboveProjectiveResolution L).α) hnat

end AbelianValued

/-! ### The two Moore bicomplexes -/

/-- Forgetting the module structure of a complex of diagrams keeps it bounded above. -/
instance isStrictlyLE_forgetModuleDiagrams
    (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) [K.IsStrictlyLE 0] :
    HomologicalComplex.IsStrictlySupported
      (((forgetModuleDiagrams (B := B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      (ComplexShape.embeddingUpIntLE 0) where
  isZero i hi := Functor.map_isZero (forgetModuleDiagrams (B := B))
    (HomologicalComplex.isZero_X_of_isStrictlySupported K
      (ComplexShape.embeddingUpIntLE 0) i hi)

/-- **The Moore bicomplex does not see the module structure**: the bicomplex of the underlying
complex of abelian diagrams is the bicomplex of the complex of module diagrams with the module
structure forgotten degreewise. This is
`Stacks.ChaoticSite.mooreCochainComplexCompForgetNatIso` applied in each column. -/
def mooreBicomplexForgetNatIso :
    (forgetModuleDiagrams (B := B)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        AbelianValued.mooreBicomplexFunctor U ≅
      ModuleValued.mooreBicomplexFunctor U ⋙
        ((ModuleValued.forgetModules (B := B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (mooreCochainComplexCompForgetNatIso U)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (ModuleValued.mooreCochainComplex U ⋙
      (ModuleValued.forgetModules (B := B)).mapHomologicalComplex (ComplexShape.up ℤ)))
        (ComplexShape.up ℤ)).symm

/-- **The image bicomplex has a total complex**, transported along
`Stacks.ChaoticSite.mooreBicomplexForgetNatIso` from the abelian Moore bicomplex, which has one
because it is bounded in both directions. No lemma derives this from the preservation of
coproducts by the forgetful functor. -/
instance hasTotal_mapBicomplex_mooreBicomplex
    (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) [K.IsStrictlyLE 0] :
    (HomologicalComplex₂.TotalMap.mapBicomplex (ModuleValued.forgetModules (B := B))
      (ModuleValued.mooreBicomplex U K)).HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_iso ((mooreBicomplexForgetNatIso U).app K) _

/-- **The total Moore complex does not see the module structure.** Combining
`Stacks.ChaoticSite.mooreBicomplexForgetNatIso` with the interchange of the total complex and an
additive functor preserving coproducts
(`HomologicalComplex₂.TotalMap.totalIso`): the total complex of the Moore bicomplex of the
underlying complex of abelian diagrams is the total complex of the Moore bicomplex of the complex
of module diagrams, read degreewise in abelian groups. -/
def totalMooreBicomplexForgetIso (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ)
    [K.IsStrictlyLE 0] :
    (AbelianValued.mooreBicomplex U (((forgetModuleDiagrams (B := B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)).total (ComplexShape.up ℤ) ≅
      ((ModuleValued.forgetModules (B := B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ModuleValued.mooreBicomplex U K).total (ComplexShape.up ℤ)) :=
  HomologicalComplex₂.total.mapIso ((mooreBicomplexForgetNatIso U).app K)
      (ComplexShape.up ℤ) ≪≫
    HomologicalComplex₂.TotalMap.totalIso (ModuleValued.forgetModules (B := B))
      (ModuleValued.mooreBicomplex U K)

/-- **`Stacks.ChaoticSite.totalMooreBicomplexForgetIso` is natural in the complex.** -/
lemma totalMooreBicomplexForgetIso_naturality
    {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (f : K ⟶ L) :
    HomologicalComplex₂.total.map ((AbelianValued.mooreBicomplexFunctor U).map
          (((forgetModuleDiagrams (B := B)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)) (ComplexShape.up ℤ) ≫
        (totalMooreBicomplexForgetIso U L).hom =
      (totalMooreBicomplexForgetIso U K).hom ≫
        ((ModuleValued.forgetModules (B := B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (HomologicalComplex₂.total.map
            ((ModuleValued.mooreBicomplexFunctor U).map f) (ComplexShape.up ℤ)) := by
  have hstep : HomologicalComplex₂.total.map ((AbelianValued.mooreBicomplexFunctor U).map
          (((forgetModuleDiagrams (B := B)).mapHomologicalComplex (ComplexShape.up ℤ)).map f))
            (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map ((mooreBicomplexForgetNatIso U).app L).hom
          (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map ((mooreBicomplexForgetNatIso U).app K).hom
          (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          ((((ModuleValued.forgetModules (B := B)).mapHomologicalComplex
            (ComplexShape.up ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((ModuleValued.mooreBicomplexFunctor U).map f)) (ComplexShape.up ℤ) := by
    rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
    exact congrArg (fun g => HomologicalComplex₂.total.map g (ComplexShape.up ℤ))
      ((mooreBicomplexForgetNatIso U).hom.naturality f)
  have htot := HomologicalComplex₂.TotalMap.totalMap_naturality
    (c₁₂ := ComplexShape.up ℤ) (ModuleValued.forgetModules (B := B))
    (ModuleValued.mooreBicomplex U K) (L := ModuleValued.mooreBicomplex U L)
    ((ModuleValued.mooreBicomplexFunctor U).map f)
  dsimp only [totalMooreBicomplexForgetIso, Iso.trans_hom]
  rw [HomologicalComplex₂.total.mapIso_hom, HomologicalComplex₂.total.mapIso_hom,
    HomologicalComplex₂.TotalMap.totalIso_hom_eq_totalMap,
    HomologicalComplex₂.TotalMap.totalIso_hom_eq_totalMap, Category.assoc, ← Category.assoc,
    hstep, Category.assoc, htot]

/-! ### The comparison for a bounded above complex -/

/-- **A morphism of bounded above complexes of `B̲`-modules is inverted by derived lower shriek
in `D(B)` exactly when the underlying morphism of complexes of abelian diagrams is inverted by
derived lower shriek in `D(Ab)`.** This is the statement that lets a result proved in `D(Ab)` —
for instance the change of coefficients of [Stacks, Tag 08QJ] — be read at module coefficients at
a complex that is not concentrated in a degree, which is the case a consumer of 08QJ meets.

It is an equivalence, not an implication, and it mentions no comparison map of its own, so it
imposes no direction on `f`: it applies to a unit and to a counit alike. -/
theorem isIso_totalDerivedColimit_map_forget_iff (hU : IsPointResolution U)
    {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (f : K ⟶ L) :
    IsIso ((totalDerivedColimit C (ModuleCat.{u} B)).map (DerivedCategory.Q.map f)) ↔
      IsIso ((totalDerivedColimit C AddCommGrpCat.{u}).map (DerivedCategory.Q.map
        (((forgetModuleDiagrams (B := B)).mapHomologicalComplex (ComplexShape.up ℤ)).map f))) := by
  rw [ModuleValued.isIso_totalDerivedColimit_map_iff U hU f,
    AbelianValued.isIso_totalDerivedColimit_map_iff U hU _,
    ← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      (HomologicalComplex₂.total.map ((ModuleValued.mooreBicomplexFunctor U).map f)
        (ComplexShape.up ℤ))
      (ModuleValued.forgetModules (B := B))]
  exact (MorphismProperty.arrow_mk_iso_iff
    (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.up ℤ))
    (Arrow.isoMk (totalMooreBicomplexForgetIso U K) (totalMooreBicomplexForgetIso U L)
      (totalMooreBicomplexForgetIso_naturality U f).symm)).symm

end Stacks.ChaoticSite

end
