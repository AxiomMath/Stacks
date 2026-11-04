module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent objects in the derived category of a sheaf of differential graded algebras

Let `C` be a category, viewed as a site with the chaotic topology, let `O` be a sheaf of rings on
it and let `(A, d)` be a sheaf of differential graded `O`-algebras. For an object `U` of `C` the
sections `A(U)` form a differential graded algebra, the sections `M(U)` of a differential graded
`A`-module form a differential graded `A(U)`-module, and taking derived sections is a functor
`RΓ(U, -) : D(A, d) ⥤ D(A(U), d)`. An object `M` of `D(A, d)` lies in the full subcategory
`QC(A, d)` when for every morphism `U → V` of `C` the canonical map
`RΓ(V, M) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, M)` is an isomorphism of `D(A(U), d)`.

Let now `F : C' ⥤ C` be a functor, `g : (Sh(C'), O') → (Sh(C), O)` the morphism of ringed topoi it
induces on the chaotic sites, `(A', d)` a sheaf of differential graded `O'`-algebras and
`φ : g^*A → A'` a map of sheaves of differential graded algebras — equivalently, a homomorphism
`A(F U') → A'(U')` of differential graded algebras for every object `U'` of `C'`, natural in `U'`.
The derived pullback `Lg^* : D(A, d) ⥤ D(A', d)` carries `QC(A, d)` into `QC(A', d)`.

The mechanism is the one of the ungraded case. Over an object `U'` of `C'` the derived sections of
`Lg^*K` are `RΓ(F U', K) ⊗^𝐋_{A(F U')} A'(U')`, so for a morphism `a' : V' ⟶ U'` of `C'ᵒᵖ` the
canonical map of `Lg^*K` along `a'` is the base change along the structure homomorphism at `U'` of
the canonical map of `K` along `F a'`, conjugated by the base-change square of `g` and by that
computation of derived sections.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.SectionData`: the section differential graded algebras
  `A(U)` and modules `M(U)` with their restriction homomorphisms, the derived sections functors
  `RΓ(U, -)` with their derived restriction maps, and the derived base changes along restriction.
* `SheafOfModules.DifferentialGradedModule.sectionComparison`: the canonical map
  `RΓ(V, M) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, M)`, the adjoint transpose of the derived restriction map.
* `SheafOfModules.DifferentialGradedModule.IsQC` and
  `SheafOfModules.DifferentialGradedModule.QC`: the quasi-coherence condition and the full
  subcategory `QC(A, d) ⊆ D(A, d)` it cuts out.
* `SheafOfModules.DifferentialGradedModule.MorphismSectionData`: the homomorphisms
  `A(F U') ⟶ A'(U')` induced by `φ` on sections, with the derived base changes along them.
* `SheafOfModules.DifferentialGradedModule.restrictionMate`: the mate of the inverse base-change
  square of `g`.
* `SheafOfModules.DifferentialGradedModule.DerivedPullbackSectionData`: the base-change square of
  `g` together with the computation of the derived sections of `Lg^*` and its compatibility with
  the derived restriction maps.
* `SheafOfModules.DifferentialGradedModule.qcPullback`: the induced functor
  `QC(A, d) ⥤ QC(A', d)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.sectionComparison_derivedPullback`: the canonical map
  of `Lg^*K` is the base change along the structure homomorphism of the canonical map of `K`,
  conjugated by the base-change square and the computation of the derived sections of `Lg^*K`.
* `SheafOfModules.DifferentialGradedModule.isQC_derivedPullback`: a functor whose derived sections
  are computed by derived base change carries quasi-coherent objects to quasi-coherent objects.

## Implementation notes

The section algebras and section modules are *pinned* to `A` and to its differential graded
modules. A `SectionData` carries, for every object `U` of the site and every integer `n`, an
additive equivalence between the degree-`n` part of `A(U)` and the sections of the degree-`n` term
of `A` over `U`, compatible with the differential, the multiplication, the unit and the
restriction maps of `A`; likewise for `M(U)` and the sections of `M`, compatibly with the right
action of `A` and with homomorphisms of `A`-modules. The derived sections functor is pinned by an
identification of its value on the image of a differential graded module `M` with the class of
`M(U)` in `D(A(U), d)`, and its derived restriction map is pinned on those images to the
restriction of sections. Since every object of the derived category is isomorphic to the image of
a differential graded module, this determines the derived sections and the quasi-coherence
condition below is a condition on `A` and on the object of `D(A, d)`.

The derived categories of the section algebras, derived restriction of scalars along their
restriction homomorphisms and the homotopy categories are the ones the ambient library constructs
for a differential graded algebra over a commutative ring; a sheaf of differential graded algebras
has differential graded algebras of sections over any commutative coefficient ring, and `Λ` is
that ring.

This file is stated for an abstract derived category, abstract derived sections and an abstract
derived pullback. On a chaotic site all three are constructed: the derived sections and their
restriction maps in `SheafOfModules.DifferentialGradedModule.sectionDatum`, and the derived
pullback along a functor of chaotic sites as
`SheafOfModules.DifferentialGradedModule.chaoticDerivedPullback`, for which Tag 0GZC is
`SheafOfModules.DifferentialGradedModule.qc_chaoticDerivedPullback`. In the abstract setting of
this file the derived category is carried as
`SheafOfModules.DifferentialGradedModule.GoodModuleData`, which supplies the localization functor
out of the homotopy category and the flat-resolution theory, and the derived pullback is carried as
`SheafOfModules.DifferentialGradedModule.DerivedTensorData`, the derived extension of
`M ↦ g^*M ⊗_A A'` computed on good modules of Tag 0FTE. The derived sections functor and its
restriction maps are fields of `SectionData`, pinned as described above, and the derived base
changes are carried as functors pinned by their adjunctions to derived restriction of scalars,
which determines them up to unique natural isomorphism.

The computation `RΓ(U', Lg^*K) ≅ RΓ(F U', K) ⊗^𝐋_{A(F U')} A'(U')` is likewise a *hypothesis*, the
field `sectionsIso` of `DerivedPullbackSectionData`. It is the commutation of derived pullback with
taking derived sections on a chaotic site, which the source deduces from Tag 0FTI and which the
ambient library does not have for these derived categories. Its compatibility with the derived
restriction maps is stated for the canonical restriction maps rather than for the canonical
comparison maps whose invertibility is at issue, so that nothing in the hypothesis presupposes the
conclusion. The mate of the base-change square's inverse, and the unit identity the transposition
argument needs, are constructed from the square.

The base-change square itself is *not* a hypothesis, although it is a field of
`DerivedPullbackSectionData`: both of its composites are left adjoints of composites of derived
restrictions of scalars, those two composites are derived restriction along the two composite
homomorphisms of section algebras, and the naturality of `φ` makes those equal. The construction
is `MorphismSectionData.baseChangeSquare` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedQuasiCoherentBaseChange.lean`, and
`DerivedPullbackSectionData.ofSectionsIso` there builds the datum from `sectionsIso` and its
compatibility alone. The derived base changes of a `MorphismSectionData` are not hypotheses
either: they are the derived tensor products with the regular bimodules of the structure
homomorphisms, by Tag 0BYX.

UNIVERSES. The two sites, their sheaves of rings, the algebra and module components of the two
sheaves of differential graded algebras, the objects and morphisms of the two derived categories
and the coefficient ring of the section algebras all keep independent universes. The section
algebras and modules lie in the universe of the coefficient ring `Λ`, which is what the derived
category of a differential graded algebra in the ambient library requires; an instantiation
chooses `Λ` large enough to accommodate the sections of both sheaves.

## References

* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Lemma 24.33.4 (Tag 0GZC)](https://stacks.math.columbia.edu/tag/0GZC)
* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe s t a m v u t' a' m' v' u' d e d' e'

namespace SheafOfModules.DifferentialGradedModule

/-! ### The section algebras and the quasi-coherence condition -/

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The sections of a sheaf of differential graded algebras `A` and of its differential graded
modules, as differential graded algebras and modules over a commutative ring `Λ`, together with
the derived sections functors out of a derived category of `A` and the derived base changes along
the restriction homomorphisms.

The section algebras and modules are pinned to `A` degreewise, the derived sections functors are
pinned on the images of differential graded modules, and each base change is pinned by its
adjunction to derived restriction of scalars. -/
structure SectionData (Λ : Type s) [CommRing Λ] {A : DifferentialGradedAlgebra.{t, a} R}
    {D : Type d} [Category.{e} D] (gA : GoodModuleData.{t, a, m, v, u, d, e} A D) where
  /-- The differential graded algebra `A(U)` of sections of `A` over `U`. -/
  algebra : Cᵒᵖ → _root_.DifferentialGradedAlgebra.{s, s} Λ
  /-- The degree-`n` part of `A(U)` is the group of sections of `A^n` over `U`. -/
  degree (U : Cᵒᵖ) (n : ℤ) : (algebra U).grading n ≃+ (A.complex.X n).val.obj U
  /-- The identification carries the differential of `A(U)` to the differential of `A`. -/
  degree_d (U : Cᵒᵖ) (n : ℤ) (x : (algebra U).grading n) :
    degree U (n + 1) ⟨(algebra U).d (x : (algebra U).A),
        (algebra U).d_mem n (x : (algebra U).A) x.2⟩ =
      (A.complex.d n (n + 1)).val.app U (degree U n x)
  /-- The identification carries the multiplication of `A(U)` to the multiplication of `A`. -/
  degree_mul (U : Cᵒᵖ) (n i : ℤ) (x : (algebra U).grading n) (y : (algebra U).grading i)
      (z : (algebra U).grading (n + i))
      (hz : (z : (algebra U).A) = (x : (algebra U).A) * (y : (algebra U).A)) :
    degree U (n + i) z = (A.mul n i).app U (degree U n x) (degree U i y)
  /-- The identification carries the unit of `A(U)` to the unit of `A`. -/
  degree_one (U : Cᵒᵖ) (z : (algebra U).grading 0) (hz : (z : (algebra U).A) = 1) :
    degree U 0 z = A.one.eval U
  /-- The restriction homomorphism `A(V) ⟶ A(U)` of a morphism `a : V ⟶ U` of `Cᵒᵖ`. -/
  restriction {U V : Cᵒᵖ} (a : V ⟶ U) : (algebra V).Hom (algebra U)
  /-- The identification carries the restriction homomorphisms of the section algebras to the
  restriction maps of `A`. -/
  restriction_degree {U V : Cᵒᵖ} (a : V ⟶ U) (n : ℤ) (x : (algebra V).grading n) :
    degree U n ⟨(restriction a).toAlgebraHom (x : (algebra V).A),
        (restriction a).map_grading n (x : (algebra V).A) x.2⟩ =
      (A.complex.X n).val.map a (degree V n x)
  /-- The sections `M(U)` over `U` of a differential graded `A`-module, as a differential graded
  `A(U)`-module. -/
  moduleSections (U : Cᵒᵖ) :
    DifferentialGradedModule.{t, a, m} A ⥤ _root_.DifferentialGradedModule.{s, s, s} (algebra U)
  /-- The degree-`n` part of `M(U)` is the group of sections of `M^n` over `U`. -/
  moduleDegree (U : Cᵒᵖ) (M : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    ((moduleSections U).obj M).grading n ≃+ (M.complex.X n).val.obj U
  /-- The identification carries the differential of `M(U)` to the differential of `M`. -/
  moduleDegree_d (U : Cᵒᵖ) (M : DifferentialGradedModule.{t, a, m} A) (n : ℤ)
      (x : ((moduleSections U).obj M).grading n) :
    moduleDegree U M (n + 1) ⟨((moduleSections U).obj M).d (x : ((moduleSections U).obj M).M),
        ((moduleSections U).obj M).d_mem n (x : ((moduleSections U).obj M).M) x.2⟩ =
      (M.complex.d n (n + 1)).val.app U (moduleDegree U M n x)
  /-- The identification carries the right action of `A(U)` on `M(U)` to the right action of `A`
  on `M`. -/
  moduleDegree_mul (U : Cᵒᵖ) (M : DifferentialGradedModule.{t, a, m} A) (n i : ℤ)
      (x : ((moduleSections U).obj M).grading n) (y : (algebra U).grading i)
      (z : ((moduleSections U).obj M).grading (n + i))
      (hz : (z : ((moduleSections U).obj M).M) =
        MulOpposite.op (y : (algebra U).A) • (x : ((moduleSections U).obj M).M)) :
    moduleDegree U M (n + i) z = (M.mul n i).app U (moduleDegree U M n x) (degree U i y)
  /-- The identification is natural in the differential graded module. -/
  moduleDegree_naturality (U : Cᵒᵖ) {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N)
      (n : ℤ) (x : ((moduleSections U).obj M).grading n) :
    moduleDegree U N n ⟨((moduleSections U).map f).toFun (x : ((moduleSections U).obj M).M),
        ((moduleSections U).map f).map_grading n (x : ((moduleSections U).obj M).M) x.2⟩ =
      (f.toHomologicalComplex.f n).val.app U (moduleDegree U M n x)
  /-- Derived sections `RΓ(U, -) : D(A, d) ⥤ D(A(U), d)` over an object of the site. -/
  derivedSections (U : Cᵒᵖ) : D ⥤ _root_.DifferentialGradedModule.derivedCategory' (algebra U)
  /-- On the image in `D(A, d)` of a differential graded module `M`, the derived sections over `U`
  are the class of the differential graded `A(U)`-module `M(U)`. -/
  derivedSectionsIso (U : Cᵒᵖ) :
    HomotopyCategory.quotient A ⋙ gA.localization ⋙ derivedSections U ≅
      moduleSections U ⋙ _root_.DifferentialGradedModule.toHomotopyCategory.{s, s, s}
          (algebra U) ⋙
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (algebra U)).Q
  /-- Restriction of sections `M(V) ⟶ M(U)_{A(V)}` along a morphism of `Cᵒᵖ`. -/
  moduleRestriction {U V : Cᵒᵖ} (a : V ⟶ U) (M : DifferentialGradedModule.{t, a, m} A) :
    (moduleSections V).obj M ⟶
      _root_.DifferentialGradedModule.restrictScalars (restriction a) ((moduleSections U).obj M)
  /-- The identification carries restriction of sections to the restriction maps of `M`. -/
  moduleRestriction_degree {U V : Cᵒᵖ} (a : V ⟶ U) (M : DifferentialGradedModule.{t, a, m} A)
      (n : ℤ) (x : ((moduleSections V).obj M).grading n) :
    moduleDegree U M n ⟨(moduleRestriction a M).toFun (x : ((moduleSections V).obj M).M),
        (moduleRestriction a M).map_grading n (x : ((moduleSections V).obj M).M) x.2⟩ =
      (M.complex.X n).val.map a (moduleDegree V M n x)
  /-- The canonical derived restriction map `RΓ(V, -) ⟶ RΓ(U, -)_{A(V)}` of a morphism of
  `Cᵒᵖ`. -/
  restrictionMap {U V : Cᵒᵖ} (a : V ⟶ U) :
    derivedSections V ⟶ derivedSections U ⋙
      _root_.DifferentialGradedModule.derivedRestriction (restriction a)
  /-- On the image of a differential graded module the derived restriction map is restriction of
  sections, read through the identifications of the derived sections and the factorization of
  derived restriction of scalars. -/
  restrictionMap_moduleSections {U V : Cᵒᵖ} (a : V ⟶ U)
      (M : DifferentialGradedModule.{t, a, m} A) :
    (derivedSectionsIso V).hom.app M ≫
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (algebra V)).Q.map
          ((_root_.DifferentialGradedModule.toHomotopyCategory.{s, s, s} (algebra V)).map
            (moduleRestriction a M)) =
      (restrictionMap a).app (gA.localization.obj ((HomotopyCategory.quotient A).obj M)) ≫
        (_root_.DifferentialGradedModule.derivedRestriction (restriction a)).map
          ((derivedSectionsIso U).hom.app M) ≫
        (_root_.DifferentialGradedModule.derivedRestrictionFactorization
            (restriction a)).hom.app
          ((_root_.DifferentialGradedModule.toHomotopyCategory.{s, s, s} (algebra U)).obj
            ((moduleSections U).obj M))
  /-- Derived base change `- ⊗^𝐋_{A(V)} A(U)` along a restriction homomorphism. -/
  baseChange {U V : Cᵒᵖ} (a : V ⟶ U) :
    _root_.DifferentialGradedModule.derivedCategory' (algebra V) ⥤
      _root_.DifferentialGradedModule.derivedCategory' (algebra U)
  /-- The base change is the left adjoint of derived restriction of scalars, which determines it
  up to unique natural isomorphism. -/
  baseChangeAdj {U V : Cᵒᵖ} (a : V ⟶ U) :
    baseChange a ⊣ _root_.DifferentialGradedModule.derivedRestriction (restriction a)

variable {Λ : Type s} [CommRing Λ] {A : DifferentialGradedAlgebra.{t, a} R} {D : Type d}
  [Category.{e} D] {gA : GoodModuleData.{t, a, m, v, u, d, e} A D}

/-- The canonical map `RΓ(V, M) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, M)` of a morphism `a : V ⟶ U` of `Cᵒᵖ`:
the adjoint transpose of the derived restriction map under the base-change adjunction. -/
def sectionComparison (sd : SectionData Λ gA) {U V : Cᵒᵖ} (a : V ⟶ U) (M : D) :
    (sd.baseChange a).obj ((sd.derivedSections V).obj M) ⟶ (sd.derivedSections U).obj M :=
  ((sd.baseChangeAdj a).homEquiv _ _).symm ((sd.restrictionMap a).app M)

/-- The adjoint transpose of `sectionComparison` is the derived restriction map. -/
private theorem homEquiv_sectionComparison (sd : SectionData Λ gA) {U V : Cᵒᵖ} (a : V ⟶ U)
    (M : D) : (sd.baseChangeAdj a).homEquiv _ _ (sectionComparison sd a M) =
      (sd.restrictionMap a).app M :=
  Equiv.apply_symm_apply _ _

/-- An object of `D(A, d)` is quasi-coherent when for every morphism `U → V` of the site the
canonical map `RΓ(V, M) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, M)` is an isomorphism of `D(A(U), d)`, the
derived sections and the derived base changes being those carried by `sd`.

Tag 0GZ9 itself is registered on
`SheafOfModules.DifferentialGradedModule.QC` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedSectionQuasiCoherent.lean`,
which cuts the same full subcategory out of the derived category of a sheaf of differential
graded algebras on a chaotic site from the section algebras and section modules themselves. This
version is the one the functoriality results of the section below are stated for. -/
def IsQC (sd : SectionData Λ gA) (M : D) : Prop :=
  ∀ {U V : Cᵒᵖ} (a : V ⟶ U), IsIso (sectionComparison sd a M)

/-- The full subcategory `QC(A, d) ⊆ D(A, d)` of quasi-coherent objects, for the derived
sections and derived base changes carried by `sd`. -/
abbrev QC (sd : SectionData Λ gA) : Type _ :=
  ObjectProperty.FullSubcategory (fun M ↦ IsQC sd M)

/-- The inclusion of the quasi-coherent objects into the derived category. -/
abbrev QCι (sd : SectionData Λ gA) : QC sd ⥤ D :=
  ObjectProperty.ι _

end Sections

/-! ### Adjoint transposes through a square of adjunctions -/

section Transpose

variable {X₁ : Type*} [Category X₁] {Y₁ : Type*} [Category Y₁] {X₂ : Type*} [Category X₂]
  {Y₂ : Type*} [Category Y₂] {G : X₁ ⥤ X₂} {H : Y₁ ⥤ Y₂} {L₁ : X₁ ⥤ Y₁} {R₁ : Y₁ ⥤ X₁}
  {L₂ : X₂ ⥤ Y₂} {R₂ : Y₂ ⥤ X₂} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Adjoint transpose of a composite through a square of adjunctions: if `β` is a mate of `α`, as
witnessed by the unit identity `hβ`, then the transpose of `L₂ s ≫ α ≫ H c ≫ e` is obtained from
the transpose of `c` by applying `G` and composing with `β` and with `R₂ e`. -/
theorem homEquiv_comp_of_unit_eq (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hβ : ∀ Y : X₁, G.map (adj₁.unit.app Y) ≫ β.app (L₁.obj Y) =
      adj₂.unit.app (G.obj Y) ≫ R₂.map (α.app Y))
    {Y : X₁} {Z : Y₁} (c : L₁.obj Y ⟶ Z) {W : X₂} (s : W ⟶ G.obj Y) {T : Y₂}
    (e : H.obj Z ⟶ T) :
    adj₂.homEquiv W T (L₂.map s ≫ α.app Y ≫ H.map c ≫ e) =
      s ≫ G.map (adj₁.homEquiv Y Z c) ≫ β.app Z ≫ R₂.map e := by
  have h₁ := hβ Y
  have h₂ := β.naturality c
  simp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₂, reassoc_of% h₁]

end Transpose

/-! ### Derived pullback along a morphism of chaotic ringed sites -/

section Pullback

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t'}}
  {Λ : Type s} [CommRing Λ] {A : DifferentialGradedAlgebra.{t, a} R}
  {A' : DifferentialGradedAlgebra.{t', a'} R'} {D : Type d} [Category.{e} D] {D' : Type d'}
  [Category.{e'} D'] {gA : GoodModuleData.{t, a, m, v, u, d, e} A D}
  {gA' : GoodModuleData.{t', a', m', v', u', d', e'} A' D'}

/-- The homomorphisms of section algebras induced by a map `φ : g^*A → A'` of sheaves of
differential graded algebras over a functor `F : C' ⥤ C` of chaotic sites, together with the
derived base changes along them.

A map `φ : g^*A → A'` is exactly such a family of homomorphisms `A(F U') ⟶ A'(U')` of differential
graded algebras, natural in `U'`, which is what `structureHom_restriction` records. The base change
along each of them is pinned by its adjunction to derived restriction of scalars. -/
structure MorphismSectionData (F : C' ⥤ C) (sd : SectionData Λ gA) (sd' : SectionData Λ gA') where
  /-- The homomorphism `A(F U') ⟶ A'(U')` of section algebras at an object of `C'`. -/
  structureHom (U' : C'ᵒᵖ) : (sd.algebra (F.op.obj U')).Hom (sd'.algebra U')
  /-- The structure homomorphisms are natural in the object of `C'`: they commute with the
  restriction homomorphisms of the two families of section algebras. -/
  structureHom_restriction {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') (x : (sd.algebra (F.op.obj V')).A) :
    (structureHom U').toAlgebraHom ((sd.restriction (F.op.map a')).toAlgebraHom x) =
      (sd'.restriction a').toAlgebraHom ((structureHom V').toAlgebraHom x)
  /-- Derived base change `- ⊗^𝐋_{A(F U')} A'(U')` along the structure homomorphism at `U'`. -/
  baseChange (U' : C'ᵒᵖ) :
    _root_.DifferentialGradedModule.derivedCategory' (sd.algebra (F.op.obj U')) ⥤
      _root_.DifferentialGradedModule.derivedCategory' (sd'.algebra U')
  /-- The base change is the left adjoint of derived restriction of scalars along the structure
  homomorphism, which determines it up to unique natural isomorphism. -/
  adj (U' : C'ᵒᵖ) :
    baseChange U' ⊣ _root_.DifferentialGradedModule.derivedRestriction (structureHom U')

variable {F : C' ⥤ C} {sd : SectionData Λ gA} {sd' : SectionData Λ gA'}

/-- The mate of the inverse of a base-change square of the morphism of ringed sites: it compares
derived restriction of scalars along a restriction homomorphism of `A`, followed by base change
along the structure homomorphism at `V'`, with base change along the structure homomorphism at
`U'`, followed by derived restriction along the corresponding restriction homomorphism of `A'`. -/
def restrictionMate (msd : MorphismSectionData F sd sd') {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (sq : sd.baseChange (F.op.map a') ⋙ msd.baseChange U' ≅
      msd.baseChange V' ⋙ sd'.baseChange a') :
    _root_.DifferentialGradedModule.derivedRestriction (sd.restriction (F.op.map a')) ⋙
        msd.baseChange V' ⟶
      msd.baseChange U' ⋙
        _root_.DifferentialGradedModule.derivedRestriction (sd'.restriction a') :=
  mateEquiv (sd.baseChangeAdj (F.op.map a')) (sd'.baseChangeAdj a') sq.inv

/-- The unit identity exhibiting `restrictionMate` as a mate of the inverse base-change square. -/
theorem unit_restrictionMate (msd : MorphismSectionData F sd sd') {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (sq : sd.baseChange (F.op.map a') ⋙ msd.baseChange U' ≅
      msd.baseChange V' ⋙ sd'.baseChange a')
    (Y : _root_.DifferentialGradedModule.derivedCategory' (sd.algebra (F.op.obj V'))) :
    (msd.baseChange V').map ((sd.baseChangeAdj (F.op.map a')).unit.app Y) ≫
        (restrictionMate msd a' sq).app ((sd.baseChange (F.op.map a')).obj Y) =
      (sd'.baseChangeAdj a').unit.app ((msd.baseChange V').obj Y) ≫
        (_root_.DifferentialGradedModule.derivedRestriction (sd'.restriction a')).map
          (sq.inv.app Y) :=
  unit_mateEquiv _ _ _ Y

/-- The base-change square of the morphism of ringed sites, the computation of the derived
sections of the derived pullback, and the compatibility of that computation with the derived
restriction maps.

The derived pullback itself is the left derived extension `Lg^*` of `M ↦ g^*M ⊗_A A'` carried by a
`SheafOfModules.DifferentialGradedModule.DerivedTensorData`; `sectionsIso` is the computation
`RΓ(U', Lg^*K) ≅ RΓ(F U', K) ⊗^𝐋_{A(F U')} A'(U')` of the source's proof. -/
structure DerivedPullbackSectionData (msd : MorphismSectionData F sd sd')
    (Lg : DerivedTensorData gA gA') where
  /-- Base change along a restriction homomorphism of `A` followed by base change along the
  structure homomorphism at `U'` agrees with base change along the structure homomorphism at `V'`
  followed by base change along the corresponding restriction homomorphism of `A'`. -/
  baseChangeSquare {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    sd.baseChange (F.op.map a') ⋙ msd.baseChange U' ≅ msd.baseChange V' ⋙ sd'.baseChange a'
  /-- `RΓ(U', Lg^*K) ≅ RΓ(F U', K) ⊗^𝐋_{A(F U')} A'(U')`, naturally in `K`. -/
  sectionsIso (U' : C'ᵒᵖ) :
    Lg.derived ⋙ sd'.derivedSections U' ≅
      sd.derivedSections (F.op.obj U') ⋙ msd.baseChange U'
  /-- The computation of the derived sections carries the canonical derived restriction maps of
  `Lg^*K` to those of `K`, transported along `restrictionMate`. -/
  sectionsIso_restrictionMap {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') (K : D) :
    (sd'.restrictionMap a').app (Lg.derived.obj K) ≫
        (_root_.DifferentialGradedModule.derivedRestriction (sd'.restriction a')).map
          ((sectionsIso U').hom.app K) =
      (sectionsIso V').hom.app K ≫
        (msd.baseChange V').map ((sd.restrictionMap (F.op.map a')).app K) ≫
        (restrictionMate msd a' (baseChangeSquare a')).app
          ((sd.derivedSections (F.op.obj U')).obj K)

variable {msd : MorphismSectionData F sd sd'} {Lg : DerivedTensorData gA gA'}

/-- The canonical map of `Lg^*K` along a morphism `a'` of `C'ᵒᵖ` is the base change along the
structure homomorphism at `U'` of the canonical map of `K` along `F a'`, conjugated by the
base-change square and by the computation of the derived sections of `Lg^*K`. -/
theorem sectionComparison_derivedPullback (dp : DerivedPullbackSectionData msd Lg)
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') (K : D) :
    sectionComparison sd' a' (Lg.derived.obj K) =
      (sd'.baseChange a').map ((dp.sectionsIso V').hom.app K) ≫
        (dp.baseChangeSquare a').inv.app ((sd.derivedSections (F.op.obj V')).obj K) ≫
        (msd.baseChange U').map (sectionComparison sd (F.op.map a') K) ≫
        (dp.sectionsIso U').inv.app K := by
  have hc := dp.sectionsIso_restrictionMap a' K
  rw [← Category.assoc] at hc
  have key := homEquiv_comp_of_unit_eq (sd.baseChangeAdj (F.op.map a')) (sd'.baseChangeAdj a')
    (dp.baseChangeSquare a').inv (restrictionMate msd a' (dp.baseChangeSquare a'))
    (unit_restrictionMate msd a' (dp.baseChangeSquare a'))
    (sectionComparison sd (F.op.map a') K) ((dp.sectionsIso V').hom.app K)
    ((dp.sectionsIso U').inv.app K)
  simp only [Functor.comp_obj] at key
  apply ((sd'.baseChangeAdj a').homEquiv _ _).injective
  rw [homEquiv_sectionComparison, key, homEquiv_sectionComparison, ← Category.assoc,
    ← Category.assoc, ← hc, Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app]
  simp

/-- A functor of derived categories whose derived sections are computed by derived base change,
compatibly with the derived restriction maps, carries quasi-coherent objects to quasi-coherent
objects.

Tag 0GZC itself, for the derived pullback along a functor of chaotic sites, is
`SheafOfModules.DifferentialGradedModule.qc_chaoticDerivedPullback` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedChaoticPullbackQuasiCoherent.lean`,
where the derived pullback is constructed. -/
theorem isQC_derivedPullback (dp : DerivedPullbackSectionData msd Lg) (K : D)
    (hK : IsQC sd K) : IsQC sd' (Lg.derived.obj K) := by
  intro U' V' a'
  rw [sectionComparison_derivedPullback dp a' K]
  have := hK (F.op.map a')
  infer_instance

/-- The functor `QC(A, d) ⥤ QC(A', d)` through which the derived pullback factors, the full
subcategories of quasi-coherent objects being stable under `Lg^*`. -/
def qcPullback (dp : DerivedPullbackSectionData msd Lg) : QC sd ⥤ QC sd' :=
  ObjectProperty.lift _ (QCι sd ⋙ Lg.derived) fun K ↦ isQC_derivedPullback dp K.obj K.property

end Pullback

end SheafOfModules.DifferentialGradedModule

end
