module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.AffineOpenSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFlatEquivalence

/-!
# The equivalence of the first clause of Tag 08KU

Let `i : X ⟶ X'` be a thickening, `f : X ⟶ Y` affine, `Y' = Y ⨿_X X'` the pushout of
[Stacks Project, Tag 07RT] and `g : V' ⟶ Y'` a morphism, with the three base changes
`V = Y ×_{Y'} V'`, `U' = X' ×_{Y'} V'` and `U = X ×_{Y'} V'`.  The first clause of
[Stacks Project, Tag 08KU] asserts that the comparison functor
`Stacks.Pushout.flatBaseChangeTripleFunctor` — a quasi-coherent `𝒪_{V'}`-module flat over `Y'`
goes to its two restrictions together with the canonical isomorphism of their restrictions to
`U` — is an **equivalence** onto the triples `(𝒢, ℱ', φ)` of a quasi-coherent module on `V` flat
over `Y`, a quasi-coherent module on `U'` flat over `X'` and an isomorphism of their restrictions
to `U`.  This file proves that.

The comparison functor is left adjoint to the gluing functor
`Stacks.Pushout.tripleGluingFunctor` by `Stacks.Pushout.baseChangeTripleAdjunction`, and the
glued module of a flat triple is itself quasi-coherent and flat over `Y'`
(`Stacks.Pushout.flatQuasicoherent_tripleGluingFunctor_obj`), so that adjunction restricts to the
two categories the tag names.  What is proved here is that its unit and its counit are
isomorphisms there, which is the remaining, affine-local, half of the clause: both are checked on
the sections over the affine charts of [Stacks Project, Tag 07RW], where the ring-level
equivalence `MilnorPatching.relativelyFlatModulesEquivalenceOverFibreProduct` applies.

## Main definitions

* `Stacks.Pushout.flatTripleGluingFunctor` is the gluing functor between the two categories of
  the tag — the restriction of `Stacks.Pushout.tripleGluingFunctor`, which lands in the
  subcategory by `Stacks.Pushout.flatQuasicoherent_tripleGluingFunctor_obj`.
* `Stacks.Pushout.flatBaseChangeTripleAdjunction` is the adjunction
  `flatBaseChangeTripleFunctor i f g hi ⊣ flatTripleGluingFunctor i f g hi`, the restriction of
  `Stacks.Pushout.baseChangeTripleAdjunction` along the two fully faithful inclusions.
* `Stacks.Pushout.chartIndex` and `Stacks.Pushout.chartOpen` are the affine opens of `V'` lying
  above an affine open of `Y'` — the charts over which everything below is checked; they cover
  `V'` by `Stacks.Pushout.isOpenCover_chartOpen`.

## Main results

* `Stacks.Pushout.isEquivalence_flatBaseChangeTripleFunctor`: **the first clause of
  [Stacks Project, Tag 08KU]** — the comparison functor restricts to an equivalence of the
  category of quasi-coherent `𝒪_{V'}`-modules flat over `Y'` with the category of triples of a
  quasi-coherent module on `V` flat over `Y`, a quasi-coherent module on `U'` flat over `X'` and
  an isomorphism of their restrictions to `U`.
* `Stacks.Pushout.isIso_gluingUnitApp`: the unit of the unrestricted adjunction is an
  isomorphism at a quasi-coherent module flat over `Y'`, and
  `Stacks.Pushout.isIso_baseChangeTripleAdjunction_counit_app`: its counit is an isomorphism at
  a triple of quasi-coherent modules flat over `Y` and over `X'`.
* `Stacks.Pushout.bijective_gluingUnitApp_of_chartData` and
  `Stacks.Pushout.bijective_counit_app_of_chartData` are the two affine-local statements those
  rest on: over one chart the unit and the two components of the counit are bijective on
  sections.
* `Stacks.Pushout.exists_chartData` collects, for one chart, every identification the previous
  file produced: the relative Milnor patching situation
  `MilnorPatching.RelativeModuleFibreProductSituation`, the isomorphism of `Γ(Y', W)` with its
  ring fibre product, and the three isomorphisms of its base-change rings with the three chart
  section rings, compatible with all five structure maps.

## Implementation notes

**How a chart statement becomes the ring-level statement.**  Over an affine open `U` of `V'`
lying above an affine open `W` of `Y'`, `Stacks.Pushout.exists_chartData` presents `Γ(V', U)` as
an algebra over the ring fibre product that `Γ(Y', W)` is, and identifies the sections of the
three restrictions over the three charts with the three base-change rings of that situation.
`Stacks.Pushout.exists_chartGluingSectionsCompatiblePairsLinearEquiv` then identifies the
sections of the glued module over `U` with the compatible pairs, `Γ(V', U)`-linearly.  The unit
and the counit of [Stacks Project, Tag 07RW] are maps between modules over those rings, so
comparing them with the geometric unit and counit is a comparison of maps out of, respectively
into, a base change; a map out of a base change is determined by its values on the elements
`1 ⊗ a`, which is `ModuleCat.ExtendScalars.hom_ext`, and that is how every comparison below is
made.  `Stacks.Pushout.exists_chartPullbackSectionsHom` and
`Stacks.Pushout.bijective_chartPullbackSectionsOut` are the two directions of that passage,
resting on `Stacks.ModuleCat.exists_extendScalarsTargetHom` and
`Stacks.ModuleCat.bijective_of_extendScalarsTargetOut` — base change does not see which of two
isomorphic spellings of its target ring it is written over.

**The transpose on sections.**  The counit's two components are the transposes of the two
projections of the glued module along the two pullback-pushforward adjunctions, and
`Stacks.Pushout.transpose_app_pullbackSection` says what such a transpose does to a pulled-back
section: the transpose composed with the unit is the morphism itself, and the unit on the
sections over a full preimage is `AlgebraicGeometry.Scheme.Modules.pullbackSection`.  That is the
only computation the counit needs beyond the chart identifications.

**From one chart to the sheaf.**  `Stacks.Pushout.chartOpen` covers `V'`, so
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover` turns
bijectivity over every chart into invertibility of the unit; the preimages of those charts cover
`V` and `U'`, which does the same for the two components of the counit, a morphism of triples
being invertible as soon as both its components are
(`Stacks.Pushout.isIso_gluingTripleHom`).

**The pushout is produced, not assumed.**  As in the two previous files, the statement registered
for the tag takes exactly the tag's own setup — `i` a thickening, `f` affine — and binds
`CategoryTheory.Limits.HasPushout i f` in its own type from the first assertion of
[Stacks Project, Tag 07RT].  The auxiliary results carry `[HasPushout i f]` as a section
variable.

**The restriction of the adjunction.**  The two conditions of the tag cut out full subcategories,
and `Stacks.Pushout.flatBaseChangeTripleFunctor` and `Stacks.Pushout.flatTripleGluingFunctor` are
equal — not merely isomorphic — to the restrictions of the two unrestricted functors, so the two
comparison isomorphisms `CategoryTheory.Adjunction.restrictFullyFaithful` asks for are
`Stacks.Pushout.flatComm1` and `Stacks.Pushout.flatComm2`, both `CategoryTheory.Iso.refl`.  The
unit and counit of the restricted adjunction are then invertible because their images under the
fully faithful inclusions are, by
`CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app` and its counit companion, and a
fully faithful functor reflects isomorphisms.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RW](https://stacks.math.columbia.edu/tag/07RW)
* [Stacks Project, Tag 08KU](https://stacks.math.columbia.edu/tag/08KU)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace Stacks.Pushout

/-! ### Sections over an affine chart as a base change

The two directions of the passage between a statement about the sections of a pullback over an
affine chart and a statement about a base change of rings: a map *into* such a module of sections
is produced from its values on the elements `1 ⊗ a`, and a map *out of* one is recognised as
bijective from the same data. -/

/-- **The sections of a pullback over an affine chart are the base change, read through a
renaming of the two rings.** -/
theorem exists_chartPullbackSectionsHom {V' Z : Scheme.{u}} (p : Z ⟶ V') (M : V'.Modules)
    [M.IsQuasicoherent] {U : V'.Opens} (hU : IsAffineOpen U) (hpU : IsAffineOpen (p ⁻¹ᵁ U))
    {D : Type u} [CommRing D] (φ : Γ(V', U) →+* D) (k : D ≃+* Γ(Z, p ⁻¹ᵁ U))
    (hk : ∀ d : Γ(V', U), k (φ d) = (p.appLE U (p ⁻¹ᵁ U) le_rfl) d)
    (N : ModuleCat.{u} D) (e : N ≃ Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ U))
    (hadd : ∀ n n' : N, e (n + n') = e n + e n')
    (hsmul : ∀ (z : D) (n : N), e (z • n) = k z • e n) :
    ∃ β : (ModuleCat.extendScalars φ).obj (ModuleCat.of Γ(V', U) Γ(M, U)) ⟶ N,
      Function.Bijective β ∧
        ∀ a : Γ(M, U), e (β ((1 : D) ⊗ₜ[Γ(V', U),φ] a)) =
          Scheme.Modules.pullbackSection p M U (p ⁻¹ᵁ U) le_rfl a := by
  obtain ⟨β, hβ, hval⟩ := Stacks.ModuleCat.exists_extendScalarsTargetHom k φ
    (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom hk (ModuleCat.of Γ(V', U) Γ(M, U)) _
    (affinePullbackSectionsBaseChangeIso p M hU hpU le_rfl) N e hadd hsmul
  exact ⟨β, hβ, fun a => (hval a).trans
    (affinePullbackSectionsBaseChangeIso_one_tmul p M hU hpU le_rfl a)⟩

/-- Composition of morphisms of modules, on sections. -/
theorem modules_comp_app {Z : Scheme.{u}} {A B C : Z.Modules} (φ : A ⟶ B) (ψ : B ⟶ C)
    (V : Z.Opens) (a : Γ(A, V)) : (φ ≫ ψ).app V a = ψ.app V (φ.app V a) := rfl

/-- The pullback of a section over the full preimage is the unit of the pullback-pushforward
adjunction on sections. -/
theorem pullbackSection_preimage {A B : Scheme.{u}} (p : A ⟶ B) (N : B.Modules) (V : B.Opens)
    (a : Γ(N, V)) :
    Scheme.Modules.pullbackSection p N V (p ⁻¹ᵁ V) le_rfl a =
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N).app V a := by
  rw [pullbackSection_eq]
  rw [show (homOfLE (le_rfl : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ V)).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

variable {X X' Y V' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f]
variable (g : V' ⟶ pushout i f)

/-! ### The chart data

Everything the previous file produced for one affine chart, collected into a single statement so
that each of the three chart steps below can take it as one hypothesis. -/

open Stacks.Thickenings in
/-- **All the chart data of an affine chart in one statement.**  For an affine open `W` of `Y'`
and an affine open `U` of `V'` above it: the relative Milnor patching situation with
`D' = Γ(V', U)`, the isomorphism of `Γ(Y', W)` with its ring fibre product, and the three
isomorphisms of the situation's base-change rings with the three chart section rings, compatible
with all five of the situation's structure maps. -/
theorem exists_chartData (hi : IsThickening i) [IsAffineHom f]
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W) :
    ∃ (I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W))
      (base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I)
      (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
      (eB : Γ(pushout i f, W) ≃+* base.fibreProduct)
      (kD : s.D ≃+* Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U))
      (kC' : s.C' ≃+* Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U))
      (kC : s.C ≃+* Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U)),
      s.toD'.comp eB.toRingHom = (g.appLE W U hUW).hom ∧
        (∀ d : Γ(V', U), kD (s.toD d) =
          (targetRestriction i f g).appLE U (targetRestriction i f g ⁻¹ᵁ U) le_rfl d) ∧
        (∀ x : Γ(Y, pushout.inr i f ⁻¹ᵁ W), kD (s.BtoD x) =
          (targetBase i f g).appLE (pushout.inr i f ⁻¹ᵁ W) (targetRestriction i f g ⁻¹ᵁ U)
            (preimage_snd_le_preimage_fst (pushout.inr i f) g hUW) x) ∧
        (∀ d : Γ(V', U), kC' (s.toC' d) =
          (ambientRestriction i f g).appLE U (ambientRestriction i f g ⁻¹ᵁ U) le_rfl d) ∧
        (∀ x : Γ(X', pushout.inl i f ⁻¹ᵁ W), kC' (s.A'toC' x) =
          (ambientBase i f g).appLE (pushout.inl i f ⁻¹ᵁ W) (ambientRestriction i f g ⁻¹ᵁ U)
            (preimage_snd_le_preimage_fst (pushout.inl i f) g hUW) x) ∧
        (∀ z : s.D, kC (s.DtoC z) =
          ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
            (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U)).hom (kD z)) ∧
        (∀ z : s.C', kC (s.C'toC z) =
          ((commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
            (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U)).hom
            (kC' z)) := by
  refine Exists.elim (exists_chartSituation i f g hi hW hUW) fun I h1 =>
    Exists.elim h1 fun base h2 => Exists.elim h2 fun s h3 =>
    Exists.elim h3 fun eB hB => ?_
  obtain ⟨hD', heB, heA'⟩ := hB
  refine Exists.elim (exists_targetChartRingEquiv i f g hi hW hU hUW base s eB hD' heB)
    fun kD hkD => Exists.elim
      (exists_ambientChartRingEquiv i f g hi hW hU hUW base s eB hD' heA') fun kC' hkC' =>
      Exists.elim (exists_commonChartRingEquiv i f g hi hW hU hUW base s eB hD' heB)
        fun kC hkC => ?_
  have hkC1' : ∀ d : Γ(V', U), kC (s.C'toC (s.toC' d)) =
      (commonRestriction i f g).appLE U (commonRestriction i f g ⁻¹ᵁ U) le_rfl d := fun d =>
    (congrArg kC (DFunLike.congr_fun s.relativeSquare_comm d).symm).trans (hkC.1 d)
  exact ⟨I, base, s, eB, kD, kC', kC, hD', hkD.1, hkD.2, hkC'.1, hkC'.2,
    chartRingEquiv_DtoC i f g hUW s kD kC hkD.1 hkD.2 hkC.1 hkC.2,
    chartRingEquiv_C'toC i f g hUW s kC' kC hkC'.1 hkC'.2 hkC1' hkC.2⟩

/-! ### The ring-level equivalence of Tag 07RW, in the form the charts need

[Stacks Project, Tag 07RW] is available as
`MilnorPatching.relativelyFlatModulesEquivalenceOverFibreProduct`.  What the chart steps use of
it is: its right adjoint's values are the compatible pairs, its unit is invertible on flat
modules and its counit is invertible outright, and the two coordinates of a transpose are the
two components of a morphism of the categorical pullback.  The statements in this section are
that content, phrased so that the geometric data enters only as an abstract module `G` with a
linear identification of it with the compatible pairs. -/

/-- **[Stacks Project, Tag 07RW] with its extension-of-scalars functor spelled as
`ModuleGlueing.extensionOfScalarsToPullback`.**  The two spellings are the same functor by
definition; naming the second is what lets a statement about the components of `E.obj L` be
applied, since in that spelling those components are the two base changes of `L` on the nose. -/
theorem exists_relativeFlatAdjunction
    {A A' B D' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    {toBase : B →+* A} {surjection : A' →+* A} {J : Ideal A'}
    {base : RingFibreProduct.Situation toBase surjection J}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := D') base) :
    ∃ (F : MilnorPatching.RelativeModuleFibreProductSituation.CompatibleModules.{u, u, u, u, u} s ⥤
          ModuleCat.{u} D')
      (e : ∀ X, F.obj X ≃ₗ[D']
        MilnorPatching.compatiblePairsModule.{u} s.toD s.toC' s.DtoC s.C'toC
          s.relativeSquare_comm X)
      (adj : ModuleGlueing.extensionOfScalarsToPullback.{u} s.toD s.toC' s.DtoC s.C'toC
        s.relativeSquare_comm ⊣ F),
      (∀ (L : ModuleCat.{u} D') (X) (h : L ⟶ F.obj X) (l : L),
          (e X (h l)).1.1 = ((adj.homEquiv L X).symm h).fst ((1 : s.D) ⊗ₜ[D',s.toD] l) ∧
            (e X (h l)).1.2 = ((adj.homEquiv L X).symm h).snd ((1 : s.C') ⊗ₜ[D',s.toC'] l)) ∧
        (∀ L : ModuleCat.{u} D',
          Module.Flat base.fibreProduct ((ModuleCat.restrictScalars.{u, u, u} s.toD').obj L) →
            IsIso (adj.unit.app L)) ∧
          IsIso adj.counit := by
  obtain ⟨F, e07, adj, form, -, hcounit, -, hunit, -⟩ :=
    MilnorPatching.relativelyFlatModulesEquivalenceOverFibreProduct s
  exact ⟨F, e07, adj, form, hunit, hcounit⟩

/-- **The transpose of a map into the compatible-pairs module is invertible as soon as its two
coordinate maps are.**  Stated for `ModuleGlueing.extensionOfScalarsToPullback` itself, where the
two components of `E.obj L` are the two base changes of `L` on the nose. -/
theorem isIso_transpose_of_components
    {D' Dr Cr' Cr : Type u} [CommRing D'] [CommRing Dr] [CommRing Cr'] [CommRing Cr]
    (toD : D' →+* Dr) (toC' : D' →+* Cr') (DtoC : Dr →+* Cr) (C'toC : Cr' →+* Cr)
    (comm : DtoC.comp toD = C'toC.comp toC')
    {F : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} DtoC)
          (ModuleCat.extendScalars.{u, u, u} C'toC) ⥤ ModuleCat.{u} D'}
    (e : ∀ X, F.obj X ≃ₗ[D']
      MilnorPatching.compatiblePairsModule.{u} toD toC' DtoC C'toC comm X)
    (adj : ModuleGlueing.extensionOfScalarsToPullback.{u} toD toC' DtoC C'toC comm ⊣ F)
    (form : ∀ (L : ModuleCat.{u} D') (X) (h : L ⟶ F.obj X) (l : L),
      (e X (h l)).1.1 = ((adj.homEquiv L X).symm h).fst ((1 : Dr) ⊗ₜ[D',toD] l) ∧
        (e X (h l)).1.2 = ((adj.homEquiv L X).symm h).snd ((1 : Cr') ⊗ₜ[D',toC'] l))
    (L : ModuleCat.{u} D') (X) (h : L ⟶ F.obj X)
    (α : (ModuleCat.extendScalars toD).obj L ⟶ X.fst)
    (α' : (ModuleCat.extendScalars toC').obj L ⟶ X.snd)
    (hα : Function.Bijective α) (hα' : Function.Bijective α')
    (h1 : ∀ l : L, (e X (h l)).1.1 = α ((1 : Dr) ⊗ₜ[D',toD] l))
    (h2 : ∀ l : L, (e X (h l)).1.2 = α' ((1 : Cr') ⊗ₜ[D',toC'] l)) :
    IsIso ((adj.homEquiv L X).symm h) := by
  refine (CategoricalPullback.isIso_iff (ModuleCat.extendScalars DtoC)
    (ModuleCat.extendScalars C'toC) _).2 ⟨?_, ?_⟩
  · rw [show ((adj.homEquiv L X).symm h).fst = α from
      ModuleCat.ExtendScalars.hom_ext (f := toD) (M := L) (N := X.fst) fun l =>
        ((form L X h l).1.symm.trans (h1 l))]
    exact (ConcreteCategory.isIso_iff_bijective α).2 hα
  · rw [show ((adj.homEquiv L X).symm h).snd = α' from
      ModuleCat.ExtendScalars.hom_ext (f := toC') (M := L) (N := X.snd) fun l =>
        ((form L X h l).2.symm.trans (h2 l))]
    exact (ConcreteCategory.isIso_iff_bijective α').2 hα'

/-- A map into a right-adjoint value whose transpose is an isomorphism is itself one, as soon as
the unit is. -/
theorem isIso_of_isIso_transpose {C₁ D₁ : Type*} [Category C₁] [Category D₁]
    {E : C₁ ⥤ D₁} {F : D₁ ⥤ C₁} (adj : E ⊣ F) {L : C₁} {Z : D₁} (h : L ⟶ F.obj Z)
    [IsIso (adj.unit.app L)] [IsIso ((adj.homEquiv L Z).symm h)] : IsIso h := by
  rw [show h = adj.unit.app L ≫ F.map ((adj.homEquiv L Z).symm h) from
    ((adj.homEquiv L Z).apply_symm_apply h).symm.trans
      (adj.homEquiv_unit L Z ((adj.homEquiv L Z).symm h))]
  infer_instance

/-- **A semilinear map into a module of compatible pairs is bijective when its two coordinate
maps are.**  The abstract form of the chart step: `G` is the sections of the glued module over
the chart, `E` identifies them with the compatible pairs, and `u` is the map whose bijectivity
is wanted; all of the scheme-level data has been discharged into `E`, `u`, `α` and `α'`. -/
theorem bijective_of_components
    {D' Dr Cr' Cr : Type u} [CommRing D'] [CommRing Dr] [CommRing Cr'] [CommRing Cr]
    (toD : D' →+* Dr) (toC' : D' →+* Cr') (DtoC : Dr →+* Cr) (C'toC : Cr' →+* Cr)
    (comm : DtoC.comp toD = C'toC.comp toC')
    {F : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} DtoC)
          (ModuleCat.extendScalars.{u, u, u} C'toC) ⥤ ModuleCat.{u} D'}
    (e : ∀ X, F.obj X ≃ₗ[D']
      MilnorPatching.compatiblePairsModule.{u} toD toC' DtoC C'toC comm X)
    (adj : ModuleGlueing.extensionOfScalarsToPullback.{u} toD toC' DtoC C'toC comm ⊣ F)
    (form : ∀ (L : ModuleCat.{u} D') (X) (h : L ⟶ F.obj X) (l : L),
      (e X (h l)).1.1 = ((adj.homEquiv L X).symm h).fst ((1 : Dr) ⊗ₜ[D',toD] l) ∧
        (e X (h l)).1.2 = ((adj.homEquiv L X).symm h).snd ((1 : Cr') ⊗ₜ[D',toC'] l))
    (L : ModuleCat.{u} D') (X) (hL : IsIso (adj.unit.app L))
    {G : Type u} [AddCommGroup G] [Module D' G]
    (E : G ≃ₗ[D'] MilnorPatching.compatiblePairsModule.{u} toD toC' DtoC C'toC comm X)
    (u : L →ₗ[D'] G)
    (α : (ModuleCat.extendScalars toD).obj L ⟶ X.fst)
    (α' : (ModuleCat.extendScalars toC').obj L ⟶ X.snd)
    (hα : Function.Bijective α) (hα' : Function.Bijective α')
    (h1 : ∀ l : L, (E (u l)).1.1 = α ((1 : Dr) ⊗ₜ[D',toD] l))
    (h2 : ∀ l : L, (E (u l)).1.2 = α' ((1 : Cr') ⊗ₜ[D',toC'] l)) :
    Function.Bijective u := by
  let h : L ⟶ F.obj X := ModuleCat.ofHom (X := L) (Y := F.obj X)
    (((e X).symm.toLinearMap).comp (E.toLinearMap.comp u))
  have hh : ∀ l : L, e X (h l) = E (u l) := fun l => (e X).apply_symm_apply _
  have : IsIso ((adj.homEquiv L X).symm h) :=
    isIso_transpose_of_components toD toC' DtoC C'toC comm e adj form L X h α α' hα hα'
      (fun l => (congrArg (fun z => z.1.1) (hh l)).trans (h1 l))
      (fun l => (congrArg (fun z => z.1.2) (hh l)).trans (h2 l))
  have : IsIso h := isIso_of_isIso_transpose adj h
  have hu : ⇑u = ⇑E.symm ∘ ⇑(e X) ∘ ⇑h :=
    funext fun l => (E.symm_apply_apply (u l)).symm.trans (congrArg E.symm (hh l)).symm
  rw [hu]
  exact E.symm.bijective.comp ((e X).bijective.comp (ConcreteCategory.bijective_of_isIso h))

/-! ### The unit over one chart -/

/-- If a morphism followed by a projection to a pushforward is the unit, then on sections the
projection of its value is the pullback of the section. -/
private theorem app_comp_eq_pullbackSection {A B : Scheme.{u}} (p : A ⟶ B) (M : B.Modules)
    {P : B.Modules} (u : M ⟶ P) (π : P ⟶ (Scheme.Modules.pushforward p).obj
      ((Scheme.Modules.pullback p).obj M))
    (h : u ≫ π = (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) (U : B.Opens)
    (a : Γ(M, U)) :
    π.app U (u.app U a) = Scheme.Modules.pullbackSection p M U (p ⁻¹ᵁ U) le_rfl a :=
  ((modules_comp_app u π U a).symm.trans (congrArg (fun k => k.app U a) h)).trans
    (pullbackSection_preimage p M U a).symm

/-- The quasi-coherence of the target of the comparison functor's value. -/
private theorem isQuasicoherent_baseChange_target
    (hi : Stacks.Thickenings.IsThickening i) [IsAffineHom f]
    (M : V'.Modules) [M.IsQuasicoherent] :
    ((baseChangeTripleFunctor i f hi g).obj M).target.IsQuasicoherent :=
  @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
    (targetRestriction i f g).toLRSHom.toShHom M ‹_›

/-- The quasi-coherence of the ambient of the comparison functor's value. -/
private theorem isQuasicoherent_baseChange_ambient
    (hi : Stacks.Thickenings.IsThickening i) [IsAffineHom f]
    (M : V'.Modules) [M.IsQuasicoherent] :
    ((baseChangeTripleFunctor i f hi g).obj M).ambient.IsQuasicoherent :=
  @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
    (ambientRestriction i f g).toLRSHom.toShHom M ‹_›

/-- A formula for a ring element's image under `appLE` over the full preimage, in terms of
`app`. -/
private theorem eq_app_of_eq_appLE {A B : Scheme.{u}} (p : A ⟶ B) {U : B.Opens}
    {x : Γ(A, p ⁻¹ᵁ U)} {d : Γ(B, U)} (h : x = p.appLE U (p ⁻¹ᵁ U) le_rfl d) :
    x = (p.app U).hom d := by
  rw [h, Scheme.Hom.appLE_eq_app]

open Stacks.Thickenings in
/-- The first projection of the glued module, on the sections of
`Stacks.Pushout.gluingUnitApp`, is the pullback of the section. -/
theorem gluingUnitApp_app_fst_app (hi : IsThickening i) [IsAffineHom f] (M : V'.Modules)
    (U : V'.Opens) (a : Γ(M, U)) :
    (pullback.fst ((glueTargetNat i f g).app ((baseChangeTripleFunctor i f hi g).obj M))
        ((glueAmbientNat i f g).app ((baseChangeTripleFunctor i f hi g).obj M))).app U
        ((gluingUnitApp i f g hi M).app U a) =
      Scheme.Modules.pullbackSection (targetRestriction i f g) M U
        (targetRestriction i f g ⁻¹ᵁ U) le_rfl a :=
  app_comp_eq_pullbackSection _ M _ _ (gluingUnitApp_fst i f g hi M) U a

open Stacks.Thickenings in
/-- The companion of `Stacks.Pushout.gluingUnitApp_app_fst_app` on `U'`. -/
theorem gluingUnitApp_app_snd_app (hi : IsThickening i) [IsAffineHom f] (M : V'.Modules)
    (U : V'.Opens) (a : Γ(M, U)) :
    (pullback.snd ((glueTargetNat i f g).app ((baseChangeTripleFunctor i f hi g).obj M))
        ((glueAmbientNat i f g).app ((baseChangeTripleFunctor i f hi g).obj M))).app U
        ((gluingUnitApp i f g hi M).app U a) =
      Scheme.Modules.pullbackSection (ambientRestriction i f g) M U
        (ambientRestriction i f g ⁻¹ᵁ U) le_rfl a :=
  app_comp_eq_pullbackSection _ M _ _ (gluingUnitApp_snd i f g hi M) U a

open Stacks.Thickenings in
/-- **The sections of a module flat over `Y'` over an affine chart are flat over the chart's
ring fibre product.** -/
theorem flat_chartSections_of_isFlatOver (_hi : IsThickening i) [IsAffineHom f]
    (M : V'.Modules) [M.IsQuasicoherent]
    (hM : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom M)
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W)
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    {base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
    (eB : Γ(pushout i f, W) ≃+* base.fibreProduct)
    (hD' : s.toD'.comp eB.toRingHom = (g.appLE W U hUW).hom) :
    Module.Flat base.fibreProduct
      ((ModuleCat.restrictScalars.{u, u, u} s.toD').obj (ModuleCat.of Γ(V', U) Γ(M, U))) := by
  have h0 : @Module.Flat Γ(pushout i f, W) Γ(M, U) _ _
      (Module.compHom Γ(M, U) (g.appLE W U hUW).hom) :=
    ((AlgebraicGeometry.isFlatOver_tfae g M).out 1 2 rfl rfl).mp hM U hU W hW hUW
  have h2 : (g.appLE W U hUW).hom.comp eB.symm.toRingHom = s.toD' :=
    RingHom.ext fun x => by
      rw [← hD']
      exact congrArg s.toD' (eB.apply_symm_apply x)
  have h1 := flat_of_ringEquiv_base eB.symm (g.appLE W U hUW).hom h0
  rw [h2] at h1
  exact h1

open Stacks.Thickenings in
/-- **The two components of the chart comparison of the unit.** -/
theorem exists_chartUnitComponents (hi : IsThickening i) [IsAffineHom f]
    (M : V'.Modules) [M.IsQuasicoherent]
    {W : (pushout i f).Opens} {U : V'.Opens} (hU : IsAffineOpen U)
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    {base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
    (kD : s.D ≃+* Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U))
    (kC' : s.C' ≃+* Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U))
    (kC : s.C ≃+* Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U))
    (hkD1 : ∀ d : Γ(V', U), kD (s.toD d) =
      (targetRestriction i f g).appLE U (targetRestriction i f g ⁻¹ᵁ U) le_rfl d)
    (hkC'1 : ∀ d : Γ(V', U), kC' (s.toC' d) =
      (ambientRestriction i f g).appLE U (ambientRestriction i f g ⁻¹ᵁ U) le_rfl d)
    (hDC : ∀ z : s.D, kC (s.DtoC z) =
      ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U)).hom (kD z))
    (hC'C : ∀ z : s.C', kC (s.C'toC z) =
      ((commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U)).hom (kC' z)) :
    ∃ (Xc : MilnorPatching.RelativeModuleFibreProductSituation.CompatibleModules.{u, u, u, u, u} s)
      (E : Γ((tripleGluingFunctor i f g).obj ((baseChangeTripleFunctor i f hi g).obj M), U)
          ≃ₗ[Γ(V', U)]
        MilnorPatching.compatiblePairsModule.{u} s.toD s.toC' s.DtoC s.C'toC
          s.relativeSquare_comm Xc)
      (β : (ModuleCat.extendScalars s.toD).obj (ModuleCat.of Γ(V', U) Γ(M, U)) ⟶ Xc.fst)
      (γ : (ModuleCat.extendScalars s.toC').obj (ModuleCat.of Γ(V', U) Γ(M, U)) ⟶ Xc.snd),
      Function.Bijective β ∧ Function.Bijective γ ∧
        (∀ a : Γ(M, U), (E ((gluingUnitApp i f g hi M).app U a)).1.1 =
          β ((1 : s.D) ⊗ₜ[Γ(V', U),s.toD] a)) ∧
          (∀ a : Γ(M, U), (E ((gluingUnitApp i f g hi M).app U a)).1.2 =
            γ ((1 : s.C') ⊗ₜ[Γ(V', U),s.toC'] a)) := by
  have := isQuasicoherent_baseChange_target i f g hi M
  have := isQuasicoherent_baseChange_ambient i f g hi M
  have hkDapp := fun d => eq_app_of_eq_appLE _ (hkD1 d)
  have hkC'app := fun d => eq_app_of_eq_appLE _ (hkC'1 d)
  refine Exists.elim (exists_chartGluingSectionsCompatiblePairsLinearEquiv i f g hi
      ((baseChangeTripleFunctor i f hi g).obj M) hU s kD kC' kC hDC hC'C hkDapp hkC'app)
    fun Xc h7 => Exists.elim h7 fun E h8 => Exists.elim h8 fun eD h9 =>
    Exists.elim h9 fun eA h10 => ?_
  obtain ⟨hDadd, hDsmul, hAadd, hAsmul, hfst, hsnd⟩ := h10
  refine Exists.elim (exists_chartPullbackSectionsHom (targetRestriction i f g) M hU
      (isAffineOpen_targetChart i f g hi hU) s.toD kD hkD1 Xc.fst eD hDadd hDsmul)
    fun β hβ => Exists.elim (exists_chartPullbackSectionsHom (ambientRestriction i f g) M hU
      (isAffineOpen_ambientChart i f g hi hU) s.toC' kC' hkC'1 Xc.snd eA hAadd hAsmul)
    fun γ hγ => ?_
  refine ⟨Xc, E, β, γ, hβ.1, hγ.1, fun a => ?_, fun a => ?_⟩
  · exact eD.injective ((hfst _).trans
      ((gluingUnitApp_app_fst_app i f g hi M U a).trans (hβ.2 a).symm))
  · exact eA.injective ((hsnd _).trans
      ((gluingUnitApp_app_snd_app i f g hi M U a).trans (hγ.2 a).symm))

open Stacks.Thickenings in
/-- **The unit of the comparison is bijective on the sections over an affine chart.**  Over the
chart the sections of the glued module are the compatible pairs of the chart's Milnor patching
situation, the sections of the unit are the unit of [Stacks Project, Tag 07RW], and that unit is
invertible because `Γ(M, U)` is flat over the ring fibre product. -/
theorem bijective_gluingUnitApp_of_chartData (hi : IsThickening i) [IsAffineHom f]
    (M : V'.Modules) [M.IsQuasicoherent]
    (hM : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom M)
    {W : (pushout i f).Opens} (hW : IsAffineOpen W) {U : V'.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W)
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    {base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
    (eB : Γ(pushout i f, W) ≃+* base.fibreProduct)
    (kD : s.D ≃+* Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U))
    (kC' : s.C' ≃+* Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U))
    (kC : s.C ≃+* Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U))
    (hD' : s.toD'.comp eB.toRingHom = (g.appLE W U hUW).hom)
    (hkD1 : ∀ d : Γ(V', U), kD (s.toD d) =
      (targetRestriction i f g).appLE U (targetRestriction i f g ⁻¹ᵁ U) le_rfl d)
    (hkC'1 : ∀ d : Γ(V', U), kC' (s.toC' d) =
      (ambientRestriction i f g).appLE U (ambientRestriction i f g ⁻¹ᵁ U) le_rfl d)
    (hDC : ∀ z : s.D, kC (s.DtoC z) =
      ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U)).hom (kD z))
    (hC'C : ∀ z : s.C', kC (s.C'toC z) =
      ((commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U)).hom (kC' z)) :
    Function.Bijective ((gluingUnitApp i f g hi M).app U) := by
  refine Exists.elim (exists_chartUnitComponents i f g hi M hU s kD kC' kC hkD1 hkC'1 hDC hC'C)
    fun Xc h1 => Exists.elim h1 fun E h2 => Exists.elim h2 fun β h3 =>
    Exists.elim h3 fun γ h4 => ?_
  obtain ⟨hβbij, hγbij, hβval, hγval⟩ := h4
  obtain ⟨F, e07, adj, form, hunit07, -⟩ := exists_relativeFlatAdjunction s
  exact bijective_of_components s.toD s.toC' s.DtoC s.C'toC s.relativeSquare_comm e07 adj form
    (ModuleCat.of Γ(V', U) Γ(M, U)) Xc
    (hunit07 (ModuleCat.of Γ(V', U) Γ(M, U))
      (flat_chartSections_of_isFlatOver i f g hi M hM hW hU hUW s eB hD'))
    E (Scheme.Modules.sectionsLinearMap (gluingUnitApp i f g hi M) U) β γ hβbij hγbij
    hβval hγval

/-! ### The charts cover `V'`, and the two detection criteria -/

/-- The affine opens of `V'` lying above an affine open of `Y'`. -/
abbrev chartIndex : Type u :=
  Σ W : (pushout i f).affineOpens,
    {U : V'.affineOpens // (U : V'.Opens) ≤ g ⁻¹ᵁ (W : (pushout i f).Opens)}

/-- The open of `V'` an index names. -/
abbrev chartOpen (p : chartIndex i f g) : V'.Opens := (p.2.1 : V'.Opens)

/-- **The charts cover `V'`.**  Every point of `V'` lies in an affine open contained in the
preimage of an affine open of `Y'` containing its image, the affine opens of a scheme being a
basis of its topology. -/
theorem isOpenCover_chartOpen : TopologicalSpace.IsOpenCover (chartOpen i f g) := by
  refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)
  obtain ⟨W, hWaff, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (pushout i f).isBasis_affineOpens (show g.base x ∈ (⊤ : (pushout i f).Opens) from trivial)
  obtain ⟨U, hUaff, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    V'.isBasis_affineOpens (show x ∈ g ⁻¹ᵁ W from hxW)
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨⟨⟨W, hWaff⟩, ⟨⟨U, hUaff⟩, hUW⟩⟩, hxU⟩

/-- The sections of a morphism of modules over an open, written as the value of the underlying
morphism of presheaves at that open. -/
theorem val_app_bijective {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N) (U : Z.Opens)
    (h : Function.Bijective (φ.app U)) : Function.Bijective (φ.val.app (op U)) := h

/-- **Invertibility of a morphism of quasi-coherent modules is detected on an affine open
cover**, with quasi-coherence of the two modules taken as hypotheses rather than instances. -/
theorem isIso_of_bijective_app_of_isOpenCover' {Z : Scheme.{u}} {M N : Z.Modules}
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) (φ : M ⟶ N) {J : Type*}
    (W : J → Z.Opens) (hcover : TopologicalSpace.IsOpenCover W)
    (hW : ∀ j, IsAffineOpen (W j)) (h : ∀ j, Function.Bijective (φ.app (W j))) : IsIso φ :=
  have := hM
  have := hN
  Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover φ W hcover hW
    fun j => val_app_bijective φ (W j) (h j)

/-- The preimage of the chart cover under a morphism into `V'` is an open cover. -/
theorem isOpenCover_preimage_chartOpen {Z : Scheme.{u}} (p : Z ⟶ V') :
    TopologicalSpace.IsOpenCover (fun q : chartIndex i f g => p ⁻¹ᵁ chartOpen i f g q) :=
  TopologicalSpace.IsOpenCover.comap (isOpenCover_chartOpen i f g) p.base.hom

/-! ### The counit over one chart -/

/-- **A map out of the sections over an affine chart of the pullback of a module**, bijective
because the chart base change identifies it with a bijection of modules over the chart's ring. -/
theorem bijective_chartPullbackSectionsOut {V' Z : Scheme.{u}} (p : Z ⟶ V') (M : V'.Modules)
    [M.IsQuasicoherent] {U : V'.Opens} (hU : IsAffineOpen U) (hpU : IsAffineOpen (p ⁻¹ᵁ U))
    {D : Type u} [CommRing D] (φ : Γ(V', U) →+* D) (k : D ≃+* Γ(Z, p ⁻¹ᵁ U))
    (hk : ∀ d : Γ(V', U), k (φ d) = (p.appLE U (p ⁻¹ᵁ U) le_rfl) d)
    (Nt : Z.Modules) (c : (Scheme.Modules.pullback p).obj M ⟶ Nt)
    (P : ModuleCat.{u} D) (e : P ≃ Γ(Nt, p ⁻¹ᵁ U))
    (hadd : ∀ x y : P, e (x + y) = e x + e y)
    (hsmul : ∀ (z : D) (x : P), e (z • x) = k z • e x)
    (δ : (ModuleCat.extendScalars φ).obj (ModuleCat.of Γ(V', U) Γ(M, U)) ⟶ P)
    (hδ : Function.Bijective δ)
    (hval : ∀ a : Γ(M, U), e (δ ((1 : D) ⊗ₜ[Γ(V', U),φ] a)) =
      c.app (p ⁻¹ᵁ U) (Scheme.Modules.pullbackSection p M U (p ⁻¹ᵁ U) le_rfl a)) :
    Function.Bijective (c.app (p ⁻¹ᵁ U)) :=
  Stacks.ModuleCat.bijective_of_extendScalarsTargetOut k φ (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom hk
    (ModuleCat.of Γ(V', U) Γ(M, U)) _
    (affinePullbackSectionsBaseChangeIso p M hU hpU le_rfl)
    (ModuleCat.of Γ(Z, p ⁻¹ᵁ U) Γ(Nt, p ⁻¹ᵁ U))
    (ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap c (p ⁻¹ᵁ U))) P e hadd hsmul
    δ hδ (fun a => (hval a).trans (congrArg (fun z => c.app (p ⁻¹ᵁ U) z)
      (affinePullbackSectionsBaseChangeIso_one_tmul p M hU hpU le_rfl a).symm))

/-- **The transpose of a morphism into a pushforward, on the sections of a pulled-back
section.**  The transpose composed with the unit is the morphism itself, and the unit on sections
over the full preimage is `AlgebraicGeometry.Scheme.Modules.pullbackSection`. -/
theorem transpose_app_pullbackSection {A B : Scheme.{u}} (p : A ⟶ B) (M : B.Modules)
    (N : A.Modules) (h : M ⟶ (Scheme.Modules.pushforward p).obj N) (U : B.Opens) (z : Γ(M, U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).symm h).app (p ⁻¹ᵁ U)
        (Scheme.Modules.pullbackSection p M U (p ⁻¹ᵁ U) le_rfl z) = h.app U z := by
  have key := ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).apply_symm_apply h
  rw [CategoryTheory.Adjunction.homEquiv_unit] at key
  refine Eq.trans ?_ (congrArg
    (fun t : M ⟶ (Scheme.Modules.pushforward p).obj N => t.app U z) key)
  rw [pullbackSection_preimage]
  rfl

/-- **The two components of the counit of [Stacks Project, Tag 07RW]**, as bijections out of the
two base changes of the compatible-pairs module, given by the two coordinates of a pair. -/
theorem exists_counitComponents
    {D' Dr Cr' Cr : Type u} [CommRing D'] [CommRing Dr] [CommRing Cr'] [CommRing Cr]
    (toD : D' →+* Dr) (toC' : D' →+* Cr') (DtoC : Dr →+* Cr) (C'toC : Cr' →+* Cr)
    (comm : DtoC.comp toD = C'toC.comp toC')
    {F : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} DtoC)
          (ModuleCat.extendScalars.{u, u, u} C'toC) ⥤ ModuleCat.{u} D'}
    (e : ∀ X, F.obj X ≃ₗ[D']
      MilnorPatching.compatiblePairsModule.{u} toD toC' DtoC C'toC comm X)
    (adj : ModuleGlueing.extensionOfScalarsToPullback.{u} toD toC' DtoC C'toC comm ⊣ F)
    (form : ∀ (L : ModuleCat.{u} D') (X) (h : L ⟶ F.obj X) (l : L),
      (e X (h l)).1.1 = ((adj.homEquiv L X).symm h).fst ((1 : Dr) ⊗ₜ[D',toD] l) ∧
        (e X (h l)).1.2 = ((adj.homEquiv L X).symm h).snd ((1 : Cr') ⊗ₜ[D',toC'] l))
    (hcounit : IsIso adj.counit) (X) :
    ∃ (δ : (ModuleCat.extendScalars toD).obj (F.obj X) ⟶ X.fst)
      (δ' : (ModuleCat.extendScalars toC').obj (F.obj X) ⟶ X.snd),
      Function.Bijective δ ∧ Function.Bijective δ' ∧
        (∀ y : F.obj X, δ ((1 : Dr) ⊗ₜ[D',toD] y) = (e X y).1.1) ∧
        (∀ y : F.obj X, δ' ((1 : Cr') ⊗ₜ[D',toC'] y) = (e X y).1.2) := by
  have := hcounit
  have : IsIso (adj.counit.app X) := NatIso.isIso_app_of_isIso adj.counit X
  obtain ⟨hfst, hsnd⟩ := (CategoricalPullback.isIso_iff (ModuleCat.extendScalars DtoC)
    (ModuleCat.extendScalars C'toC) (adj.counit.app X)).1 ‹_›
  have := hfst
  have := hsnd
  have hid : (adj.homEquiv (F.obj X) X).symm (𝟙 (F.obj X)) = adj.counit.app X := by
    rw [CategoryTheory.Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id,
      CategoryTheory.Category.id_comp]
  refine ⟨(adj.counit.app X).fst, (adj.counit.app X).snd,
    (ConcreteCategory.isIso_iff_bijective _).1 hfst,
    (ConcreteCategory.isIso_iff_bijective _).1 hsnd, fun y => ?_, fun y => ?_⟩
  · have h0 := (form (F.obj X) X (𝟙 (F.obj X)) y).1
    rw [hid] at h0
    exact h0.symm
  · have h0 := (form (F.obj X) X (𝟙 (F.obj X)) y).2
    rw [hid] at h0
    exact h0.symm

/-- **The two components of the counit of [Stacks Project, Tag 07RW], transported along a linear
identification of the right adjoint's value.**  `G` is the sections of the glued module over an
affine chart and `E` the identification of them with the compatible pairs; the two bijections
are the counit's components read through it. -/
theorem exists_counitChartHom
    {D' Dr Cr' Cr : Type u} [CommRing D'] [CommRing Dr] [CommRing Cr'] [CommRing Cr]
    (toD : D' →+* Dr) (toC' : D' →+* Cr') (DtoC : Dr →+* Cr) (C'toC : Cr' →+* Cr)
    (comm : DtoC.comp toD = C'toC.comp toC')
    {F : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} DtoC)
          (ModuleCat.extendScalars.{u, u, u} C'toC) ⥤ ModuleCat.{u} D'}
    (e : ∀ X, F.obj X ≃ₗ[D']
      MilnorPatching.compatiblePairsModule.{u} toD toC' DtoC C'toC comm X)
    (adj : ModuleGlueing.extensionOfScalarsToPullback.{u} toD toC' DtoC C'toC comm ⊣ F)
    (form : ∀ (L : ModuleCat.{u} D') (X) (h : L ⟶ F.obj X) (l : L),
      (e X (h l)).1.1 = ((adj.homEquiv L X).symm h).fst ((1 : Dr) ⊗ₜ[D',toD] l) ∧
        (e X (h l)).1.2 = ((adj.homEquiv L X).symm h).snd ((1 : Cr') ⊗ₜ[D',toC'] l))
    (hcounit : IsIso adj.counit) (X)
    {G : Type u} [AddCommGroup G] [Module D' G]
    (E : G ≃ₗ[D'] MilnorPatching.compatiblePairsModule.{u} toD toC' DtoC C'toC comm X) :
    ∃ (δ : (ModuleCat.extendScalars toD).obj (ModuleCat.of D' G) ⟶ X.fst)
      (δ' : (ModuleCat.extendScalars toC').obj (ModuleCat.of D' G) ⟶ X.snd),
      Function.Bijective δ ∧ Function.Bijective δ' ∧
        (∀ z : G, δ ((1 : Dr) ⊗ₜ[D',toD] z) = (E z).1.1) ∧
        (∀ z : G, δ' ((1 : Cr') ⊗ₜ[D',toC'] z) = (E z).1.2) := by
  obtain ⟨δ₀, δ₀', hδ₀, hδ₀', hδ₀val, hδ₀'val⟩ :=
    exists_counitComponents toD toC' DtoC C'toC comm e adj form hcounit X
  let θ : ModuleCat.of D' G ⟶ F.obj X :=
    ModuleCat.ofHom (X := ModuleCat.of D' G) (Y := F.obj X) (E ≪≫ₗ (e X).symm).toLinearMap
  have hθ : ∀ z : G, e X (θ z) = E z := fun z => (e X).apply_symm_apply _
  have : IsIso θ := (ConcreteCategory.isIso_iff_bijective θ).2 (E ≪≫ₗ (e X).symm).bijective
  have hmapD : Function.Bijective ((ModuleCat.extendScalars toD).map θ) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hmapC' : Function.Bijective ((ModuleCat.extendScalars toC').map θ) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  refine ⟨(ModuleCat.extendScalars toD).map θ ≫ δ₀, (ModuleCat.extendScalars toC').map θ ≫ δ₀',
    hδ₀.comp hmapD, hδ₀'.comp hmapC', fun z => ?_, fun z => ?_⟩
  · exact (congrArg (fun y => δ₀ y) (ModuleCat.ExtendScalars.map_tmul toD θ (1 : Dr) z)).trans
      ((hδ₀val (θ z)).trans (congrArg (fun w => w.1.1) (hθ z)))
  · exact (congrArg (fun y => δ₀' y) (ModuleCat.ExtendScalars.map_tmul toC' θ (1 : Cr') z)).trans
      ((hδ₀'val (θ z)).trans (congrArg (fun w => w.1.2) (hθ z)))

open Stacks.Thickenings in
/-- **The counit of the comparison is bijective on the sections over an affine chart.**  Over the
chart of an affine open `U` of `V'` the sections of the glued module are the compatible pairs of
the chart's Milnor patching situation, and the two components of the counit become the two
components of the counit of [Stacks Project, Tag 07RW], which is invertible with no flatness
hypothesis. -/
theorem bijective_counit_app_of_chartData (hi : IsThickening i) [IsAffineHom f]
    (T : GluingTriple i f g) [T.target.IsQuasicoherent] [T.ambient.IsQuasicoherent]
    {W : (pushout i f).Opens} {U : V'.Opens} (hU : IsAffineOpen U)
    {I : Ideal Γ(X', pushout.inl i f ⁻¹ᵁ W)}
    {base : RingFibreProduct.Situation (chartToBase i f W) (chartSurjection i f W) I}
    (s : MilnorPatching.RelativeModuleFibreProductSituation (D' := Γ(V', U)) base)
    (kD : s.D ≃+* Γ(pullback (pushout.inr i f) g, targetRestriction i f g ⁻¹ᵁ U))
    (kC' : s.C' ≃+* Γ(pullback (pushout.inl i f) g, ambientRestriction i f g ⁻¹ᵁ U))
    (kC : s.C ≃+* Γ(pullback (i ≫ pushout.inl i f) g, commonRestriction i f g ⁻¹ᵁ U))
    (hkD1 : ∀ d : Γ(V', U), kD (s.toD d) =
      (targetRestriction i f g).appLE U (targetRestriction i f g ⁻¹ᵁ U) le_rfl d)
    (hkC'1 : ∀ d : Γ(V', U), kC' (s.toC' d) =
      (ambientRestriction i f g).appLE U (ambientRestriction i f g ⁻¹ᵁ U) le_rfl d)
    (hDC : ∀ z : s.D, kC (s.DtoC z) =
      ((commonToTarget i f g).appLE (targetRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_targetChart i f g U)).hom (kD z))
    (hC'C : ∀ z : s.C', kC (s.C'toC z) =
      ((commonToAmbient i f g).appLE (ambientRestriction i f g ⁻¹ᵁ U)
        (commonRestriction i f g ⁻¹ᵁ U) (commonChart_le_ambientChart i f g U)).hom (kC' z)) :
    Function.Bijective ((GluingTripleHom.target
        ((baseChangeTripleAdjunction i f g hi).counit.app T)).app
      (targetRestriction i f g ⁻¹ᵁ U)) ∧
      Function.Bijective ((GluingTripleHom.ambient
        ((baseChangeTripleAdjunction i f g hi).counit.app T)).app
      (ambientRestriction i f g ⁻¹ᵁ U)) := by
  have : ((tripleGluingFunctor i f g).obj T).IsQuasicoherent :=
    isQuasicoherent_tripleGluingFunctor_obj i f g hi T ‹_› ‹_›
  have hkDapp := fun d => eq_app_of_eq_appLE _ (hkD1 d)
  have hkC'app := fun d => eq_app_of_eq_appLE _ (hkC'1 d)
  obtain ⟨Xc, E, eD, eA, hDadd, hDsmul, hAadd, hAsmul, hfst, hsnd⟩ :=
    exists_chartGluingSectionsCompatiblePairsLinearEquiv i f g hi T hU s
      kD kC' kC hDC hC'C hkDapp hkC'app
  obtain ⟨F, e07, adj, form, -, hcounit⟩ := exists_relativeFlatAdjunction s
  obtain ⟨δ, δ', hδ, hδ', hδval, hδ'val⟩ :=
    exists_counitChartHom s.toD s.toC' s.DtoC s.C'toC s.relativeSquare_comm e07 adj form
      hcounit Xc E
  constructor
  · rw [baseChangeTripleAdjunction_counit_app_target i f g hi T]
    refine bijective_chartPullbackSectionsOut (targetRestriction i f g)
      ((tripleGluingFunctor i f g).obj T) hU (isAffineOpen_targetChart i f g hi hU) s.toD kD hkD1
      T.target _ Xc.fst eD hDadd hDsmul δ hδ fun z =>
        ((congrArg eD (hδval z)).trans (hfst z)).trans
          (transpose_app_pullbackSection (targetRestriction i f g)
            ((tripleGluingFunctor i f g).obj T) T.target (pullback.fst _ _) U z).symm
  · rw [baseChangeTripleAdjunction_counit_app_ambient i f g hi T]
    refine bijective_chartPullbackSectionsOut (ambientRestriction i f g)
      ((tripleGluingFunctor i f g).obj T) hU (isAffineOpen_ambientChart i f g hi hU) s.toC' kC'
      hkC'1 T.ambient _ Xc.snd eA hAadd hAsmul δ' hδ' fun z =>
        ((congrArg eA (hδ'val z)).trans (hsnd z)).trans
          (transpose_app_pullbackSection (ambientRestriction i f g)
            ((tripleGluingFunctor i f g).obj T) T.ambient (pullback.snd _ _) U z).symm

/-! ### The unit and the counit are isomorphisms -/

open Stacks.Thickenings in
/-- **The unit of the comparison is an isomorphism on a quasi-coherent module flat over `Y'`.**
Bijectivity on the sections over each chart of the cover is
`Stacks.Pushout.bijective_gluingUnitApp_of_chartData`, and invertibility is detected on an affine
open cover. -/
theorem isIso_gluingUnitApp (hi : IsThickening i) [IsAffineHom f] (M : V'.Modules)
    [M.IsQuasicoherent] (hM : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom M) :
    IsIso (gluingUnitApp i f g hi M) := by
  have hqt := isQuasicoherent_baseChange_target i f g hi M
  have hqa := isQuasicoherent_baseChange_ambient i f g hi M
  have : ((tripleGluingFunctor i f g).obj
      ((baseChangeTripleFunctor i f hi g).obj M)).IsQuasicoherent :=
    isQuasicoherent_tripleGluingFunctor_obj i f g hi _ hqt hqa
  refine isIso_of_bijective_app_of_isOpenCover' ‹M.IsQuasicoherent› ‹_›
    (gluingUnitApp i f g hi M) (chartOpen i f g) (isOpenCover_chartOpen i f g)
    (fun q => q.2.1.2) fun q => ?_
  obtain ⟨I, base, s, eB, kD, kC', kC, hD', hkD1, -, hkC'1, -, hDC, hC'C⟩ :=
    exists_chartData i f g hi q.1.2 q.2.1.2 q.2.2
  exact bijective_gluingUnitApp_of_chartData i f g hi M hM q.1.2 q.2.1.2 q.2.2 s eB kD kC' kC
    hD' hkD1 hkC'1 hDC hC'C

/-- **A morphism of triples with both components invertible is invertible.** -/
theorem isIso_gluingTripleHom {T T' : GluingTriple i f g} (φ : T ⟶ T')
    (ht : IsIso (GluingTripleHom.target φ)) (ha : IsIso (GluingTripleHom.ambient φ)) :
    IsIso φ := by
  have := ht
  have := ha
  refine ⟨⟨⟨inv (GluingTripleHom.target φ), inv (GluingTripleHom.ambient φ), ?_⟩, ?_, ?_⟩⟩
  · rw [CategoryTheory.Functor.map_inv, CategoryTheory.Functor.map_inv, IsIso.inv_comp_eq,
      ← Category.assoc, IsIso.eq_comp_inv]
    exact (GluingTripleHom.comm φ).symm
  · exact gluingTripleHom_ext i f g (IsIso.hom_inv_id _) (IsIso.hom_inv_id _)
  · exact gluingTripleHom_ext i f g (IsIso.inv_hom_id _) (IsIso.inv_hom_id _)

open Stacks.Thickenings in
/-- **The counit of the comparison is an isomorphism on a triple of quasi-coherent modules flat
over `Y` and over `X'`.**  Both components are bijective on the sections over the charts of the
cover by `Stacks.Pushout.bijective_counit_app_of_chartData`, and those charts cover `V` and `U'`.
-/
theorem isIso_baseChangeTripleAdjunction_counit_app (hi : IsThickening i) [IsAffineHom f]
    (T : GluingTriple i f g) (hT : IsFlatQuasicoherentTriple i f g T) :
    IsIso ((baseChangeTripleAdjunction i f g hi).counit.app T) := by
  have := hT.1.1
  have := hT.2.1
  have : ((tripleGluingFunctor i f g).obj T).IsQuasicoherent :=
    isQuasicoherent_tripleGluingFunctor_obj i f g hi T hT.1.1 hT.2.1
  have hqt := isQuasicoherent_baseChange_target i f g hi ((tripleGluingFunctor i f g).obj T)
  have hqa := isQuasicoherent_baseChange_ambient i f g hi ((tripleGluingFunctor i f g).obj T)
  refine isIso_gluingTripleHom i f g _ ?_ ?_
  · refine isIso_of_bijective_app_of_isOpenCover' hqt hT.1.1
      (GluingTripleHom.target ((baseChangeTripleAdjunction i f g hi).counit.app T))
      (fun q : chartIndex i f g => targetRestriction i f g ⁻¹ᵁ chartOpen i f g q)
      (isOpenCover_preimage_chartOpen i f g (targetRestriction i f g))
      (fun q => isAffineOpen_targetChart i f g hi q.2.1.2) fun q => ?_
    obtain ⟨I, base, s, eB, kD, kC', kC, hD', hkD1, -, hkC'1, -, hDC, hC'C⟩ :=
      exists_chartData i f g hi q.1.2 q.2.1.2 q.2.2
    exact (bijective_counit_app_of_chartData i f g hi T q.2.1.2 s kD kC' kC
      hkD1 hkC'1 hDC hC'C).1
  · refine isIso_of_bijective_app_of_isOpenCover' hqa hT.2.1
      (GluingTripleHom.ambient ((baseChangeTripleAdjunction i f g hi).counit.app T))
      (fun q : chartIndex i f g => ambientRestriction i f g ⁻¹ᵁ chartOpen i f g q)
      (isOpenCover_preimage_chartOpen i f g (ambientRestriction i f g))
      (fun q => isAffineOpen_ambientChart i f g hi q.2.1.2) fun q => ?_
    obtain ⟨I, base, s, eB, kD, kC', kC, hD', hkD1, -, hkC'1, -, hDC, hC'C⟩ :=
      exists_chartData i f g hi q.1.2 q.2.1.2 q.2.2
    exact (bijective_counit_app_of_chartData i f g hi T q.2.1.2 s kD kC' kC
      hkD1 hkC'1 hDC hC'C).2

/-! ### The equivalence -/

open Stacks.Thickenings in
/-- **The gluing functor between the two categories of Tag 08KU.**  The restriction of
`Stacks.Pushout.tripleGluingFunctor`, which lands in the quasi-coherent modules flat over `Y'`
by `Stacks.Pushout.flatQuasicoherent_tripleGluingFunctor_obj`. -/
noncomputable def flatTripleGluingFunctor (hi : IsThickening i) [IsAffineHom f] :
    FlatGluingTriple i f g ⥤ FlatQuasicoherentModule g :=
  (FlatQuasicoherent g).lift ((IsFlatQuasicoherentTriple i f g).ι ⋙ tripleGluingFunctor i f g)
    fun T => flatQuasicoherent_tripleGluingFunctor_obj i f g hi T.obj T.property

open Stacks.Thickenings in
/-- The restricted comparison functor is the comparison functor. -/
noncomputable def flatComm1 (hi : IsThickening i) [IsAffineHom f] :
    (FlatQuasicoherent g).ι ⋙ baseChangeTripleFunctor i f hi g ≅
      flatBaseChangeTripleFunctor i f g hi ⋙ (IsFlatQuasicoherentTriple i f g).ι :=
  Iso.refl _

open Stacks.Thickenings in
/-- The restricted gluing functor is the gluing functor. -/
noncomputable def flatComm2 (hi : IsThickening i) [IsAffineHom f] :
    (IsFlatQuasicoherentTriple i f g).ι ⋙ tripleGluingFunctor i f g ≅
      flatTripleGluingFunctor i f g hi ⋙ (FlatQuasicoherent g).ι :=
  Iso.refl _

open Stacks.Thickenings in
/-- **The adjunction of Tag 08KU between the two categories the tag names.** -/
noncomputable def flatBaseChangeTripleAdjunction (hi : IsThickening i) [IsAffineHom f] :
    flatBaseChangeTripleFunctor i f g hi ⊣ flatTripleGluingFunctor i f g hi :=
  (baseChangeTripleAdjunction i f g hi).restrictFullyFaithful
    (FlatQuasicoherent g).fullyFaithfulι (IsFlatQuasicoherentTriple i f g).fullyFaithfulι
    (flatComm1 i f g hi) (flatComm2 i f g hi)

open Stacks.Thickenings in
/-- The unit of the restricted adjunction, read through the inclusion of the subcategory. -/
theorem flatUnit_map (hi : IsThickening i) [IsAffineHom f] (X : FlatQuasicoherentModule g) :
    (FlatQuasicoherent g).ι.map ((flatBaseChangeTripleAdjunction i f g hi).unit.app X) =
      (baseChangeTripleAdjunction i f g hi).unit.app X.obj ≫
        (tripleGluingFunctor i f g).map ((flatComm1 i f g hi).hom.app X) ≫
        (flatComm2 i f g hi).hom.app ((flatBaseChangeTripleFunctor i f g hi).obj X) :=
  CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app _ _ _ _ _ X

open Stacks.Thickenings in
/-- The counit of the restricted adjunction, read through the inclusion of the subcategory. -/
theorem flatCounit_map (hi : IsThickening i) [IsAffineHom f] (T : FlatGluingTriple i f g) :
    (IsFlatQuasicoherentTriple i f g).ι.map
        ((flatBaseChangeTripleAdjunction i f g hi).counit.app T) =
      (flatComm1 i f g hi).inv.app ((flatTripleGluingFunctor i f g hi).obj T) ≫
        (baseChangeTripleFunctor i f hi g).map ((flatComm2 i f g hi).inv.app T) ≫
        (baseChangeTripleAdjunction i f g hi).counit.app T.obj :=
  CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app _ _ _ _ _ T

open Stacks.Thickenings in
/-- **The first clause of [Stacks Project, Tag 08KU], with the pushout assumed.**  The comparison
functor restricts to an equivalence between quasi-coherent `𝒪_{V'}`-modules flat over `Y'` and
the triples of a quasi-coherent module on `V` flat over `Y`, a quasi-coherent module on `U'` flat
over `X'` and an isomorphism of their restrictions to `U`.

`Stacks.Pushout.isEquivalence_flatBaseChangeTripleFunctor` is this statement with the pushout
produced from the thickening rather than assumed; that is the form registered for the tag. -/
theorem isEquivalence_flatBaseChangeTripleFunctor_of_hasPushout (hi : IsThickening i)
    [IsAffineHom f] : (flatBaseChangeTripleFunctor i f g hi).IsEquivalence := by
  have hunit : ∀ X : FlatQuasicoherentModule g,
      IsIso ((flatBaseChangeTripleAdjunction i f g hi).unit.app X) := by
    intro X
    have := X.property.1
    have : IsIso ((baseChangeTripleAdjunction i f g hi).unit.app X.obj) := by
      rw [baseChangeTripleAdjunction_unit_app]
      exact isIso_gluingUnitApp i f g hi X.obj X.property.2
    have : IsIso ((FlatQuasicoherent g).ι.map
        ((flatBaseChangeTripleAdjunction i f g hi).unit.app X)) := by
      rw [flatUnit_map]
      infer_instance
    exact isIso_of_reflects_iso _ (FlatQuasicoherent g).ι
  have hcounit : ∀ T : FlatGluingTriple i f g,
      IsIso ((flatBaseChangeTripleAdjunction i f g hi).counit.app T) := by
    intro T
    have : IsIso ((baseChangeTripleAdjunction i f g hi).counit.app T.obj) :=
      isIso_baseChangeTripleAdjunction_counit_app i f g hi T.obj T.property
    have : IsIso ((IsFlatQuasicoherentTriple i f g).ι.map
        ((flatBaseChangeTripleAdjunction i f g hi).counit.app T)) := by
      rw [flatCounit_map]
      infer_instance
    exact isIso_of_reflects_iso _ (IsFlatQuasicoherentTriple i f g).ι
  exact (flatBaseChangeTripleAdjunction i f g hi).toEquivalence.isEquivalence_functor

open Stacks.Thickenings in
omit [HasPushout i f] in
/-- **Stacks Project, Tag 08KU, the equivalence of the first clause.**  For a thickening
`i : X ⟶ X'`, an affine morphism `f : X ⟶ Y`, the pushout `Y' = Y ⨿_X X'` and any
`g : V' ⟶ Y'`, the comparison functor of the tag — a quasi-coherent `𝒪_{V'}`-module flat over
`Y'` goes to its restrictions to `V = Y ×_{Y'} V'` and to `U' = X' ×_{Y'} V'` together with the
canonical isomorphism of their restrictions to `U = X ×_{Y'} V'` — is an **equivalence of
categories** onto the triples `(𝒢, ℱ', φ)` with `𝒢` quasi-coherent on `V` and flat over `Y`,
`ℱ'` quasi-coherent on `U'` and flat over `X'`, and `φ` an isomorphism of their restrictions
to `U`.

The pushout `Y' = Y ⨿_X X'` is not assumed to exist: for a thickening `i` and an affine `f` it
does, by the first assertion of [Stacks Project, Tag 07RT],
`Stacks.Pushout.hasPushout_of_isThickening_of_isAffineHom`, whose [Stacks Project, Tag 06AD]
hypothesis is discharged by `Stacks.Thickenings.forall_isAffine_of_isThickening`; that is the
instance the statement binds for itself. -/
@[stacks 08KU "the equivalence of the first clause"]
theorem isEquivalence_flatBaseChangeTripleFunctor (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
    ∀ g : V' ⟶ pushout i f, (flatBaseChangeTripleFunctor i f g hi).IsEquivalence :=
  let := hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi
  fun g => isEquivalence_flatBaseChangeTripleFunctor_of_hasPushout i f g hi

end Stacks.Pushout

end
