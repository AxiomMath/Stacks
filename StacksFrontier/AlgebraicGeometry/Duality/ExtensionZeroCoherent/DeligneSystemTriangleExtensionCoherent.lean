module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangleExtension
import all StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangleExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.CoherentComplexRepresentative
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.BoundedCoherentTriangulated
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemRestrictionLifting
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Coherence

/-!
# Extending a distinguished triangle of `D^b_Coh(𝒪_U)` to a system of Deligne systems

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and let `K ⟶ L ⟶ M ⟶ K[1]` be a
distinguished triangle of `D^b_{Coh}(𝒪_U)`. [Stacks, Tag 0G4M] produces an inverse system of
distinguished triangles `K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]` of `D^b_{Coh}(𝒪_X)` whose three vertex
systems are Deligne systems and whose restriction to `U` is isomorphic to the triangle one
started with.

The proof has two halves, as in the source. The first produces a *coherent complex model over
`X`* for the morphism `K ⟶ L`, that is a morphism `α^• : 𝓕^• ⟶ 𝓖^•` of bounded complexes of
coherent `𝒪_X`-modules whose image in `D(𝒪_U)` under restriction is the given `K ⟶ L`
(`AlgebraicGeometry.DeligneTriangle.CoherentComplexModel`); the second builds the inverse system
of triangles from it.

## The coherent complex model

`K` and `L` are restrictions of bounded complexes `𝓕^•` and `𝓖^•` of coherent `𝒪_X`-modules,
`AlgebraicGeometry.exists_bounded_isCoherent_complex_restrict_Q_iso` (after [Stacks, Tag 0G48]).
The system `(𝓘^n𝓕^•)` is a Deligne system with value `K`
(`AlgebraicGeometry.DeligneSystem.restrictIsoConst`), so by
[Stacks, Tag 0G2H], in the form `AlgebraicGeometry.DeligneSystem.exists_comp_restrict_eq`, the
morphism `K ⟶ L` is the restriction of a morphism `𝓘^n𝓕^• ⟶ 𝓖^•` of `D(𝒪_X)` for some `n`. That
morphism is a roof `𝓘^n𝓕^• ← 𝓕'^• ⟶ 𝓖^•` of bounded complexes of coherent modules with a
quasi-isomorphism as left leg, `AlgebraicGeometry.exists_isCoherent_roof` (after
[Stacks, Tag 0FDB]), and its right leg is the model.

## The construction

Choose a quasi-coherent sheaf of ideals `𝓘` cutting out `X ∖ U` — the vanishing ideal of the
closed complement of the range of `j` serves. The Deligne system attached to a bounded complex
`𝓕^•` of coherent modules is the system `(𝓘^n𝓕^•)` of its termwise ideal-power subcomplexes; what
has to be checked is that each `𝓘^n𝓕^•` defines an object of `D^b_{Coh}(𝒪_X)`, which is
`AlgebraicGeometry.DeligneTriangle.mem_boundedCoherentDerived_Q_obj` applied to
`AlgebraicGeometry.DeligneTriangle.idealPowerComplex_bounds` and
`AlgebraicGeometry.DeligneTriangle.isCoherent_idealPowerComplex_X`.

The third system is the one the source's identity

`C(α_n)^• = 𝓘^n C(α^•)`

provides: ideal powers are computed termwise, so they are the image of a complex under the
*functor* `AlgebraicGeometry.DeligneTriangle.idealPowerFunctor`, and that functor is additive, so
Mathlib's comparison `CochainComplex.mappingCone.mapHomologicalComplexXIso` for an additive
functor applied to a mapping cone is exactly the displayed identity, in each degree. This is what
makes `𝓘^n C(α^•)` carry an `AlgebraicGeometry.IdealPowerComplexSystem` whose terms are the cones
`C(α_n)^•`, hence what makes the third system a Deligne system rather than merely an inverse
system of cones: the `AlgebraicGeometry.DeligneSystem` structure demands the ideal-power
presentation, and the cone has to be taken at the level of complexes for it to have one.

The inverse system of distinguished triangles is then the system of the cone triangles of the
`α_n`, which is `AlgebraicGeometry.DeligneTriangle.mappingConeTriangleFunctor`; each is
distinguished by `DerivedCategory.mappingCone_triangle_distinguished`. Its restriction to `U` is
the constant system at the cone triangle of `α^•`, because the inclusion `𝓘^n𝓕^• ⟶ 𝓕^•` becomes
an isomorphism on `U` (the ideal is the unit ideal away from its support,
`AlgebraicGeometry.DeligneTriangle.isIso_restrict_idealPowerComplex_inclusion`) and then the
third vertex follows by the five lemma. Finally the restricted triangle is identified with the
given one by `TR3` and the fact that a morphism of distinguished triangles which is invertible on
two vertices is invertible on the third,
`AlgebraicGeometry.DeligneTriangle.nonempty_triangle_iso_of_mor₁`.

These triangles are built in `D(𝒪_X)`; all their vertices lie in `D^b_{Coh}(𝒪_X)`, a full
triangulated subcategory, so the system lifts to an inverse system of distinguished triangles of
`D^b_{Coh}(𝒪_X)` (`AlgebraicGeometry.DeligneTriangle.exists_triangleFunctor_lift`), and the
identifications of its vertex systems and of its restriction to `U` are transported back along
the fully faithful inclusions.

## Main definitions

* `AlgebraicGeometry.DeligneTriangle.idealPowerFunctor`: `M ↦ 𝓘^nM`, as an additive functor.
* `AlgebraicGeometry.DeligneTriangle.deligneSystemOfComplex`: the Deligne system `(𝓘^n𝓕^•)` of a
  bounded complex of coherent modules.
* `AlgebraicGeometry.DeligneTriangle.conePowerSystem`: the ideal-power presentation of `C(α^•)`
  whose `n`-th complex is `C(α_n)^•`.
* `AlgebraicGeometry.DeligneTriangle.deligneSystemOfMappingCone`: the Deligne system of the cone.
* `AlgebraicGeometry.DeligneTriangle.CoherentComplexModel`: a coherent complex model over `X` of
  a morphism of `D^b_{Coh}(𝒪_U)`.
* `AlgebraicGeometry.DeligneSystem.value`: the value on `U` of a Deligne system, and
  `AlgebraicGeometry.DeligneSystem.restrictIsoConst`: the restricted system is the constant
  system at the value.

## Main results

* `AlgebraicGeometry.mem_boundedCoherentDerived_restrict`: restriction along an open immersion
  preserves `D^b_{Coh}`, whence the restriction functor
  `AlgebraicGeometry.restrictBoundedCoherentLift : D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_U)`.
* `AlgebraicGeometry.DeligneTriangle.nonempty_coherentComplexModel`: every morphism of
  `D^b_{Coh}(𝒪_U)` has a coherent complex model over `X`.
* `AlgebraicGeometry.DeligneTriangle.exists_deligneSystem_distTriang_derived`: the inverse system
  of triangles, read in `D(𝒪_X)`.
* `AlgebraicGeometry.DeligneTriangle.exists_triangleFunctor_lift`: a system of distinguished
  triangles with vertices in a triangulated subcategory comes from the subcategory.
* `AlgebraicGeometry.DeligneTriangle.exists_deligneSystem_distTriang_boundedCoherent`: **Stacks
  0G4M**, with the inverse system of distinguished triangles in `D^b_{Coh}(𝒪_X)`.

## Implementation notes

**The third vertex.** The triangle `K ⟶ L ⟶ M ⟶ K[1]` enters only through `TR3`: the third
vertex of the constructed system is the cone of the model, and no particular shape of `M` is
used.

**Which derived category.** There are two `HasDerivedCategory` instances available for
`X.Modules`: the global `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, whose morphisms
live in universe `u`, and `CategoryTheory.HasDerivedCategory.standard`, whose morphisms live in
universe `u + 1`. They are *different* categories, and `AlgebraicGeometry.boundedCoherentDerived`
denotes different things depending on which is ambient. This file is about the second one: it
installs `CategoryTheory.HasDerivedCategory.standard` as a local instance **at priority 10000**,
which beats the global instance's default priority, so that the choice does not depend on whether
the global one happens to be in scope through some import. That is the model of
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemHom`, where
`AlgebraicGeometry.DeligneSystem` and `AlgebraicGeometry.BoundedCoherentDerived` are declared,
and of
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.BoundedCoherentTriangulated`, whose
triangulatedness instance for `D^b_{Coh}(𝒪_X)` is what this file consumes; a mismatch would be a
type error at every use of `AlgebraicGeometry.DeligneSystem` below rather than a silent change of
statement, because the Deligne systems this file builds are built field by field.

## References

* [Stacks Project, Tag 0G4M](https://stacks.math.columbia.edu/tag/0G4M)
* [Stacks Project, Tag 0G4L](https://stacks.math.columbia.edu/tag/0G4L)
* [Stacks Project, Tag 0G48](https://stacks.math.columbia.edu/tag/0G48)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.AlgebraicGeometry.IdealPower

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.DeligneTriangle

variable {U X : Scheme.{u}}

/-! ### Ideal powers as an additive functor -/

/-! ### The ideal-power subcomplexes as the image of that functor -/

/-! ### `𝓘^n` of a bounded complex of coherent modules is an object of `D^b_Coh(𝒪_X)` -/

/-! ### The Deligne system of a bounded complex of coherent modules -/

/-! ### The inverse system of cone triangles -/

/-! ### The cone of a morphism of ideal-power subcomplexes -/

/-! ### The Deligne system of the cone -/

/-! ### Restriction to `U` -/

end AlgebraicGeometry.DeligneTriangle

namespace AlgebraicGeometry

variable {U X : Scheme.{u}}

/-! ### The value on `U` of a Deligne system -/

/-- **Restriction along an open immersion preserves `D^b_{Coh}`.** Restriction commutes with the
cohomology sheaves of the derived category, preserves vanishing, and carries coherent modules to
coherent modules. -/
public lemma mem_boundedCoherentDerived_restrict (j : U ⟶ X) [IsOpenImmersion j]
    [IsLocallyNoetherian X] (L : DerivedCategory X.Modules) (hL : boundedCoherentDerived X L) :
    boundedCoherentDerived U ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj L) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hL
  refine ⟨⟨⟨a, fun i hi => ?_⟩, ⟨b, fun i hi => ?_⟩⟩, fun i => ?_⟩
  · exact ((Scheme.Modules.restrictFunctor j).map_isZero (ha i hi)).of_iso
      (((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso i).app L)
  · exact ((Scheme.Modules.restrictFunctor j).map_isZero (hb i hi)).of_iso
      (((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso i).app L)
  · have : ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent := hc i
    exact (coherentInModules U).prop_of_iso
      (((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso i).app L).symm
      (Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion j _)

/-- **Restriction `D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_U)` along an open immersion `j : U ⟶ X`**: the
restriction `AlgebraicGeometry.restrictBoundedCoherent j`, which lands in `D^b_{Coh}(𝒪_U)` by
`AlgebraicGeometry.mem_boundedCoherentDerived_restrict`. -/
public abbrev restrictBoundedCoherentLift (j : U ⟶ X) [IsOpenImmersion j]
    [IsLocallyNoetherian X] : BoundedCoherentDerived X ⥤ BoundedCoherentDerived U :=
  (boundedCoherentDerived U).lift (restrictBoundedCoherent j) fun L =>
    mem_boundedCoherentDerived_restrict j L.obj L.property

namespace DeligneSystem

variable {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X] (D : DeligneSystem j)

/-- **The inclusions `𝓘^n𝓕^• ⟶ 𝓕^•` of a Deligne system become isomorphisms on `U`.** In each
degree the inclusion is that of the ideal-power multiple `𝓘^n𝓕^i ⊆ 𝓕^i`, and `𝓘` is the unit
ideal on `U`. -/
public lemma isIso_restrict_Q_map_inclusion (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.map
      (DerivedCategory.Q.map (D.powers.inclusion n))) := by
  set R := Scheme.Modules.restrictFunctor j
  set i := D.powers.inclusion n
  have hcomp : ∀ k, IsIso (((R.mapHomologicalComplex (ComplexShape.up ℤ)).map i).f k) := by
    intro k
    have hc : (D.complex.X k).IsCoherent := D.isCoherent_complex k
    have hq : (D.complex.X k).IsQuasicoherent := isQuasicoherent_of_isCoherent (D.complex.X k)
    have h₁ : IsIso (R.map
        (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple D.idealSheaf n
          (D.complex.X k)).ι) :=
      DeligneTriangle.isIso_restrict_idealPowerMultiple_ι j D.idealSheaf
        D.support_idealSheaf (D.complex.X k) n
    have h₂ : R.map (i.f k) = R.map (D.powers.termIso n k).hom ≫
        R.map (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple D.idealSheaf n
          (D.complex.X k)).ι :=
      ((R.map_comp _ _).symm.trans (congrArg R.map (D.powers.include_f n k))).symm
    show IsIso (R.map (i.f k))
    rw [h₂]
    exact IsIso.comp_isIso' (R.mapIso (D.powers.termIso n k)).isIso_hom h₁
  set q := (R.mapHomologicalComplex (ComplexShape.up ℤ)).map i
  have hqiso : IsIso q :=
    (HomologicalComplex.Hom.isoOfComponents (fun k => asIso (q.f k))
      (fun k l _ => q.comm k l)).isIso_hom
  have hf : R.mapDerivedCategory.map (DerivedCategory.Q.map i) =
      R.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map q ≫
        R.mapDerivedCategoryFactors.inv.app _ := by
    simpa using congrArg (fun p => p ≫ R.mapDerivedCategoryFactors.inv.app _)
      (R.mapDerivedCategoryFactors.hom.naturality i)
  rw [hf]
  infer_instance

/-- The inclusions `𝓘^n𝓕^• ⟶ 𝓕^•` of a Deligne system, as a morphism from its system of
complexes to the constant system at `𝓕^•`. -/
public def inclusionNatTrans :
    Functor.ofOpSequence D.powers.transition ⟶ (Functor.const ℕᵒᵖ).obj D.complex :=
  NatTrans.ofOpSequence (fun n => D.powers.inclusion n) (fun n => by
    rw [Functor.ofOpSequence_map_homOfLE_succ (fun m => D.powers.transition m) n]
    exact (D.powers.transition_include n).trans (Category.comp_id _).symm)

/-- **The value on `U` of a Deligne system**: the restriction `𝓕^•|_U` of its complex, an object
of `D^b_{Coh}(𝒪_U)`. -/
public def value : BoundedCoherentDerived U :=
  ⟨(Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj (DerivedCategory.Q.obj D.complex),
    mem_boundedCoherentDerived_restrict j _
      (DeligneTriangle.mem_boundedCoherentDerived_Q_obj D.complex D.exists_isStrictlyGE
        D.exists_isStrictlyLE D.isCoherent_complex)⟩

/-- **The restriction of a Deligne system to `U` is the constant system at its value.** The
identification is induced by the inclusions `𝓘^n𝓕^• ⟶ 𝓕^•`, which restrict to isomorphisms by
`AlgebraicGeometry.DeligneSystem.isIso_restrict_Q_map_inclusion`. -/
public def restrictIsoConst :
    D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj D.value) :=
  have : IsIso (Functor.whiskerRight D.inclusionNatTrans
      (DerivedCategory.Q ⋙ (Scheme.Modules.restrictFunctor j).mapDerivedCategory)) := by
    have : ∀ n : ℕᵒᵖ, IsIso ((Functor.whiskerRight D.inclusionNatTrans
        (DerivedCategory.Q ⋙ (Scheme.Modules.restrictFunctor j).mapDerivedCategory)).app n) :=
      fun n => D.isIso_restrict_Q_map_inclusion n.unop
    exact NatIso.isIso_of_isIso_app _
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight D.representation
      ((Scheme.Modules.restrictFunctor j).mapDerivedCategory) ≪≫
    Functor.associator _ _ _ ≪≫
    asIso (Functor.whiskerRight D.inclusionNatTrans
      (DerivedCategory.Q ⋙ (Scheme.Modules.restrictFunctor j).mapDerivedCategory)) ≪≫
    Functor.constComp _ _ _

end DeligneSystem

end AlgebraicGeometry

namespace AlgebraicGeometry.DeligneTriangle

variable {U X : Scheme.{u}}

/-! ### The input of the construction -/

/-- **Every morphism of `D^b_{Coh}(𝒪_U)` has a coherent complex model over `X`**, for an open
immersion `j : U ⟶ X` into a Noetherian scheme. This is the first two paragraphs of the proof of
[Stacks, Tag 0G4M]. Both `K` and `L` are restrictions of bounded complexes `𝓕^•`, `𝓖^•` of
coherent `𝒪_X`-modules (`AlgebraicGeometry.exists_bounded_isCoherent_complex_restrict_Q_iso`, after
[Stacks, Tag 0G48]); the morphism `K ⟶ L` is the restriction of a morphism `𝓘^n𝓕^• ⟶ 𝓖^•` from a
stage of the Deligne system of `𝓕^•` ([Stacks, Tag 0G2H], in the form
`AlgebraicGeometry.DeligneSystem.exists_comp_restrict_eq`); and that morphism is a roof
`𝓘^n𝓕^• ← 𝓕'^• ⟶ 𝓖^•` of bounded complexes of coherent modules whose left leg is a
quasi-isomorphism (`AlgebraicGeometry.exists_isCoherent_roof`, after [Stacks, Tag 0FDB]). The model
is the right leg. -/
public lemma nonempty_coherentComplexModel (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X]
    {K L : BoundedCoherentDerived U} (α : K ⟶ L) : Nonempty (CoherentComplexModel j α) := by
  classical
  set R := (Scheme.Modules.restrictFunctor j).mapDerivedCategory
  obtain ⟨F, hFcoh, hFge, hFle, ⟨σ⟩⟩ := exists_bounded_isCoherent_complex_restrict_Q_iso j K
  obtain ⟨G, hGcoh, hGge, hGle, ⟨τ⟩⟩ := exists_bounded_isCoherent_complex_restrict_Q_iso j L
  set Z : TopologicalSpace.Closeds X := j.opensRange.compl
  set I := Scheme.IdealSheafData.vanishingIdeal Z
  have hI : (I.support : Set X) = (Set.range j.base)ᶜ :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  set D := deligneSystemOfComplex j I hI F hFge hFle hFcoh
  set e := D.restrictIsoConst ≪≫ (Functor.const ℕᵒᵖ).mapIso σ
  let L' : BoundedCoherentDerived X :=
    ⟨DerivedCategory.Q.obj G, mem_boundedCoherentDerived_Q_obj G hGge hGle hGcoh⟩
  -- `K ⟶ L` is the restriction of some `𝓘^n𝓕^• ⟶ 𝓖^•`, by Stacks 0G2H
  obtain ⟨n, g, hg⟩ := D.exists_comp_restrict_eq K e L'
    ((boundedCoherentDerived U).ι.map α ≫ τ.inv)
  -- and that morphism is a roof of bounded complexes of coherent modules, by Stacks 0FDB
  obtain ⟨aF, haF⟩ := hFge
  obtain ⟨bF, hbF⟩ := hFle
  obtain ⟨aG, haG⟩ := hGge
  obtain ⟨bG, hbG⟩ := hGle
  obtain ⟨hPge, hPle⟩ := idealPowerComplex_bounds I F aF bF haF hbF n.unop
  obtain ⟨F₀, hF'coh, hF'ge, hF'le, s₀, hs₀, g₀, hfac₀⟩ :=
    @exists_isCoherent_roof X _ _ G (isCoherent_idealPowerComplex_X I F hFcoh n.unop) hGcoh
      (min aF aG) (max bF bG)
      (((idealPowerComplexSystem I F).complex n.unop).isStrictlyGE_of_ge _ aF (min_le_left _ _))
      (((idealPowerComplexSystem I F).complex n.unop).isStrictlyLE_of_le bF _ (le_max_left _ _))
      (G.isStrictlyGE_of_ge _ aG (min_le_right _ _)) (G.isStrictlyLE_of_le bG _ (le_max_right _ _))
      g.hom
  let F' : CochainComplex X.Modules ℤ := F₀
  let s : F' ⟶ (idealPowerComplexSystem I F).complex n.unop := s₀
  let g' : F' ⟶ G := g₀
  have hs : IsIso (DerivedCategory.Q.map s) := hs₀
  have hfac : g.hom = inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g' := hfac₀
  have hQ : DerivedCategory.Q.map s ≫ g.hom = DerivedCategory.Q.map g' := by
    rw [hfac, IsIso.hom_inv_id_assoc]
  have hg' : e.hom.app n ≫ (boundedCoherentDerived U).ι.map α = R.map g.hom ≫ τ.hom := by
    have h₂ := congrArg (· ≫ τ.hom) hg
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h₂
    rw [← h₂, Iso.hom_inv_id_app_assoc]
    rfl
  exact ⟨{ source := F', target := G, map := g'
           exists_isStrictlyGE_source := ⟨_, hF'ge⟩, exists_isStrictlyLE_source := ⟨_, hF'le⟩
           exists_isStrictlyGE_target := ⟨_, haG⟩, exists_isStrictlyLE_target := ⟨_, hbG⟩
           isCoherent_source := hF'coh, isCoherent_target := hGcoh
           sourceIso := asIso (R.map (DerivedCategory.Q.map s)) ≪≫ e.app n, targetIso := τ
           restrict_map := (congrArg (fun q => R.map q ≫ τ.hom) hQ).symm.trans
             ((congrArg (· ≫ τ.hom) (R.map_comp _ _)).trans ((Category.assoc _ _ _).trans
               ((congrArg (R.map (DerivedCategory.Q.map s) ≫ ·) hg'.symm).trans
                 (Category.assoc _ _ _).symm))) }⟩

/-! ### Lifting systems of triangles to a triangulated subcategory -/

/-- **A distinguished triangle whose first two vertices are isomorphic to objects of a
triangulated subcategory comes from the subcategory**: complete the corresponding morphism of the
subcategory to a distinguished triangle there, and compare by `TR3`. -/
public lemma mem_essImage_ι_mapTriangle {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) [P.IsTriangulated] (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : P.isoClosure T.obj₁) (h₂ : P.isoClosure T.obj₂) : P.ι.mapTriangle.essImage T := by
  obtain ⟨Y₁, hY₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨Y₂, hY₂, ⟨e₂⟩⟩ := h₂
  obtain ⟨Z, g, h, H⟩ := distinguished_cocone_triangle
    (ObjectProperty.homMk (e₁.inv ≫ T.mor₁ ≫ e₂.hom) :
      (⟨Y₁, hY₁⟩ : P.FullSubcategory) ⟶ ⟨Y₂, hY₂⟩)
  exact ⟨_, ⟨isoTriangleOfIso₁₂ _ _ (P.ι.map_distinguished _ H) hT e₁.symm e₂.symm
    (by
      show (e₁.inv ≫ T.mor₁ ≫ e₂.hom) ≫ e₂.inv = e₁.inv ≫ T.mor₁
      simp)⟩⟩

/-- **A system of distinguished triangles whose first two vertices lie in a triangulated
subcategory is the image of a system of triangles of the subcategory.** The inclusion is fully
faithful on triangles, and each triangle of the system is in its essential image by
`AlgebraicGeometry.DeligneTriangle.mem_essImage_ι_mapTriangle`. -/
public lemma exists_triangleFunctor_lift {C J : Type*} [Category C] [Category J]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (P : ObjectProperty C) [P.IsTriangulated] (G : J ⥤ Triangle C)
    (hG : ∀ i, G.obj i ∈ distTriang C) (h₁ : ∀ i, P.isoClosure (G.obj i).obj₁)
    (h₂ : ∀ i, P.isoClosure (G.obj i).obj₂) :
    ∃ G' : J ⥤ Triangle P.FullSubcategory, Nonempty (G' ⋙ P.ι.mapTriangle ≅ G) := by
  have : P.ι.mapTriangle.toEssImage.IsEquivalence := {}
  let e := P.ι.mapTriangle.toEssImage.asEquivalence
  exact ⟨P.ι.mapTriangle.essImage.lift G
    (fun i => mem_essImage_ι_mapTriangle P _ (hG i) (h₁ i) (h₂ i)) ⋙ e.inverse,
    ⟨Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ P.ι.mapTriangle.toEssImageCompι.symm ≪≫
        e.invFunIdAssoc _) ≪≫
      P.ι.mapTriangle.essImage.liftCompιIso _ _⟩⟩

/-! ### Stacks 0G4M -/

/-- **[Stacks, Tag 0G4M], with the triangles read in `D(𝒪_X)`.** The inverse system of
distinguished triangles is the system of cone triangles of a coherent complex model of `K ⟶ L`,
recorded in `D(𝒪_X)`, with its vertex systems identified with three Deligne systems and its
restriction to `U` with the constant system at the given triangle.

A *coherent complex model over `X`* for `K ⟶ L`, a morphism `α^• : 𝓕^• ⟶ 𝓖^•` of bounded
complexes of coherent `𝒪_X`-modules restricting to it on `U`, is produced by
`AlgebraicGeometry.DeligneTriangle.nonempty_coherentComplexModel` from [Stacks, Tag 0G48],
[Stacks, Tag 0G2H] and [Stacks, Tag 0FDB]. The quasi-coherent ideal sheaf cutting out `X ∖ U`
is the vanishing ideal of the closed complement of the range of `j`; the two outer Deligne
systems are the ideal-power systems of `𝓕^•` and `𝓖^•`; the third is the ideal-power system of
the mapping cone `C(α^•)`, which is legitimate exactly because `C(α_n)^• = 𝓘^nC(α^•)`; the
inverse system of distinguished triangles is the system of cone triangles of the `α_n`; and the
restricted system is constant at the cone triangle of `α^•`, which is identified with the given
triangle by `TR3`. -/
public theorem exists_deligneSystem_distTriang_derived (j : U ⟶ X) [IsOpenImmersion j]
    [IsNoetherian X]
    (T : Triangle (BoundedCoherentDerived U)) (hT : T ∈ distTriang (BoundedCoherentDerived U)) :
    ∃ (DK DL DM : DeligneSystem j) (TX : ℕᵒᵖ ⥤ Triangle (DerivedCategory X.Modules)),
      (∀ n : ℕᵒᵖ, TX.obj n ∈ distTriang (DerivedCategory X.Modules)) ∧
      Nonempty (DK.system ⋙ (boundedCoherentDerived X).ι ≅ TX ⋙ Triangle.π₁) ∧
      Nonempty (DL.system ⋙ (boundedCoherentDerived X).ι ≅ TX ⋙ Triangle.π₂) ∧
      Nonempty (DM.system ⋙ (boundedCoherentDerived X).ι ≅ TX ⋙ Triangle.π₃) ∧
      Nonempty (TX ⋙ (Scheme.Modules.restrictFunctor j).mapDerivedCategory.mapTriangle ≅
        (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.mapTriangle.obj T)) := by
  classical
  obtain ⟨model⟩ := nonempty_coherentComplexModel j T.mor₁
  set F := model.source
  set G := model.target
  set g := model.map
  set Z : TopologicalSpace.Closeds X := j.opensRange.compl
  set I := Scheme.IdealSheafData.vanishingIdeal Z
  have hI : (I.support : Set X) = (Set.range j.base)ᶜ :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  set DF := deligneSystemOfComplex j I hI F model.exists_isStrictlyGE_source
    model.exists_isStrictlyLE_source model.isCoherent_source
  set DG := deligneSystemOfComplex j I hI G model.exists_isStrictlyGE_target
    model.exists_isStrictlyLE_target model.isCoherent_target
  set DC := deligneSystemOfMappingCone j I hI g model.exists_isStrictlyGE_source
    model.exists_isStrictlyLE_source model.exists_isStrictlyGE_target
    model.exists_isStrictlyLE_target model.isCoherent_source model.isCoherent_target
  set TX := idealPowerConeTriangleFunctor I g ⋙ DerivedCategory.Q.mapTriangle
  refine ⟨DF, DG, DC, TX,
    mappingConeTriangleFunctor_distinguished _ _ (idealPowerComplexMapNatTrans I g),
    ⟨DF.representation ≪≫ mappingConeTriangleFunctor_π₁Iso _ _ _⟩,
    ⟨DG.representation ≪≫ mappingConeTriangleFunctor_π₂Iso _ _ _⟩,
    ⟨DC.representation ≪≫
      Functor.isoWhiskerRight (idealPowerConeTriangle_π₃Iso I g) DerivedCategory.Q⟩, ?_⟩
  set R := (Scheme.Modules.restrictFunctor j).mapDerivedCategory
  set S := R.mapTriangle.obj
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle g))
  set TU := (boundedCoherentDerived U).ι.mapTriangle.obj T
  have hfirst : S.mor₁ ≫ model.targetIso.hom = model.sourceIso.hom ≫ TU.mor₁ :=
    model.restrict_map
  obtain ⟨eST⟩ := nonempty_triangle_iso_of_mor₁ S TU
    (R.map_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished g))
    ((boundedCoherentDerived U).ι.map_distinguished T hT) model.sourceIso model.targetIso hfirst
  obtain ⟨eRes⟩ := nonempty_conePowerRestrictIsoConst j I hI g
    model.isCoherent_source model.isCoherent_target
  exact ⟨eRes ≪≫ (Functor.const ℕᵒᵖ).mapIso eST⟩

/-- **Stacks Project, Tag 0G4M.** Let `j : U ⟶ X` be an open immersion of Noetherian schemes and
let

`K ⟶ L ⟶ M ⟶ K[1]`

be a distinguished triangle of `D^b_{Coh}(𝒪_U)`. Then there is an inverse system of
distinguished triangles

`K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]`

in `D^b_{Coh}(𝒪_X)` such that `(K_n)`, `(L_n)` and `(M_n)` are Deligne systems and such that the
restriction of these distinguished triangles to `U` is isomorphic to the distinguished triangle
one started with.

The system is the one of
`AlgebraicGeometry.DeligneTriangle.exists_deligneSystem_distTriang_derived`, the cone triangles
of a coherent complex model of `K ⟶ L`, lifted to `D^b_{Coh}(𝒪_X)` by
`AlgebraicGeometry.DeligneTriangle.exists_triangleFunctor_lift`; the identifications of its
vertex systems and of its restriction to `U` are transported back along the fully faithful
inclusions of `D^b_{Coh}`. -/
@[stacks 0G4M]
public theorem exists_deligneSystem_distTriang_boundedCoherent (j : U ⟶ X) [IsOpenImmersion j]
    [IsNoetherian X]
    (T : Triangle (BoundedCoherentDerived U)) (hT : T ∈ distTriang (BoundedCoherentDerived U)) :
    ∃ (DK DL DM : DeligneSystem j) (TX : ℕᵒᵖ ⥤ Triangle (BoundedCoherentDerived X)),
      (∀ n : ℕᵒᵖ, TX.obj n ∈ distTriang (BoundedCoherentDerived X)) ∧
      Nonempty (TX ⋙ Triangle.π₁ ≅ DK.system) ∧
      Nonempty (TX ⋙ Triangle.π₂ ≅ DL.system) ∧
      Nonempty (TX ⋙ Triangle.π₃ ≅ DM.system) ∧
      Nonempty (TX ⋙ (restrictBoundedCoherentLift j).mapTriangle ≅
        (Functor.const ℕᵒᵖ).obj T) := by
  obtain ⟨DK, DL, DM, T₀, hT₀, ⟨eK⟩, ⟨eL⟩, ⟨eM⟩, ⟨eR⟩⟩ :=
    exists_deligneSystem_distTriang_derived j T hT
  set ιX := (boundedCoherentDerived X).ι
  set ιU := (boundedCoherentDerived U).ι
  obtain ⟨TX, ⟨eT⟩⟩ := exists_triangleFunctor_lift (boundedCoherentDerived X) T₀ hT₀
    (fun n => ⟨_, (DK.system.obj n).property, ⟨(eK.app n).symm⟩⟩)
    (fun n => ⟨_, (DL.system.obj n).property, ⟨(eL.app n).symm⟩⟩)
  have hX := (boundedCoherentDerived X).fullyFaithfulι.whiskeringRight ℕᵒᵖ
  have hU := (Functor.FullyFaithful.ofFullyFaithful ιU.mapTriangle).whiskeringRight ℕᵒᵖ
  have v : ∀ (π : Triangle (BoundedCoherentDerived X) ⥤ BoundedCoherentDerived X)
      (π' : Triangle (DerivedCategory X.Modules) ⥤ DerivedCategory X.Modules)
      (S : ℕᵒᵖ ⥤ BoundedCoherentDerived X), (π ⋙ ιX ≅ ιX.mapTriangle ⋙ π') →
      (S ⋙ ιX ≅ T₀ ⋙ π') → Nonempty (TX ⋙ π ≅ S) := fun π π' S w e =>
    ⟨hX.preimageIso (Functor.isoWhiskerLeft TX w ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eT π' ≪≫ e.symm)⟩
  refine ⟨DK, DL, DM, TX, fun n => isomorphic_distinguished _ (hT₀ n) _ (eT.app n),
    v _ _ _ (Iso.refl _) eK, v _ _ _ (Iso.refl _) eL, v _ _ _ (Iso.refl _) eM,
    ⟨hU.preimageIso ?_⟩⟩
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft TX ((Functor.mapTriangleCompIso _ _).symm ≪≫
      Functor.mapTriangleIso ((boundedCoherentDerived U).liftCompιIso _ _) ≪≫
      Functor.mapTriangleCompIso ιX (Scheme.Modules.restrictFunctor j).mapDerivedCategory) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eT _ ≪≫ eR ≪≫
    (Functor.constComp _ _ _).symm

end AlgebraicGeometry.DeligneTriangle

end
