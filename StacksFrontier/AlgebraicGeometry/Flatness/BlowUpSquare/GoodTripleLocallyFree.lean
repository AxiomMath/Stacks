module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafRestrictOpen
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatIdealTorsionFree
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernSetup
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedUnconditional
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaGeneratorSection
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPrincipalityTransfer
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleBlowup
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FreeOnAffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.Homology.Eta.Perfect.LocallyFreeModule
public import StacksFrontier.Homology.Eta.Perfect.SectionsBasisPresentation
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeReflect

/-!
# Blowing up complexes, II: the décalage of a complex of vector bundles

Let `X` be a scheme, `D ⊆ X` an effective Cartier divisor with ideal sheaf `ℐ`, and `M` a
perfect object of `D(𝒪_X)`, and assume the triple `(X, D, M)` is good: every point of `D` lies
in an affine chart `(U, A, f, M^•)` all of whose determinantal ideals `I_i(M^•, f)` are
principal.  If `M` is represented by a locally bounded complex `ℳ^•` of finite locally free
`𝒪_X`-modules, then `Lη_ℐ M` is represented by one as well, namely by `η_ℐ ℳ^•`.

The terms of `ℳ^•` are flat, hence `ℐ`-torsion free, so `η_ℐ ℳ^•` is defined and represents
`Lη_ℐ M`.  Local boundedness of the décalage is inherited from that of `ℳ^•`.  Finite local
freeness of its terms is checked on affine opens: over an affine open `U` small enough for the
modules of sections `Γ(U, ℳ^i)` to be finite free, those sections form a bounded complex `N^•`
of finite free `Γ(X, U)`-modules which represents `M|_U`, the sections of `η_ℐ ℳ^•` over `U` are
`η_f N^•` for the equation `f` of `D ∩ U`, and the determinantal ideals `I_i(N^•, f)` are
principal — on a basic open of a good chart by the transfer of principality across an
isomorphism in `D(Γ(X, U))`, and away from `D` because there `f` is a unit.  The terms of
`η_f N^•` are then finite locally free modules.

## Main definitions

* `Stacks.BlowUpComplexes.etaComplex`: the chain-level décalage `η_ℐ ℳ^•` of a complex of
  `ℐ`-torsion-free `𝒪_X`-modules, read at the scheme-level spelling of the category of
  `𝒪_X`-modules.
* `Stacks.BlowUpComplexes.sectionsTildeComplexIso` and
  `Stacks.BlowUpComplexes.affineTildeModelComplexIso`: a complex of quasi-coherent
  `𝒪_X`-modules, restricted to an affine open `U`, is the complex of `𝒪_U`-modules associated
  with its complex of sections over `U`.

## Main results

* `Stacks.BlowUpComplexes.nonempty_tildeModel_of_represents`: over an affine open, the complex
  of sections of a representative of `M` is a model for `M|_U` in the derived category of
  `Γ(X, U)`-modules.
* `Stacks.BlowUpComplexes.isFiniteLocallyFree_of_module_affineOpens`: a quasi-coherent module
  whose sections over the members of an affine cover are finite locally free modules is a
  finite locally free module.
* `Stacks.BlowUpComplexes.isIdealTorsionFree_of_isFiniteLocallyFree`: a finite locally free
  `𝒪_X`-module has no `ℐ`-torsion.
* `Stacks.BlowUpComplexes.isFiniteLocallyFree_etaComplex` and
  `Stacks.BlowUpComplexes.isLocallyBounded_etaComplex`: the terms of `η_ℐ ℳ^•` are finite
  locally free `𝒪_X`-modules, and the complex is locally bounded.
* `Stacks.BlowUpComplexes.exists_isLocallyBoundedFiniteLocallyFree_derivedEta`: the statement of
  the tag — `Lη_ℐ M` is represented by a locally bounded complex of finite locally free
  `𝒪_X`-modules.

## Implementation notes

The source states the conclusion for `𝒪_{X'}`-modules, but the complex its proof produces is
`η_ℐ ℳ^•`, a complex of `𝒪_X`-modules; no blowup of `X` occurs in the argument, and `X'` is the
scheme of the next lemma of the section.  The conclusion here is therefore about `𝒪_X`-modules.

Three spellings of the category of `𝒪_X`-modules meet here and are definitionally equal:
`AlgebraicGeometry.Scheme.Modules`, at which the sections functor, the tilde comparison and the
derived décalage of an effective Cartier divisor are written; `StrictlyPerfect.OXMod` of the
underlying ringed space, at which a triple records its perfect object; and
`SheafOfModules (structureSheaf _)`, at which the chain-level décalage is written.  Instance
search does not identify them, which is why `etaComplex` is given a name: ascribing the
scheme-level type to the décalage is what makes the module structure on its modules of sections
available.

The decisive input is `affineTildeModelComplexIso`, the comparison of a complex of
quasi-coherent modules with the tilde of its complex of sections over an affine open.  The
object-level comparison `Stacks.Modules.tildeIsoRestrictFromSpec` carries no naturality, so the
comparison is assembled instead from `Stacks.AffineTilde.tildeGammaComplexIso`, the counit of
the tilde–`Γ` adjunction read on complexes over a spectrum, transported along
`AlgebraicGeometry.IsAffineOpen.restrictFromSpecGlobalSectionsIso`.  This is what supplies the
hypothesis of `AffineChart.isPrincipal_idealI_of_eq_basicOpen`, which asks the complex whose
determinantal ideals are to be shown principal to represent `M` over the basic open.

A point off the divisor needs no chart: there the ideal of `D` is the unit ideal, so the
equation of `D` can be taken to be `1`, and `I_i(N^•, 1)` contains `1`.  The good-triple
condition, which quantifies only over the points of `D`, is used nowhere else.

The equation of `D` on the basic open is the restriction of the equation of the chart, not an
arbitrary generator: the two differ by a unit, but their determinantal ideals are identified
only through the comparison of the ideal sheaf with its restriction, which
`AffineChart.isPrincipal_idealI_of_eq_basicOpen` avoids by requiring the equations to agree.

## References

* [Stacks Project, Tag 0GTX](https://stacks.math.columbia.edu/tag/0GTX)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8M](https://stacks.math.columbia.edu/tag/0F8M)
* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 0F7W](https://stacks.math.columbia.edu/tag/0F7W)
* [Stacks Project, Tag 0GSS](https://stacks.math.columbia.edu/tag/0GSS)
* [Stacks Project, Tag 0GT5](https://stacks.math.columbia.edu/tag/0GT5)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open StrictlyPerfect
open AlgebraicGeometry.Scheme.Modules (restrictFunctor restrictFunctorComp restrictFunctorCongr)
open Stacks.IdealTorsion.Eta (etaObj sectionsComplex generatorSection)
open Stacks.Divisors.Eta (idealSheaf idealSheafι)

universe u d

namespace Stacks.BlowUpComplexes

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 100000]
  AlgebraicGeometry.ComplexAndDivisorSituation.modulesHasDerivedCategory

variable {X : Scheme.{u}}

/-! ### Equations of the divisor on a basic open -/

/-- The image of a nonzerodivisor in the ring of sections over a basic open of an affine open is
again a nonzerodivisor: the restriction map is a localization. -/
theorem mem_nonZeroDivisors_map_basicOpen {U : X.Opens} (hU : IsAffineOpen U) (g : Γ(X, U))
    {f : Γ(X, U)} (hf : f ∈ nonZeroDivisors Γ(X, U)) :
    (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom f ∈
      nonZeroDivisors Γ(X, X.basicOpen g) := by
  have inst := hU.isLocalization_basicOpen g
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers g) _ hf

/-- The ideal of an ideal sheaf on a basic open of an affine open is generated by the restriction
of a generator on that affine open. -/
theorem ideal_basicOpen_eq_span_map (D : X.IdealSheafData) {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) {f : Γ(X, U)} (hf : D.ideal ⟨U, hU⟩ = Ideal.span {f}) :
    D.ideal ⟨X.basicOpen g, hU.basicOpen g⟩ =
      Ideal.span {(X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom f} := by
  have h := D.map_ideal_basicOpen ⟨U, hU⟩ g
  rw [hf, Ideal.map_span, Set.image_singleton] at h
  exact h.symm

/-- Off the support of an ideal sheaf every point has an affine open neighbourhood inside a given
open on which the ideal is the unit ideal. -/
theorem exists_affineOpen_ideal_eq_top (D : X.IdealSheafData) {x : X}
    (hx : x ∉ D.supportSet) (W : X.Opens) (hxW : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W ∧ D.ideal V = ⊤ := by
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hxW
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨U, hU⟩) hxU,
    Scheme.mem_zeroLocus_iff] at hx
  push Not at hx
  obtain ⟨s, hs, hxs⟩ := hx
  refine ⟨⟨X.basicOpen s, hU.basicOpen s⟩, hxs, (X.basicOpen_le s).trans hUW, ?_⟩
  have hmap := D.map_ideal (U := ⟨X.basicOpen s, hU.basicOpen s⟩) (V := ⟨U, hU⟩)
    (X.basicOpen_le s)
  refine Ideal.eq_top_of_isUnit_mem _ ?_ (X.toRingedSpace.isUnit_res_basicOpen s)
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ hs

/-! ### Transfer of finite local freeness -/

/-- Finite local freeness of a module transports along a linear equivalence. -/
private theorem isFiniteLocallyFree_of_linearEquiv {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (h : Module.IsFiniteLocallyFree R M) : Module.IsFiniteLocallyFree R N :=
  have h' := (Module.isFiniteLocallyFree_iff_finite_projective R M).mp h
  have := h'.1
  have := h'.2
  (Module.isFiniteLocallyFree_iff_finite_projective R N).mpr
    ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

/-- A zero object of a category of modules has only one element. -/
private theorem subsingleton_of_isZero {R : Type u} [Ring R] {N : ModuleCat.{u} R}
    (h : IsZero N) : Subsingleton N := by
  have hz := (IsZero.iff_id_eq_zero N).mp h
  have hall : ∀ c : N, c = 0 := fun c => by
    have hc := congrArg (fun (φ : N ⟶ N) => φ.hom c) hz
    simpa using hc
  exact ⟨fun a b => by rw [hall a, hall b]⟩

/-- A sheaf of modules vanishing on an open has no nonzero section over that open. -/
theorem subsingleton_sections_of_isZero (F : X.Modules) (U : X.Opens)
    (h : IsZero ((restrictModules X.toRingedSpace U).obj F)) : Subsingleton Γ(F, U) := by
  have h' : IsZero (Scheme.Modules.restrict F U.ι) :=
    IsZero.of_iso h
      ((AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor X U).app F).symm
  have h2 : Subsingleton Γ(Scheme.Modules.restrict F U.ι, (⊤ : U.toScheme.Opens)) :=
    subsingleton_of_isZero
      (Functor.map_isZero (_root_.AlgebraicGeometry.sectionsOn U.toScheme ⊤) h')
  exact U.ι_image_top ▸ h2

/-- **The sections of a quasi-coherent module over an affine open inside a trivialising open are
free.**  A trivialisation over `W` restricts to one over `Spec Γ(X, U)`, where Tag 05JM reads it
as freeness of the module of sections. -/
theorem module_free_sections_of_restrict_iso_free (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {W : X.Opens} (hUW : U ≤ W) (I : Type u)
    (e : (restrictFunctor W.ι).obj F ≅ SheafOfModules.free.{u} I) :
    Module.Free Γ(X, U) Γ(F, U) := by
  have hr : Set.range hU.fromSpec.base ⊆ Set.range W.ι.base := by
    rw [← Scheme.Hom.coe_opensRange, hU.opensRange_fromSpec, Scheme.Opens.range_ι]
    exact hUW
  obtain ⟨e'⟩ := Stacks.Modules.nonempty_restrictIsoFree_of_range_subset W.ι hU.fromSpec F I hr e
  exact (tilde_free_iff_module_free Γ(X, U) Γ(F, U)).mp
    ⟨I, ⟨Stacks.Modules.tildeIsoRestrictFromSpec F hU ≪≫ e'⟩⟩

/-- **The sections of a finite locally free module over an affine open form a finite locally free
module.**  This is Tag 05JM, transported along `Stacks.Modules.tildeIsoRestrictFromSpec`. -/
theorem module_isFiniteLocallyFree_sections (F : X.Modules) [F.IsQuasicoherent]
    (hF : Scheme.Modules.IsFiniteLocallyFree F) {U : X.Opens} (hU : IsAffineOpen U) :
    Module.IsFiniteLocallyFree Γ(X, U) Γ(F, U) :=
  (Stacks.Modules.tilde_isFiniteLocallyFree_iff_module Γ(X, U) Γ(F, U)).mp
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
      (Stacks.Modules.tildeIsoRestrictFromSpec F hU).symm
      (h := (Scheme.Modules.isFiniteLocallyFree_iff _).mp (hF.restrict hU.fromSpec)))

/-- **Finite local freeness is affine-local on sections.**  A quasi-coherent module each of whose
points lies in an affine open over which its sections form a finite locally free module is a
finite locally free module. -/
theorem isFiniteLocallyFree_of_module_affineOpens (F : X.Modules) [F.IsQuasicoherent]
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Module.IsFiniteLocallyFree Γ(X, U.1) Γ(F, U.1)) :
    Scheme.Modules.IsFiniteLocallyFree F := by
  choose U hU hmod using h
  have hUa : ∀ x : X, IsAffineOpen (U x).1 := fun x => (U x).2
  have hcov : ∀ x : X, ∃ (y : X) (z : Spec Γ(X, (U y).1)), (hUa y).fromSpec.base z = x := by
    intro x
    obtain ⟨z, hz⟩ : x ∈ Set.range (hUa x).fromSpec.base := by
      rw [← Scheme.Hom.coe_opensRange, (hUa x).opensRange_fromSpec]
      exact hU x
    exact ⟨x, z, hz⟩
  refine Stacks.Modules.isFiniteLocallyFree_of_openCover F
    (Scheme.Cover.mkOfCovers X (fun x => Spec Γ(X, (U x).1)) (fun x => (hUa x).fromSpec)
      hcov fun x => inferInstance) fun x => ?_
  refine (Scheme.Modules.isFiniteLocallyFree_iff _).mpr ?_
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
    (Stacks.Modules.tildeIsoRestrictFromSpec F (hUa x))
    (h := (Stacks.Modules.tilde_isFiniteLocallyFree_iff_module Γ(X, (U x).1) Γ(F, (U x).1)).mpr
      (hmod x))

/-! ### A complex of quasi-coherent modules on an affine open -/

/-- **A complex of quasi-coherent `𝒪_X`-modules is the complex associated with its sections over
an affine open.**  The comparison is the counit of the tilde–`Γ` adjunction on `Spec Γ(X, U)`,
whose global sections there are the sections over `U`. -/
def sectionsTildeComplexIso (ℳ : CochainComplex X.Modules ℤ)
    (hqc : ∀ i : ℤ, (ℳ.X i).IsQuasicoherent) {U : X.Opens} (hU : IsAffineOpen U) :
    ((tilde.functor Γ(X, U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Stacks.Eta.Sections.complex U ℳ) ≅
      ((restrictFunctor hU.fromSpec).mapHomologicalComplex (ComplexShape.up ℤ)).obj ℳ :=
  have hP : ∀ i : ℤ, IsIso (Scheme.Modules.fromTildeΓ
      ((((restrictFunctor hU.fromSpec).mapHomologicalComplex (ComplexShape.up ℤ)).obj ℳ).X i)) :=
    fun i => by
      have := hqc i
      change IsIso (Scheme.Modules.fromTildeΓ ((restrictFunctor hU.fromSpec).obj (ℳ.X i)))
      exact (isQuasicoherent_iff_isIso_fromTildeΓ _).mp inferInstance
  ((tilde.functor Γ(X, U)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      ((Functor.mapHomologicalComplexCompIso hU.restrictFromSpecGlobalSectionsIso
        (ComplexShape.up ℤ)).app ℳ).symm ≪≫
    Stacks.AffineTilde.tildeGammaComplexIso _ hP

/-- The same comparison read on the open subscheme `U` rather than on `Spec Γ(X, U)`. -/
def affineTildeModelComplexIso (ℳ : CochainComplex X.Modules ℤ)
    (hqc : ∀ i : ℤ, (ℳ.X i).IsQuasicoherent) {U : X.Opens} (hU : IsAffineOpen U) :
    ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj ℳ ≅
      ((tilde.functor Γ(X, U) ⋙ restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Stacks.Eta.Sections.complex U ℳ) :=
  ((Functor.mapHomologicalComplexCompIso
      ((restrictFunctorComp hU.isoSpec.hom hU.fromSpec).symm ≪≫
        restrictFunctorCongr hU.isoSpec_hom_fromSpec) (ComplexShape.up ℤ)).app ℳ).symm ≪≫
    ((restrictFunctor hU.isoSpec.hom).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (sectionsTildeComplexIso ℳ hqc hU).symm ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (tilde.functor Γ(X, U) ⋙ restrictFunctor hU.isoSpec.hom))
      (ComplexShape.up ℤ)).app (Stacks.Eta.Sections.complex U ℳ)

open AlgebraicGeometry.ComplexAndDivisorSituation in
/-- **The sections of a representative over an affine open are a model for the restriction.**  If
a complex `ℳ^•` of quasi-coherent `𝒪_X`-modules represents `M`, and the bounded complex `N` of
finite free `Γ(X, U)`-modules is its complex of sections over an affine open `U`, then `N`
represents `M|_U` in the sense that `AffineChart.isPrincipal_idealI_of_eq_basicOpen` asks for. -/
theorem nonempty_tildeModel_of_represents (S : ComplexAndDivisorSituation.{u, d})
    (ℳ : CochainComplex S.X.Modules ℤ) (hqc : ∀ i : ℤ, (ℳ.X i).IsQuasicoherent)
    (e : (@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj ℳ ≅ S.M)
    {U : S.X.Opens} (hU : IsAffineOpen U) (N : BoundedComplex Γ(S.X, U))
    (eN : Stacks.Eta.Sections.complex U ℳ ≅ N.toCochainComplex) :
    Nonempty ((restrictFunctor U.ι).mapDerivedCategory.obj S.M ≅
      (tilde.functor Γ(S.X, U) ⋙ restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj N.toCochainComplex)) :=
  ⟨(restrictFunctor U.ι).mapDerivedCategory.mapIso e.symm ≪≫
    (restrictFunctor U.ι).mapDerivedCategoryFactors.app ℳ ≪≫
    DerivedCategory.Q.mapIso (affineTildeModelComplexIso ℳ hqc hU ≪≫
      ((tilde.functor Γ(S.X, U) ⋙ restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso eN) ≪≫
    ((tilde.functor Γ(S.X, U) ⋙ restrictFunctor hU.isoSpec.hom).mapDerivedCategoryFactors.app
      N.toCochainComplex).symm⟩

/-! ### Free sections of a locally bounded complex of vector bundles -/

/-- **A locally bounded complex of finite locally free modules has free sections over small
enough affine opens.**  Every point has a neighbourhood `W` such that over every affine open
inside `W` all the modules of sections are free and all but finitely many vanish. -/
theorem exists_nhd_free_sections (ℳ : CochainComplex X.Modules ℤ)
    (hqc : ∀ n : ℤ, (ℳ.X n).IsQuasicoherent)
    (hflf : ∀ n : ℤ, Scheme.Modules.IsFiniteLocallyFree (ℳ.X n))
    (hlb : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ lo hi : ℤ, ∀ n : ℤ, (n < lo ∨ hi < n) →
      IsZero ((restrictModules X.toRingedSpace U).obj (ℳ.X n)))
    (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ W →
      (∀ n : ℤ, Module.Free Γ(X, V) Γ(ℳ.X n, V)) ∧
        {n : ℤ | ¬ Subsingleton Γ(ℳ.X n, V)}.Finite := by
  classical
  obtain ⟨U, hxU, lo, hi, hbd⟩ := hlb x
  choose Wn hxWn In hInfin eWn using fun n : ℤ => hflf n x
  refine ⟨U ⊓ ⨅ n : (Finset.Icc lo hi : Finset ℤ), Wn n.1,
    ⟨hxU, by simp only [Opens.coe_iInf, Set.mem_iInter]; exact fun n => hxWn n.1⟩, ?_⟩
  intro V hV hVW
  have hVU : V ≤ U := hVW.trans inf_le_left
  have hzero : ∀ n : ℤ, (n < lo ∨ hi < n) → Subsingleton Γ(ℳ.X n, V) := by
    intro n hn
    have := hqc n
    exact subsingleton_sections_of_isZero (ℳ.X n) V
      (Stacks.IdealTorsion.Eta.isZero_restrict_of_le hVU _ (hbd n hn))
  refine ⟨fun n => ?_, ?_⟩
  · by_cases hn : lo ≤ n ∧ n ≤ hi
    · have hVn : V ≤ Wn n :=
        hVW.trans (inf_le_right.trans
          (iInf_le _ (⟨n, Finset.mem_Icc.mpr hn⟩ : (Finset.Icc lo hi : Finset ℤ))))
      have := hqc n
      exact module_free_sections_of_restrict_iso_free (ℳ.X n) hV hVn (In n) (eWn n).some
    · have := hzero n (by omega)
      infer_instance
  · refine Set.Finite.subset (Set.finite_Icc lo hi) ?_
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    by_contra hc
    exact hn (hzero n (by simp only [Set.mem_Icc, not_and_or, not_le] at hc; omega))

/-! ### The décalage of a complex of vector bundles -/

/-- The chain-level décalage `η_ℐ ℳ^•` of a complex of `ℐ`-torsion-free `𝒪_X`-modules along the
ideal sheaf of an effective Cartier divisor. -/
def etaComplex (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (ℳ : CochainComplex X.Modules ℤ)
    (htf : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree X.toRingedSpace
      (idealSheafι D) (ℳ.X n)) : CochainComplex X.Modules ℤ :=
  letI := hD
  @etaObj X.toRingedSpace (idealSheaf D) (idealSheafι D)
    (Stacks.Divisors.Eta.mono_idealSheafι D) inferInstance ℳ htf

/-- An isomorphism of complexes of modules induces one of their décalages. -/
def etaObjectIso {A : Type u} [CommRing A] (f : A) {C E : EtaComplex.Complex.{u, u} A}
    (e : C ≅ E) : EtaComplex.etaObject f C ≅ EtaComplex.etaObject f E where
  hom := EtaComplex.etaMap f e.hom
  inv := EtaComplex.etaMap f e.inv
  hom_inv_id := by rw [← EtaComplex.etaMap_comp, e.hom_inv_id, EtaComplex.etaMap_id]
  inv_hom_id := by rw [← EtaComplex.etaMap_comp, e.inv_hom_id, EtaComplex.etaMap_id]

/-- The degree-`i` term of the décalage of a bounded matrix complex, read as the décalage term of
the matrix of its differential. -/
theorem term_toCochainComplex {A : Type u} [CommRing A] (C : BoundedComplex A) (f : A) (i : ℤ) :
    EtaComplex.term f C.toCochainComplex i = EtaPow.fetaTerm f ((C.d i).mulVecLin) i :=
  congrArg (fun dd => EtaPow.fetaTerm f dd i)
    (congrArg ModuleCat.Hom.hom (C.toCochainComplex_d i))

/-- **The sections of the décalage over an affine open form a finite locally free module.**  They
are the degree-`i` term of `η_f N^•` for the complex `N^•` of sections of `ℳ^•` in chosen bases,
which is finite locally free by Tag 0F7W once `I_i(N^•, f)` is principal. -/
theorem module_isFiniteLocallyFree_sections_etaComplex (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (ℳ : CochainComplex X.Modules ℤ) (hqc : ∀ n : ℤ, (ℳ.X n).IsQuasicoherent)
    (htf : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree X.toRingedSpace
      (idealSheafι D) (ℳ.X n))
    {U : X.Opens} (hU : IsAffineOpen U) (g : (idealSheaf D).val.obj (op U))
    (hg : Stacks.IdealTorsion.GeneratesIdealOn X.toRingedSpace U g)
    (hreg : IsRegular (generatorSection X.toRingedSpace (idealSheafι D) U g))
    (P : Stacks.Eta.BasisPresentation (Stacks.Eta.Sections.complex U ℳ)) (i : ℤ)
    (hprin : Submodule.IsPrincipal (idealI P.toBoundedComplex
      (generatorSection X.toRingedSpace (idealSheafι D) U g) i)) :
    Module.IsFiniteLocallyFree Γ(X, U) Γ((etaComplex D hD ℳ htf).X i, U) := by
  have := hD
  set f := generatorSection X.toRingedSpace (idealSheafι D) U g with hfdef
  have hterm : Module.IsFiniteLocallyFree Γ(X, U)
      (EtaComplex.term f P.toBoundedComplex.toCochainComplex i) := by
    rw [term_toCochainComplex]
    exact EtaPow.LocallyFree.isFiniteLocallyFree_fetaTerm P.toBoundedComplex f hreg i hprin
  have hterm' : Module.IsFiniteLocallyFree Γ(X, U)
      ((EtaComplex.etaObject f P.toBoundedComplex.toCochainComplex).X i) := hterm
  let ε : sectionsComplex X.toRingedSpace (etaComplex D hD ℳ htf) U ≅
      EtaComplex.etaObject f P.toBoundedComplex.toCochainComplex :=
    (Stacks.Divisors.Eta.etaSectionsIso D ℳ hqc htf U hU g hg).symm ≪≫ etaObjectIso f P.iso
  exact isFiniteLocallyFree_of_linearEquiv
    ((HomologicalComplex.eval _ _ i).mapIso ε).toLinearEquiv.symm hterm'

/-! ### The good-triple argument -/

open AlgebraicGeometry.ComplexAndDivisorSituation in
/-- **The sections of the décalage are finite locally free over a suitable affine open of every
point.**  Over a basic open of a good chart the determinantal ideals of the complex of sections
of `ℳ^•` are principal by the transfer of Tag 0GSS; off the divisor the equation of `D` is a
unit, so they are the unit ideal. -/
theorem exists_affineOpen_module_isFiniteLocallyFree_etaComplex
    (S : ComplexAndDivisorSituation.{u, d}) (hgood : S.IsGoodTriple)
    (ℳ : CochainComplex S.X.Modules ℤ) (hqc : ∀ n : ℤ, (ℳ.X n).IsQuasicoherent)
    (hflf : ∀ n : ℤ, Scheme.Modules.IsFiniteLocallyFree (ℳ.X n))
    (hlb : ∀ x : S.X, ∃ U : Opens S.X, x ∈ U ∧ ∃ lo hi : ℤ, ∀ n : ℤ, (n < lo ∨ hi < n) →
      IsZero ((restrictModules S.X.toRingedSpace U).obj (ℳ.X n)))
    (e : (@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj ℳ ≅ S.M)
    (htf : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree S.X.toRingedSpace
      (idealSheafι S.D) (ℳ.X n))
    (i : ℤ) (x : S.X) :
    ∃ U : S.X.affineOpens, x ∈ U.1 ∧
      Module.IsFiniteLocallyFree Γ(S.X, U.1)
        Γ((etaComplex S.D S.isEffectiveCartierDivisor ℳ htf).X i, U.1) := by
  have := S.isEffectiveCartierDivisor
  obtain ⟨W, hxW, hWfree⟩ := exists_nhd_free_sections ℳ hqc hflf hlb x
  have key : ∀ (V : S.X.affineOpens) (f : Γ(S.X, V.1)), V.1 ≤ W →
      S.D.ideal V = Ideal.span {f} → f ∈ nonZeroDivisors Γ(S.X, V.1) →
      (∀ P : Stacks.Eta.BasisPresentation (Stacks.Eta.Sections.complex V.1 ℳ),
        Submodule.IsPrincipal (idealI P.toBoundedComplex f i)) →
      Module.IsFiniteLocallyFree Γ(S.X, V.1)
        Γ((etaComplex S.D S.isEffectiveCartierDivisor ℳ htf).X i, V.1) := by
    intro V f hVW hspan hfnzd hprin
    obtain ⟨hfree, hzero⟩ := hWfree V.1 V.2 hVW
    have hfin : ∀ n : ℤ, Module.Finite Γ(S.X, V.1) Γ(ℳ.X n, V.1) := fun n => by
      have := hqc n
      exact ((Module.isFiniteLocallyFree_iff_finite_projective _ _).mp
        (module_isFiniteLocallyFree_sections (ℳ.X n) (hflf n) V.2)).1
    obtain ⟨P⟩ := Stacks.Eta.BasisPresentation.exists_of_free
      (K := Stacks.Eta.Sections.complex V.1 ℳ) hfree hfin hzero
    obtain ⟨g, hg, hgf⟩ :=
      Stacks.Divisors.Eta.exists_generatesIdealOn_of_ideal_eq_span S.D V hspan hfnzd
    refine module_isFiniteLocallyFree_sections_etaComplex S.D S.isEffectiveCartierDivisor ℳ
      hqc htf V.2 g hg ?_ P i ?_
    all_goals rw [hgf]
    · exact isRegular_iff_mem_nonZeroDivisors.mpr hfnzd
    · exact hprin P
  by_cases hx : x ∈ S.D.supportSet
  · obtain ⟨C₀, hxC₀, hprin₀⟩ := hgood x hx
    obtain ⟨g₀, hg₀le, hxg₀⟩ :=
      C₀.U.2.exists_basicOpen_le (⟨x, ⟨hxW, hxC₀⟩⟩ : (W ⊓ (C₀.U : S.X.Opens) : S.X.Opens)) hxC₀
    have hU : IsAffineOpen (S.X.basicOpen g₀) := C₀.U.2.basicOpen g₀
    have hle : S.X.basicOpen g₀ ≤ (C₀.U : S.X.Opens) := S.X.basicOpen_le g₀
    have hfnzd : (S.X.presheaf.map (homOfLE hle).op).hom C₀.f ∈
        nonZeroDivisors Γ(S.X, S.X.basicOpen g₀) :=
      mem_nonZeroDivisors_map_basicOpen C₀.U.2 g₀
        C₀.regular.mem_nonZeroDivisors
    refine ⟨⟨S.X.basicOpen g₀, hU⟩, hxg₀, key ⟨S.X.basicOpen g₀, hU⟩ _
      (hg₀le.trans inf_le_left)
      (ideal_basicOpen_eq_span_map S.D C₀.U.2 g₀ C₀.divisor_ideal) hfnzd fun P => ?_⟩
    exact AffineChart.isPrincipal_idealI_of_eq_basicOpen C₀ g₀ hU hle rfl P.toBoundedComplex
      (nonempty_tildeModel_of_represents S ℳ hqc e hU P.toBoundedComplex P.iso) hfnzd i
      (hprin₀ i)
  · obtain ⟨V, hxV, hVW, hVtop⟩ := exists_affineOpen_ideal_eq_top S.D hx W hxW
    refine ⟨V, hxV, key V 1 hVW (by rw [hVtop, Ideal.span_singleton_one]) (one_mem _)
      fun P => ?_⟩
    have htop : idealI P.toBoundedComplex (1 : Γ(S.X, V.1)) i = ⊤ := by
      refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
      simpa using pow_rank_mem_idealI P.toBoundedComplex (1 : Γ(S.X, V.1)) i
    exact ⟨1, htop.trans Ideal.span_singleton_one.symm⟩

open AlgebraicGeometry.ComplexAndDivisorSituation in
/-- **Every term of the décalage of a locally bounded complex of vector bundles on a good triple
is a finite locally free module.** -/
theorem isFiniteLocallyFree_etaComplex (S : ComplexAndDivisorSituation.{u, d})
    (hgood : S.IsGoodTriple) (ℳ : CochainComplex S.X.Modules ℤ)
    (hflf : ∀ n : ℤ, Scheme.Modules.IsFiniteLocallyFree (ℳ.X n))
    (hlb : ∀ x : S.X, ∃ U : Opens S.X, x ∈ U ∧ ∃ lo hi : ℤ, ∀ n : ℤ, (n < lo ∨ hi < n) →
      IsZero ((restrictModules S.X.toRingedSpace U).obj (ℳ.X n)))
    (e : (@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj ℳ ≅ S.M)
    (htf : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree S.X.toRingedSpace
      (idealSheafι S.D) (ℳ.X n))
    (i : ℤ) :
    Scheme.Modules.IsFiniteLocallyFree
      ((etaComplex S.D S.isEffectiveCartierDivisor ℳ htf).X i) := by
  have := S.isEffectiveCartierDivisor
  have hqc : ∀ n : ℤ, (ℳ.X n).IsQuasicoherent := fun n =>
    Stacks.DerivedQCoh.isQuasicoherent_of_isFiniteLocallyFree (ℳ.X n)
      ((Scheme.Modules.isFiniteLocallyFree_iff _).mp (hflf n))
  have : ((etaComplex S.D S.isEffectiveCartierDivisor ℳ htf).X i).IsQuasicoherent :=
    Stacks.Divisors.Eta.isQuasicoherent_etaObj S.D ℳ hqc htf i
  exact isFiniteLocallyFree_of_module_affineOpens _
    (exists_affineOpen_module_isFiniteLocallyFree_etaComplex S hgood ℳ hqc hflf hlb e htf i)

/-- **A finite locally free `𝒪_X`-module has no `ℐ`-torsion.**  It is flat, and the ideal sheaf
of an effective Cartier divisor is locally generated by a nonzerodivisor, so the third criterion
of Tag 0GT5 applies. -/
theorem isIdealTorsionFree_of_isFiniteLocallyFree (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (F : X.Modules)
    (h : Scheme.Modules.IsFiniteLocallyFree F) :
    Stacks.IdealTorsion.IsIdealTorsionFree X.toRingedSpace (idealSheafι D) F :=
  have := hD
  @Stacks.IdealTorsion.isIdealTorsionFree_of_isFlat X.toRingedSpace _
    (idealSheafι D) (Stacks.Divisors.Eta.mono_idealSheafι D)
    (@Stacks.IdealTorsion.isLocallyGeneratedByRegular_of_isInvertible X.toRingedSpace
      inferInstance _ (idealSheafι D) (Stacks.Divisors.Eta.mono_idealSheafι D)
      (Stacks.Divisors.Eta.isInvertible_idealSheaf D)) F
    (AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree F
      ((Scheme.Modules.isFiniteLocallyFree_iff _).mp h))

/-- **The décalage of a locally bounded complex is locally bounded**, with the range of degrees
extended by one downwards. -/
theorem isLocallyBounded_etaComplex (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (ℳ : CochainComplex X.Modules ℤ)
    (htf : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree X.toRingedSpace
      (idealSheafι D) (ℳ.X n))
    (hlb : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ lo hi : ℤ, ∀ n : ℤ, (n < lo ∨ hi < n) →
      IsZero ((restrictModules X.toRingedSpace U).obj (ℳ.X n)))
    (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∃ lo hi : ℤ, ∀ n : ℤ, (n < lo ∨ hi < n) →
      IsZero ((restrictModules X.toRingedSpace U).obj ((etaComplex D hD ℳ htf).X n)) :=
  have := hD
  Stacks.IdealTorsion.Eta.isLocallyBounded_etaObj X.toRingedSpace (idealSheaf D)
    (idealSheafι D) (Stacks.Divisors.Eta.mono_idealSheafι D)
    (Stacks.Divisors.Eta.isInvertible_idealSheaf D) ℳ htf hlb x

/-! ### The tag -/

open AlgebraicGeometry.ComplexAndDivisorSituation in
/-- **Stacks Project, Tag 0GTX.**  Let `X` be a scheme, `D ⊆ X` an effective Cartier divisor
with ideal sheaf `ℐ`, and `M` a perfect object of `D(𝒪_X)`, and assume `(X, D, M)` is a good
triple.  If `M` is represented by a locally bounded complex of finite locally free
`𝒪_X`-modules, then so is `Lη_ℐ M`.

The representing complex for `Lη_ℐ M` is the chain-level décalage `η_ℐ ℳ^•` of the given one. -/
@[stacks 0GTX]
theorem exists_isLocallyBoundedFiniteLocallyFree_derivedEta (X : Scheme.{u})
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (M : DerivedCategory X.Modules)
    (hM : RingedSpace.IsPerfect (X := X.toRingedSpace) M)
    (hgood : IsGoodTriple
      { X := X, D := D, isEffectiveCartierDivisor := hD, M := M, isPerfect := hM })
    (hrep : ∃ ℳ : CochainComplex X.Modules ℤ,
      Stacks.Chow.IsLocallyBoundedFiniteLocallyFree ℳ ∧
        Nonempty (DerivedCategory.Q.obj ℳ ≅ M)) :
    ∃ 𝒬 : CochainComplex X.Modules ℤ,
      Stacks.Chow.IsLocallyBoundedFiniteLocallyFree 𝒬 ∧
        Nonempty (DerivedCategory.Q.obj 𝒬 ≅
          (@Stacks.Divisors.Eta.derivedEtaData X D hD).functor.obj M) := by
  obtain ⟨ℳ, ⟨hflf, hlb⟩, ⟨e⟩⟩ := hrep
  have hflf' : ∀ n : ℤ, Scheme.Modules.IsFiniteLocallyFree (ℳ.X n) := fun n =>
    (Scheme.Modules.isFiniteLocallyFree_iff _).mpr (hflf n)
  have htf : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree X.toRingedSpace
      (idealSheafι D) (ℳ.X n) := fun n =>
    isIdealTorsionFree_of_isFiniteLocallyFree D hD (ℳ.X n) (hflf' n)
  refine ⟨etaComplex D hD ℳ htf, ⟨fun n => ?_, isLocallyBounded_etaComplex D hD ℳ htf hlb⟩,
    ⟨((@Stacks.Divisors.Eta.derivedEtaData X D hD).objIso ℳ htf).symm ≪≫
      (@Stacks.Divisors.Eta.derivedEtaData X D hD).functor.mapIso e⟩⟩
  exact (Scheme.Modules.isFiniteLocallyFree_iff _).mp
    (isFiniteLocallyFree_etaComplex
      { X := X, D := D, isEffectiveCartierDivisor := hD, M := M, isPerfect := hM }
      hgood ℳ hflf' hlb e htf n)


/-! ### Tag 0GU0 -/


attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 100000]
  AlgebraicGeometry.ComplexAndDivisorSituation.modulesHasDerivedCategory

variable {X : Scheme.{u}}

/-! ### Pullback of a locally bounded complex of finite locally free modules -/

/-- **The restriction of a pullback is a pullback of the restriction.**  For a morphism of
schemes `g : Y ⟶ X` and an open `U ⊆ X`, restricting `g^*ℱ` to `g⁻¹U` is the pullback of
`ℱ|_U` along the induced morphism `g⁻¹U ⟶ U`. -/
def pullbackRestrictIso {Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens) (ℱ : X.Modules) :
    (Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback g).obj ℱ) ≅
      (Scheme.Modules.pullback (g ∣_ U)).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj ℱ) :=
  (Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ U).ι).app
      ((Scheme.Modules.pullback g).obj ℱ) ≪≫
    (Scheme.Modules.pullbackComp (g ⁻¹ᵁ U).ι g).app ℱ ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι g U)).symm.app ℱ ≪≫
        (Scheme.Modules.pullbackComp (g ∣_ U) U.ι).symm.app ℱ ≪≫
          (Scheme.Modules.pullback (g ∣_ U)).mapIso
            ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app ℱ).symm

/-- **The pullback of a locally bounded complex of finite locally free modules is again one.**
Finite local freeness is preserved termwise, and a term vanishing after restriction to an open
`U` vanishes after restriction to `g⁻¹U`, so the bounds valid near `g(y)` are valid near `y`. -/
theorem isLocallyBoundedFiniteLocallyFree_pullback {Y : Scheme.{u}} (g : Y ⟶ X)
    (ℳ : CochainComplex X.Modules ℤ)
    (hℳ : Stacks.Chow.IsLocallyBoundedFiniteLocallyFree ℳ) :
    Stacks.Chow.IsLocallyBoundedFiniteLocallyFree
      (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj ℳ) := by
  refine ⟨fun n =>
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme g (ℳ.X n) (hℳ.1 n),
    fun y => ?_⟩
  obtain ⟨U₀, hyU, lo, hi, hbd⟩ := hℳ.2 (g.base y)
  let U : X.Opens := U₀
  refine ⟨g ⁻¹ᵁ U, hyU, lo, hi, fun n hn => ?_⟩
  have h0 : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj (ℳ.X n)) :=
    (hbd n hn).of_iso
      ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X U).app
        (ℳ.X n)).symm
  have h1 : IsZero ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).obj
      ((Scheme.Modules.pullback g).obj (ℳ.X n))) :=
    (Functor.map_isZero (Scheme.Modules.pullback (g ∣_ U)) h0).of_iso
      (pullbackRestrictIso g U (ℳ.X n))
  exact h1.of_iso
    ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict Y (g ⁻¹ᵁ U)).app
      ((Scheme.Modules.pullback g).obj (ℳ.X n)))

/-! ### K-flatness of a locally bounded complex of finite locally free modules -/

/-- **A module vanishing on an open neighbourhood of a point has vanishing stalk there.** -/
theorem isZero_stalkFunctor_obj_of_isZero_restrictModules {U : X.Opens} {x : X} (hx : x ∈ U)
    (ℱ : X.Modules)
    (hℱ : IsZero ((AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U).obj ℱ)) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x).obj ℱ) := by
  have h0 : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj ℱ) :=
    hℱ.of_iso
      ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X U).app ℱ).symm
  have h1 : IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.val.presheaf x) :=
    (Stacks.AlgebraicGeometry.PerfectCohomology.isZero_stalk_of_isZero
        ((Scheme.Modules.restrictFunctor U.ι).obj ℱ) h0 ⟨x, hx⟩).of_iso
      ((Scheme.Modules.restrictStalkNatIso U.ι ⟨x, hx⟩).app ℱ).symm
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.isZero_iff_subsingleton.mp h1)

/-- **A zero module is flat.**  All of its stalks vanish, and a zero module over a ring is
flat. -/
theorem isFlat_of_isZero (ℱ : X.Modules) (hℱ : IsZero ℱ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) ℱ := by
  refine (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf ℱ).2 fun x => ?_
  have hs : Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.val.presheaf x) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp
      (Stacks.AlgebraicGeometry.PerfectCohomology.isZero_stalk_of_isZero ℱ hℱ x)
  -- `Subsingleton`, `Module.Free` and `Module.Flat` are all Prop-valued, and
  -- `hs → Module.Free → Module.Flat` is the canonical chain; it is named rather than left to
  -- instance search, which cannot run it.  The coercion of the stalk to a type that `hs` carries
  -- agrees with the one in the goal only above `instances` transparency, so `hs` is not a
  -- candidate for the `Subsingleton` side condition of `Module.Free.of_subsingleton`.  The `?_`s
  -- are what make this work: every instance argument is then taken from the goal by unification
  -- rather than searched for, so nothing is added and no second module structure is created.
  -- Writing `_` for them instead searches, and the stalk's `Module` -- the one
  -- `isFlat_iff_stalk_flat` seats in its own statement -- is not findable at this spelling.
  refine @Module.Flat.of_free _ _ ?_ ?_ ?_ ?_
  refine @Module.Free.of_subsingleton _ _ ?_ ?_ ?_ hs

/-- **The stalk complex of a stupid truncation.**  If the stalks at `x` of the terms of `ℳ^•` in
degrees above `n` vanish, then the stalk complex at `x` of the truncation of `ℳ^•` to the
degrees `≤ n` is the stalk complex of `ℳ^•` itself. -/
def stalkComplexStupidTruncIso {T : TopCat.{u}}
    (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology T) CommRingCat.{u})
    (x : T)
    (ℳ : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (n : ℤ)
    (hℳ : ∀ i : ℤ, n < i → IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf R) x).obj (ℳ.X i))) :
    AlgebraicGeometry.SheafOfModules.stalkComplex R x
        (ℳ.stupidTrunc (ComplexShape.embeddingUpIntLE n)) ≅
      AlgebraicGeometry.SheafOfModules.stalkComplex R x ℳ := by
  classical
  dsimp only [AlgebraicGeometry.SheafOfModules.stalkComplex]
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => if hi : ∃ k, (ComplexShape.embeddingUpIntLE n).f k = i then
        (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf R) x).mapIso
          (ℳ.stupidTruncXIso (ComplexShape.embeddingUpIntLE n) hi.choose_spec)
      else ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf R) x).map_isZero
        (ℳ.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE n) i (by simpa using hi))).iso
        (hℳ i ((ComplexShape.notMem_range_embeddingUpIntLE_iff n i).1 (by simpa using hi))))
    ?_
  intro i j hij
  by_cases hi : ∃ k, (ComplexShape.embeddingUpIntLE n).f k = i
  · by_cases hj : ∃ k, (ComplexShape.embeddingUpIntLE n).f k = j
    · simp only [dite_eq_left hi, dite_eq_left hj, Functor.mapIso_hom,
        Functor.mapHomologicalComplex_obj_d]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      have hi' := hi.choose_spec
      have hj' := hj.choose_spec
      rcases hi with ⟨a, rfl⟩
      rcases hj with ⟨b, rfl⟩
      have ha : (Exists.choose (show ∃ k, (ComplexShape.embeddingUpIntLE n).f k =
          (ComplexShape.embeddingUpIntLE n).f a from ⟨a, rfl⟩)) = a :=
        (ComplexShape.embeddingUpIntLE n).injective_f hi'
      have hb : (Exists.choose (show ∃ k, (ComplexShape.embeddingUpIntLE n).f k =
          (ComplexShape.embeddingUpIntLE n).f b from ⟨b, rfl⟩)) = b :=
        (ComplexShape.embeddingUpIntLE n).injective_f hj'
      simp only [ha, hb]
      dsimp [HomologicalComplex.stupidTrunc, HomologicalComplex.stupidTruncXIso]
      rw [HomologicalComplex.extend_d_eq _ (ComplexShape.embeddingUpIntLE n) rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simp [HomologicalComplex.restriction]
    · exact (hℳ j ((ComplexShape.notMem_range_embeddingUpIntLE_iff n j).1
        (by simpa using hj))).eq_of_tgt _ _
  · exact ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf R) x).map_isZero
      (ℳ.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE n) i
        (by simpa using hi))).eq_of_src _ _

/-- **A locally bounded complex of finite locally free `𝒪_X`-modules is K-flat.**  K-flatness is
a condition on the stalk complexes (Tag 06YB), and only finitely many degrees of the complex are
nonzero near a given point: the truncation of `ℳ^•` to the degrees `≤ hi` is bounded above with
flat terms, hence K-flat (Tag 06YQ), and at a point near which `ℳ^•` vanishes above degree `hi`
it has the same stalk complex as `ℳ^•`. -/
theorem kFlatComplex_of_isLocallyBoundedFiniteLocallyFree (ℳ : CochainComplex X.Modules ℤ)
    (hℳ : Stacks.Chow.IsLocallyBoundedFiniteLocallyFree ℳ) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace ℳ := by
  classical
  refine Stacks.SheafOfModules.KFlatPullback.stalkCriterion.kFlat_of_kFlatStalkwise
    X.toRingedSpace ℳ fun x => ?_
  obtain ⟨U₀, hx, lo, hi, hbd⟩ := hℳ.2 x
  let U : X.Opens := U₀
  have hzero : ∀ i : ℤ, hi < i → IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x).obj (ℳ.X i)) := fun i h =>
    isZero_stalkFunctor_obj_of_isZero_restrictModules (U := U) hx (ℳ.X i) (hbd i (Or.inr h))
  have hT : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace
      (ℳ.stupidTrunc (ComplexShape.embeddingUpIntLE hi)) := by
    refine AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat
      X.toRingedSpace _ ⟨hi, ?_⟩ fun i => ?_
    · exact ⟨fun i' hi' => ℳ.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE hi) i' hi'⟩
    · by_cases hi' : ∃ k, (ComplexShape.embeddingUpIntLE hi).f k = i
      · exact AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _
          (@AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso X _ _
            (ℳ.stupidTruncXIso (ComplexShape.embeddingUpIntLE hi) hi'.choose_spec).symm (hℳ.1 i))
      · exact isFlat_of_isZero _ (ℳ.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE hi) i
          (by simpa using hi'))
  exact Stacks.SheafOfModules.KFlatPullback.kFlat_of_stalkIso X.sheaf x
    (stalkComplexStupidTruncIso X.sheaf x ℳ hi hzero)
    (Stacks.SheafOfModules.KFlatPullback.stalkCriterion.kFlatStalkwise_of_kFlat
      X.toRingedSpace _ hT x)

/-! ### The derived pullback of the object of a triple -/

/-- **A locally bounded complex of finite locally free modules representing `M` has pullback
representing `Lb^*M`.**  The complex is K-flat, so the comparison `Lb^*ℳ^• ⟶ b^*ℳ^•` of
Tag 06YJ is invertible; the given isomorphism lives at the model of `D(𝒪_X)` carried by the
triple and is carried to the standard model, at which `Lb^*M` is formed, by the canonical
equivalence of two localizations at the quasi-isomorphisms. -/
theorem nonempty_iso_derivedPullbackObject
    (S : AlgebraicGeometry.ComplexAndDivisorSituation.{u, d}) {X' : Scheme.{u}} (b : X' ⟶ S.X)
    (ℳ : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ)
    (hℳ : Stacks.Chow.IsLocallyBoundedFiniteLocallyFree ℳ)
    (e : (@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj ℳ ≅ S.M) :
    Nonempty ((@DerivedCategory.Q _ _ _
          (HasDerivedCategory.standard (OXMod.{u, u} X'.toRingedSpace))).obj
        (((Scheme.Modules.pullback b).mapHomologicalComplex (ComplexShape.up ℤ)).obj ℳ) ≅
      S.derivedPullbackObject b) := by
  have hkf := kFlatComplex_of_isLocallyBoundedFiniteLocallyFree (X := S.X) ℳ hℳ
  refine ⟨(Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat b.toLRSHom.toShHom ℳ hkf).symm ≪≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        b.toLRSHom.toShHom).mapIso ?_⟩
  exact ((Localization.compUniqFunctor (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
      (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (OXMod.{u, u} S.X.toRingedSpace)))
      (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
        (ComplexShape.up ℤ))).app ℳ).symm ≪≫
    (Localization.uniq (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
      (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (OXMod.{u, u} S.X.toRingedSpace)))
      (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
        (ComplexShape.up ℤ))).functor.mapIso e

/-! ### The tag -/

/-- **Stacks Project, Tag 0GU0.**  Let `(X, D, M)` be a triple as in Situation 0F8S and let
`b : X' ⟶ X` be a morphism along which the pullback `D' = b⁻¹D` of the effective Cartier divisor
is defined and makes the pulled-back triple `(X', D', Lb^*M)` good — the two conditions that
Stacks tag 0GTY's morphism satisfies.  If `M` is represented by a locally bounded complex of
finite locally free `𝒪_X`-modules, then `Q = Lη_{ℐ'}Lb^*M` is represented by a locally bounded
complex of finite locally free `𝒪_{X'}`-modules.

The pullback `b^*ℳ^•` of a representative of `M` is a locally bounded complex of finite locally
free `𝒪_{X'}`-modules representing `Lb^*M`, so tag 0GTX applies to the pulled-back triple. -/
@[stacks 0GU0 "for every `b` along which `b⁻¹D` is defined and the pulled-back triple is good, \
in particular the morphism of Tag 0GTY (`goodBlowupToBase`); `Q` is stated directly as \
`Lη_{ℐ'}Lb^*M`"]
theorem exists_isLocallyBoundedFiniteLocallyFree_etaDerivedPullback
    (S : AlgebraicGeometry.ComplexAndDivisorSituation.{u, d}) {X' : Scheme.{u}} (b : X' ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined b S.D)
    (hgood : AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodTriple (S.pullback b hD))
    (hrep : ∃ ℳ : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ,
      Stacks.Chow.IsLocallyBoundedFiniteLocallyFree ℳ ∧
        Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj ℳ ≅ S.M)) :
    ∃ 𝒬 : CochainComplex X'.Modules ℤ,
      Stacks.Chow.IsLocallyBoundedFiniteLocallyFree 𝒬 ∧
        Nonempty (DerivedCategory.Q.obj 𝒬 ≅
          (Stacks.Divisors.Eta.derivedEtaData (S.D.comap b)).functor.obj
            (S.derivedPullbackObject b)) := by
  obtain ⟨ℳ, hℳ, ⟨e⟩⟩ := hrep
  exact exists_isLocallyBoundedFiniteLocallyFree_derivedEta X' (S.D.comap b) hD
    (S.derivedPullbackObject b) (S.isPerfect_derivedPullbackObject b) hgood
    ⟨((Scheme.Modules.pullback b).mapHomologicalComplex (ComplexShape.up ℤ)).obj ℳ,
      isLocallyBoundedFiniteLocallyFree_pullback b ℳ hℳ,
      nonempty_iso_derivedPullbackObject S b ℳ hℳ e⟩

end Stacks.BlowUpComplexes

end
