module

public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTriple
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTriplePreparation
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DepthCoherence.ReflexiveExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.PuncturedSpectrumCompletion
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeExtension
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumPicardInjectivitySGA2
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer

/-!
# The global-sections map of an invertible coherent triple

Let `A` be a local ring, let `f ∈ A`, and let `T` be a coherent triple for `(A, f)`. Restricting a
section of the module on the punctured spectrum `U` to the punctured closed fibre `U₀` and reading
the result through the triple's identification gives a map `Γ(U, F) → Γ(U₀, F₀)`. This file
constructs that map, proves that it is linear over `A`, and -- when the two members of the triple
are invertible and `A` is Noetherian local of depth at least three -- that the cokernel of the map
has finite length.

When the depth of `A` is at least three, the depth of `A / fA` is at least two, so Hartogs
extension identifies the closed-fibre member of the triple with the direct image of its own
restriction to the punctured closed fibre; in particular restriction of global sections there is
bijective. The direct image of the punctured-spectrum member along the inclusion of the punctured
spectrum is then itself a prepared extension of the triple, and its closed-fibre map has the same
cokernel as the map on global sections.

## Main definitions

* `Stacks.Algebraization.puncturedScalars` and
  `Stacks.Algebraization.puncturedClosedFibreScalars`: the two structure maps from `A` to the
  functions on the punctured spectrum and on the punctured closed fibre.
* `Stacks.Algebraization.puncturedSectionsModule` and
  `Stacks.Algebraization.puncturedClosedFibreSectionsModule`: the `A`-module structures they
  induce on global sections.
* `Stacks.Algebraization.globalSectionsMap`: the canonical `A`-linear map on global sections, the
  map whose cokernel the Euler characteristic of an invertible triple computes.

## Main results

* `Stacks.Algebraization.finiteLength_cokernel_globalSectionsMap`: the cokernel of the canonical
  map on global sections has finite length over `A`.
* `Stacks.Algebraization.exists_preparedExtension_length_cokernel_eq`: the direct image of the
  punctured-spectrum member is a prepared extension of the triple whose closed-fibre map has a
  cokernel of the same length as that of the map on global sections, and which is surjective
  exactly when that map is.
* `Stacks.Algebraization.injective_closedFibreMap_of_two_le_depth`: the closed-fibre map of a
  prepared extension whose global sections have depth at least two over `A` is injective.

## Implementation notes

Sections of a module over a scheme carry a module structure over the functions on that scheme, so
both sides of the map are turned into `A`-modules through the structure maps above; those module
structures are supplied by `letI` in the statements rather than declared as instances, since the
two sheaves involved live on different schemes and no canonical `A`-action is intended globally.

The punctured closed fibre is `Stacks.Algebraization.puncturedClosedFibre`, the preimage of the
punctured spectrum under the closed immersion, and the morphism along which the restriction is
taken is `AlgebraicGeometry.morphismRestrict` of the closed immersion, which is the arrow the
triple's identification is stated over. Restriction of global sections along a morphism of schemes
is `AlgebraicGeometry.pullbackGlobalSections`.

Invertibility is used only through coherence and reflexivity: an invertible module is finite
locally free of rank one, hence coherent with free stalks, hence reflexive, and the extension
results of `Stacks.FundamentalGroup.DepthCoherence` apply to it. That is why the depth hypothesis
enters only as the depth of the structure sheaf at the closed point, which is the depth of `A`.

## References

* [Stacks Project, Tag 0F28](https://stacks.math.columbia.edu/tag/0F28)
* [Stacks Project, Tag 0F25](https://stacks.math.columbia.edu/tag/0F25)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace
open scoped Pointwise

universe u

namespace Stacks.Algebraization

/-- The ring map from `A` to the functions on the punctured spectrum of `A`. -/
noncomputable def puncturedScalars (A : Type u) [CommRing A] [IsLocalRing A] :
    A →+* Γ((Stacks.Divisors.puncturedSpectrum A).toScheme, ⊤) :=
  (Stacks.Divisors.puncturedSpectrum A).ι.appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- The ring map from `A` to the functions on the punctured closed fibre of `(A, f)`. -/
noncomputable def puncturedClosedFibreScalars (A : Type u) [CommRing A] [IsLocalRing A] (f : A) :
    A →+* Γ((puncturedClosedFibre A f).toScheme, ⊤) :=
  (puncturedClosedFibre A f).ι.appTop.hom.comp
    ((closedImmersion A f).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)

/-- Global sections on the punctured spectrum as an `A`-module. -/
@[instance_reducible]
noncomputable def puncturedSectionsModule (A : Type u) [CommRing A] [IsLocalRing A]
    (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules) :
    Module A Γ(F, ⊤) :=
  Module.compHom _ (puncturedScalars A)

/-- Global sections on the punctured closed fibre as an `A`-module. -/
@[instance_reducible]
noncomputable def puncturedClosedFibreSectionsModule (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (F : (puncturedClosedFibre A f).toScheme.Modules) :
    Module A Γ(F, ⊤) :=
  Module.compHom _ (puncturedClosedFibreScalars A f)

/-- **Restriction on global sections is bijective when the module is the direct image of its
own inverse image.** For `g : X ⟶ Y` and `F` on `Y` whose unit of the pullback-pushforward
adjunction is an isomorphism, `AlgebraicGeometry.pullbackGlobalSections g F` is a bijection
`Γ(F, ⊤) ≃ Γ(g^* F, ⊤)`. -/
theorem bijective_pullbackGlobalSections_of_isIso_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : Y.Modules) [IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F)] :
    Function.Bijective (pullbackGlobalSections g F) := by
  have h : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).app ⊤) := by
    show IsIso (((Scheme.Modules.toPresheaf Y).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F)).app (.op ⊤))
    infer_instance
  have hb := (ConcreteCategory.isIso_iff_bijective _).mp h
  refine ⟨fun a b hab => hb.injective ?_, fun y => ?_⟩
  · exact (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit g F a).symm.trans
      (hab.trans (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit g F b))
  · obtain ⟨a, ha⟩ := hb.surjective y
    exact ⟨a, (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit g F a).trans ha⟩

private theorem pullbackGlobalSections_comp_inv {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (F : Z.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackComp g h).inv.app F).app ⊤
      (pullbackGlobalSections (g ≫ h) F s) =
        pullbackGlobalSections g ((Scheme.Modules.pullback h).obj F)
          (pullbackGlobalSections h F s) := by
  rw [← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp]
  exact congrArg (fun a => a.app ⊤
      (pullbackGlobalSections g ((Scheme.Modules.pullback h).obj F)
        (pullbackGlobalSections h F s)))
    ((Scheme.Modules.pullbackComp g h).app F).hom_inv_id

private theorem puncturedClosedImmersion_appTop (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (a : A) :
    (puncturedClosedFibreRestriction A f).appTop.hom (puncturedScalars A a) =
      puncturedClosedFibreScalars A f a := by
  show (((puncturedClosedFibreRestriction A f ≫
      (Stacks.Divisors.puncturedSpectrum A).ι).appTop.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) a =
    ((((puncturedClosedFibre A f).ι ≫ closedImmersion A f).appTop.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) a
  rw [morphismRestrict_ι]

/-- **The canonical map on global sections of a coherent triple.** It carries a section of the
module on the punctured spectrum to its restriction to the punctured closed fibre, read through
the triple's identification as a section of the module on the closed fibre. It is linear over
`A`, which acts on both sides through the structure morphisms. -/
@[stacks 0F28 "the canonical map on global sections"]
noncomputable def globalSectionsMap (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    (T : CoherentTriple A f) :
    letI := puncturedSectionsModule A T.F
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
    Γ(T.F, ⊤) →ₗ[A] Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀, ⊤) :=
  letI := puncturedSectionsModule A T.F
  letI := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  { toFun := fun s => T.alpha.hom.app ⊤ (pullbackGlobalSections
        (puncturedClosedFibreRestriction A f)
      T.F s)
    map_add' := fun x y => by
      simp only [map_add]
    map_smul' := fun a x => by
      change T.alpha.hom.app ⊤ (pullbackGlobalSections (puncturedClosedFibreRestriction A f) T.F
          (puncturedScalars A a • x)) =
        puncturedClosedFibreScalars A f a •
          T.alpha.hom.app ⊤ (pullbackGlobalSections (puncturedClosedFibreRestriction A f) T.F x)
      rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
        Scheme.Modules.Hom.app_smul,
        puncturedClosedImmersion_appTop] }

/-- The canonical map on global sections is the restriction map followed by the triple's
identification. -/
theorem globalSectionsMap_apply (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    (T : CoherentTriple A f) (s : Γ(T.F, ⊤)) :
    globalSectionsMap A f T s =
      T.alpha.hom.app ⊤ (pullbackGlobalSections (puncturedClosedFibreRestriction A f) T.F s) :=
  rfl

/-! ### Invertible modules are coherent and reflexive -/

/-- An invertible module on a locally Noetherian scheme is reflexive: it is finite locally free
of rank one, hence coherent with free stalks. -/
private theorem isReflexive_of_isInvertible (X : Scheme.{u}) [IsLocallyNoetherian X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Stacks.AlgebraicGeometry.ReflexiveModules.IsReflexive L := by
  have hc : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := X.ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X L
  have h2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  exact Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree L
    ((Stacks.Modules.isFiniteLocallyFree_iff_localGenerators L).mpr h2)

/-! ### Depth along the complement of the closed point -/

/-- The structure sheaf of the spectrum of a local ring of depth at least two has depth at least
two at every point off the punctured spectrum, there being only the closed point there. -/
private theorem two_le_depth_stalk_notMem_puncturedSpectrum (A : Type u) [CommRing A]
    [IsLocalRing A] (hdepth : 2 ≤ Module.depth A (maximalIdeal A) A)
    (x : Spec (CommRingCat.of A))
    (hx : x ∉ (Stacks.Divisors.puncturedSpectrum A : Set (Spec (CommRingCat.of A)))) :
    (2 : ℕ∞) ≤ Module.depth ((Spec (CommRingCat.of A)).presheaf.stalk x)
      (maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk x))
      ((Spec (CommRingCat.of A)).presheaf.stalk x) := by
  have heq : x = closedPoint A := not_not.mp hx
  subst heq
  exact Stacks.AlgebraicGeometry.PicardBaseChange.le_depth_stalk_of_isClosed A hdepth
    (closedPoint A) ((PrimeSpectrum.isClosed_singleton_iff_isMaximal (closedPoint A)).mpr
      (IsLocalRing.maximalIdeal.isMaximal A))

/-- **A coherent reflexive module on the spectrum of a Noetherian local ring of depth at least
two is the direct image of its restriction to the punctured spectrum.** This is Hartogs
extension, the complement of the punctured spectrum being the closed point. -/
private theorem isIso_unit_puncturedSpectrum (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (F : (Spec (CommRingCat.of A)).Modules)
    [_root_.SheafOfModules.IsCoherent F]
    (hF : Stacks.AlgebraicGeometry.ReflexiveModules.IsReflexive F)
    (hdepth : 2 ≤ Module.depth A (maximalIdeal A) A) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.app F) :=
  Stacks.FundamentalGroup.DepthCoherence.isIso_unit_of_isReflexive
    (Stacks.Divisors.puncturedSpectrum A) F hF
    (two_le_depth_stalk_notMem_puncturedSpectrum A hdepth)

/-- An invertible module on the spectrum of a Noetherian local ring of depth at least two is the
direct image of its restriction to the punctured spectrum. -/
theorem isIso_unit_puncturedSpectrum_of_isInvertible (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (F : (Spec (CommRingCat.of A)).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (Spec (CommRingCat.of A)).presheaf
      (Spec (CommRingCat.of A)).ringCatSheaf.2 F]
    (hdepth : 2 ≤ Module.depth A (maximalIdeal A) A) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.app F) :=
  have : _root_.SheafOfModules.IsCoherent F :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible _ F
  isIso_unit_puncturedSpectrum A F (isReflexive_of_isInvertible _ F) hdepth

/-- **Dropping a regular element of the maximal ideal drops the depth by one.** -/
@[ega "0 16.4.6" "(ii) for M = A", sga "2 III 2.5" "Case M = A"]
theorem depth_quotient_span_singleton_add_one (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    [IsLocalRing (A ⧸ Ideal.span {f})] :
    Module.depth (A ⧸ Ideal.span {f}) (maximalIdeal (A ⧸ Ideal.span {f}))
        (A ⧸ Ideal.span {f}) + 1 =
      Module.depth A (maximalIdeal A) A := by
  have h := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (maximalIdeal A) A).1 f hf hreg.left
  rw [Module.depth_eq_depth_of_linearEquiv (maximalIdeal A)
      (show QuotSMulTop f A ≃ₗ[A] (A ⧸ Ideal.span {f}) from
        Submodule.quotEquivOfEq _ _ (by
          rw [← Submodule.ideal_span_singleton_smul]
          simp)),
    Module.depth_eq_depth_map_algebraMap (B := A ⧸ Ideal.span {f})
      Ideal.Quotient.mk_surjective,
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A (A ⧸ Ideal.span {f}))
      Ideal.Quotient.mk_surjective] at h
  exact h

/-- From depth at least three on `A` to depth at least two on `A / fA`. -/
private theorem two_le_depth_quotient (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    [IsLocalRing (A ⧸ Ideal.span {f})]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    2 ≤ Module.depth (A ⧸ Ideal.span {f}) (maximalIdeal (A ⧸ Ideal.span {f}))
      (A ⧸ Ideal.span {f}) := by
  apply (ENat.add_le_add_iff_right (show (1 : ℕ∞) ≠ ⊤ by simp)).mp
  simpa only [show (2 : ℕ∞) + 1 = 3 by rfl,
    depth_quotient_span_singleton_add_one A f hf hreg] using hdepth

/-- **The closed-fibre member of an invertible triple is the direct image of its restriction to
the punctured closed fibre.** The punctured closed fibre is the punctured spectrum of `A / fA`,
whose depth is at least two. -/
theorem isIso_unit_puncturedClosedFibre (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    [IsLocalRing (A ⧸ Ideal.span {f})] (F₀ : (closedFibre A f).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (puncturedClosedFibre A f).ι).unit.app F₀) := by
  rw [puncturedClosedFibre_eq_puncturedSpectrum A f hf]
  exact isIso_unit_puncturedSpectrum_of_isInvertible (A ⧸ Ideal.span {f}) F₀
    (two_le_depth_quotient A f hf hreg hdepth)

/-! ### The direct image of an invertible module from the punctured spectrum -/

/-- **The direct image of an invertible module from the punctured spectrum of a Noetherian local
ring of depth at least two is coherent and reflexive.** The invertible module is coherent and
reflexive, and it extends to a coherent module on `Spec A`, so the backward half of the
reflexive-extension equivalence applies. -/
private theorem isCoherent_isReflexive_pushforward_puncturedSpectrum (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A]
    (L : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 L]
    (hdepth : 2 ≤ Module.depth A (maximalIdeal A) A) :
    _root_.SheafOfModules.IsCoherent
        ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj L) ∧
      Stacks.AlgebraicGeometry.ReflexiveModules.IsReflexive
        ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj L) := by
  have : IsLocallyNoetherian (Stacks.Divisors.puncturedSpectrum A).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (Stacks.Divisors.puncturedSpectrum A).ι
  have hLc : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible _ L
  have : L.IsCoherent := hLc
  obtain ⟨E, hE, ⟨e⟩⟩ := AlgebraicGeometry.exists_isCoherent_restrict_iso
    (Stacks.Divisors.puncturedSpectrum A)
    (TopologicalSpace.NoetherianSpace.isCompact _) L
  have : _root_.SheafOfModules.IsCoherent E := hE
  exact Stacks.FundamentalGroup.DepthCoherence.isCoherent_isReflexive_pushforward_of_extension
    (Stacks.Divisors.puncturedSpectrum A) L E e (isReflexive_of_isInvertible _ L)
    (two_le_depth_stalk_notMem_puncturedSpectrum A hdepth)

/-- The direct image of an invertible module from the punctured spectrum is recovered from its
own restriction: it is coherent and reflexive, so Hartogs extension applies to it. -/
theorem isIso_unit_pushforward_puncturedSpectrum (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A]
    (L : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 L]
    (hdepth : 2 ≤ Module.depth A (maximalIdeal A) A) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.app
        ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj L)) := by
  obtain ⟨hc, hr⟩ := isCoherent_isReflexive_pushforward_puncturedSpectrum A L hdepth
  have : _root_.SheafOfModules.IsCoherent
    ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj L) := hc
  exact isIso_unit_puncturedSpectrum A _ hr hdepth

private theorem exists_map_eq_of_isIso_unit {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {V W : C}
    [IsIso (adj.unit.app W)] (a : L.obj V ⟶ L.obj W) :
    ∃ b : V ⟶ W, L.map b = a := by
  refine ⟨adj.homEquiv V (L.obj W) a ≫ inv (adj.unit.app W),
    (adj.homEquiv V (L.obj W)).injective ?_⟩
  rw [adj.homEquiv_unit]
  calc
    _ = (adj.homEquiv V (L.obj W) a ≫ inv (adj.unit.app W)) ≫ adj.unit.app W :=
      (adj.unit.naturality _).symm
    _ = _ := by simp

/-- **The direct image of the punctured-spectrum member of an invertible triple is a prepared
extension of the triple.** -/
private theorem exists_preparedExtension_pushforward (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    [IsLocalRing (A ⧸ Ideal.span {f})] (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    ∃ P : PreparedExtension A f T,
      P.F' = (Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj T.F := by
  have hd2 : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A :=
    (show (2 : ℕ∞) ≤ 3 by decide).trans hdepth
  let U := Stacks.Divisors.puncturedSpectrum A
  let i := closedImmersion A f
  let j₀ := (puncturedClosedFibre A f).ι
  let k := puncturedClosedFibreRestriction A f
  let G := (Scheme.Modules.pushforward U.ι).obj T.F
  let e : (Scheme.Modules.pullback U.ι).obj G ≅ T.F :=
    asIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).counit.app T.F)
  let c := (Scheme.Modules.pullbackCongr (morphismRestrict_ι i U).symm).hom.app G
  let a : (Scheme.Modules.pullback j₀).obj ((Scheme.Modules.pullback i).obj G) ⟶
      (Scheme.Modules.pullback j₀).obj T.F₀ :=
    (Scheme.Modules.pullbackComp j₀ i).hom.app G ≫ c ≫
      (Scheme.Modules.pullbackComp k U.ι).inv.app G ≫
        (Scheme.Modules.pullback k).map e.hom ≫ T.alpha.hom
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction j₀).unit.app T.F₀) :=
    isIso_unit_puncturedClosedFibre A f hf hreg T.F₀ hdepth
  obtain ⟨a₀, ha₀⟩ := exists_map_eq_of_isIso_unit
    (Scheme.Modules.pullbackPushforwardAdjunction j₀) a
  refine ⟨⟨G, (isCoherent_isReflexive_pushforward_puncturedSpectrum A T.F hd2).1, ?_, e, a₀, ?_⟩,
    rfl⟩
  · intro V
    show IsSMulRegular Γ(T.F, U.ι ⁻¹ᵁ V)
      (U.ι.app V ((baseScheme A).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    have heq : U.ι.app V ((baseScheme A).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)) = scalarOnOpen A f (U.ι ⁻¹ᵁ V) :=
      ConcreteCategory.congr_hom (U.ι.naturality (homOfLE (le_top : V ≤ ⊤)).op)
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)
    rw [heq]
    exact T.torsionFree (U.ι ⁻¹ᵁ V)
  · show c ≫ (Scheme.Modules.pullbackComp k U.ι).inv.app G ≫
        (Scheme.Modules.pullback k).map e.hom ≫ T.alpha.hom =
      (Scheme.Modules.pullbackComp j₀ i).inv.app G ≫ (Scheme.Modules.pullback j₀).map a₀
    rw [ha₀]
    simp [a]

/-! ### Restriction of global sections along the closed immersion and to the punctured fibre -/

open scoped ChangeOfRings in
private theorem one_tmul_surjective {R S : Type u} [CommRing R] [CommRing S]
    (q : R →+* S) (hq : Function.Surjective q) (M : ModuleCat.{u} R) :
    Function.Surjective (fun m : M => (1 : S) ⊗ₜ[R, q] m) := by
  let := q.toAlgebra
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul s m =>
    obtain ⟨r, rfl⟩ := hq s
    refine ⟨r • m, ?_⟩
    dsimp only
    rw [← TensorProduct.smul_tmul]
    simp only [Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact ⟨m + n, TensorProduct.tmul_add _ _ _⟩

/-- **Restriction of global sections along a closed immersion of affine schemes is surjective**
for a quasi-coherent module: on the module of global sections it is `m ↦ 1 ⊗ m`. -/
private theorem surjective_pullbackGlobalSections_specMap (R S : CommRingCat.{u}) (q : R ⟶ S)
    (hq : Function.Surjective q.hom) (F : (Spec R).Modules) [F.IsQuasicoherent] :
    Function.Surjective (pullbackGlobalSections (Spec.map q) F) := by
  let M := (moduleSpecΓFunctor (R := R)).obj F
  let e := asIso F.fromTildeΓ
  let c := (AlgebraicGeometry.pullbackTildeIso R S q).app M
  have htilde : Function.Surjective (pullbackGlobalSections (Spec.map q) (tilde M)) := by
    intro s
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso (tilde.isoTop
      ((ModuleCat.extendScalars q.hom).obj M)).hom).surjective (c.hom.app ⊤ s)
    obtain ⟨m, rfl⟩ := one_tmul_surjective q.hom hq M z
    refine ⟨tilde.toOpen M ⊤ m, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (c.hom.app ⊤)).injective
    show c.hom.app ⊤ _ = c.hom.app ⊤ s
    refine (congrArg (fun y => c.hom.app ⊤ y)
      (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit (Spec.map q) (tilde M)
        (tilde.toOpen M ⊤ m))).trans ?_
    exact (AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen R S q M m).trans hz
  intro s
  obtain ⟨s', hs'⟩ := (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback (Spec.map q)).mapIso e).hom.app ⊤)).surjective s
  obtain ⟨m, rfl⟩ := htilde s'
  exact ⟨e.hom.app ⊤ m,
    (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
      (Spec.map q) e.hom m).trans hs'⟩

/-- The quotient of a local ring by a principal ideal generated by an element of the maximal ideal
is local. -/
private theorem isLocalRing_quotient_span_singleton (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ maximalIdeal A) : IsLocalRing (A ⧸ Ideal.span {f}) :=
  have hI : Ideal.span {f} ≠ (⊤ : Ideal A) := fun h =>
    (maximalIdeal.isMaximal A).ne_top
      (top_unique (h ▸ Ideal.span_le.mpr (by simpa using hf)))
  have : Nontrivial (A ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective

/-- Restriction of global sections along the closed immersion of the closed fibre is surjective
for a quasi-coherent module. -/
private theorem surjective_pullbackGlobalSections_closedImmersion (A : Type u) [CommRing A]
    (f : A) (F : (baseScheme A).Modules) [F.IsQuasicoherent] :
    Function.Surjective (pullbackGlobalSections (closedImmersion A f) F) :=
  surjective_pullbackGlobalSections_specMap (CommRingCat.of A)
    (CommRingCat.of (A ⧸ Ideal.span {f}))
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) Ideal.Quotient.mk_surjective F

/-- The image of `a : A` in the global sections of the closed fibre `Spec (A ⧸ (f))` is the
pullback along the closed immersion of the global section of `Spec A` given by `a`. -/
theorem closedFibreScalars_eq (A : Type u) [CommRing A] (f : A) (a : A) :
    (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ Ideal.span {f}))).inv
        (Ideal.Quotient.mk (Ideal.span {f}) a) =
      (closedImmersion A f).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) :=
  congrArg (fun h => h a)
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))))

/-- **Restriction of global sections from the closed fibre to the punctured closed fibre**, as a
map of `A`-modules. -/
private noncomputable def closedFibreRestriction (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (F₀ : (closedFibre A f).Modules) :
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀)
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
        ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).obj F₀)) →ₗ[A]
      Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀, ⊤) :=
  letI := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀)
  { toFun := pullbackGlobalSections (puncturedClosedFibre A f).ι F₀
    map_add' := map_add _
    map_smul' := by
      intro a s
      refine (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul
        (puncturedClosedFibre A f).ι F₀ _ s).trans ?_
      exact congrArg (fun r => r • pullbackGlobalSections (puncturedClosedFibre A f).ι F₀ s)
        (congrArg (puncturedClosedFibre A f).ι.appTop.hom (closedFibreScalars_eq A f a)) }

private theorem closedFibreRestriction_apply (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (F₀ : (closedFibre A f).Modules) (s : Γ(F₀, ⊤)) :
    closedFibreRestriction A f F₀ s =
      pullbackGlobalSections (puncturedClosedFibre A f).ι F₀ s :=
  rfl

/-- **The two routes around the square commute on global sections.** Restricting a section of a
prepared extension to the punctured spectrum and then to the punctured closed fibre through the
triple's identification is restricting it to the closed fibre and then to the punctured closed
fibre. -/
private theorem preparedExtension_globalSections_comm (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (T : CoherentTriple A f) (P : PreparedExtension A f T) (s : Γ(P.F', ⊤)) :
    T.alpha.hom.app ⊤ (pullbackGlobalSections (puncturedClosedFibreRestriction A f) T.F
        (P.alpha'.hom.app ⊤ (pullbackGlobalSections
          (Stacks.Divisors.puncturedSpectrum A).ι P.F' s))) =
      pullbackGlobalSections (puncturedClosedFibre A f).ι T.F₀
        (P.alpha₀'.app ⊤ (pullbackGlobalSections (closedImmersion A f) P.F' s)) := by
  have h := congrArg (fun a => a.app ⊤
    (pullbackGlobalSections ((puncturedClosedFibre A f).ι ≫ closedImmersion A f) P.F' s))
    P.compatible
  simp only [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply] at h
  rwa [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr,
    pullbackGlobalSections_comp_inv, pullbackGlobalSections_comp_inv,
    ← Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality,
    ← Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality] at h

/-! ### Injectivity of the closed-fibre map -/

/-- **Global sections on the closed fibre are the global sections on `Spec A` modulo `f`.** -/
noncomputable def closedFibreSectionsEquivQuotSMulTop (A : Type u) [CommRing A]
    [IsLocalRing A] (f : A) (F : (baseScheme A).Modules) [F.IsQuasicoherent] :
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
        ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).obj
          ((Scheme.Modules.pullback (closedImmersion A f)).obj F))) ≃ₗ[A]
      QuotSMulTop f ((moduleSpecΓFunctor (R := .of A)).obj F) :=
  let q : CommRingCat.of A ⟶ .of (A ⧸ Ideal.span {f}) :=
    CommRingCat.ofHom (Ideal.Quotient.mk _)
  let M := (moduleSpecΓFunctor (R := .of A)).obj F
  (((ModuleCat.restrictScalars q.hom).mapIso
    ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).mapIso
        ((Scheme.Modules.pullback (closedImmersion A f)).mapIso
            (asIso F.fromTildeΓ).symm ≪≫
          (AlgebraicGeometry.pullbackTildeIso (.of A) (.of (A ⧸ Ideal.span {f})) q).app M) ≪≫
      (tilde.isoTop ((ModuleCat.extendScalars q.hom).obj M)).symm)).toLinearEquiv).trans
    (QuotSMulTop.equivQuotTensor f M).symm

/-- A module of positive depth along an ideal admits a regular element of that ideal. -/
private theorem exists_regular_of_depth_ne_zero (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : Module.depth R I M ≠ 0) : ∃ r ∈ I, IsSMulRegular M r := by
  by_contra hc
  refine h (le_zero_iff.mp ?_)
  rw [Module.depth_eq_iSup_isWeaklyRegular_length]
  refine iSup₂_le fun rs hrs => ?_
  rcases rs with _ | ⟨r, rs⟩
  · simp
  · exact (hc ⟨r, hrs.1 r (List.mem_cons_self ..),
      ((RingTheory.Sequence.isWeaklyRegular_cons_iff M r rs).mp hrs.2).1⟩).elim

/-- A finite-length module on which an element of the maximal ideal acts regularly vanishes. -/
private theorem subsingleton_of_finiteLength_of_isSMulRegular {A M : Type*} [CommRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) {r : A}
    (hr : r ∈ maximalIdeal A) (hreg : IsSMulRegular M r) : Subsingleton M := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  have hs := IsArtinian.surjective_of_injective_endomorphism (LinearMap.lsmul A M r) hreg
  have ht : (⊤ : Submodule A M) = r • ⊤ :=
    le_antisymm (fun x _ => ⟨(hs x).choose, trivial, (hs x).choose_spec⟩) le_top
  have hbot := Submodule.eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator
    (show (⊤ : Submodule A M).FG from IsNoetherian.noetherian _) ht
    (show r ∈ (⊤ : Submodule A M).annihilator.jacobson from
      (Ideal.jacobson_mono bot_le)
        (by simpa only [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] using hr))
  exact ⟨fun x y => (show x = 0 from hbot.le trivial).trans
    (show y = 0 from hbot.le trivial).symm⟩

/-- **A map of modules with finite-length kernel out of a module of positive depth is
injective.** -/
private theorem injective_of_finiteLength_kernel_of_depth_pos {A : Type u} [CommRing A]
    [IsLocalRing A] {M N : ModuleCat.{u} A} [Module.Finite A M] (g : M ⟶ N)
    (hker : IsFiniteLength A (kernel g).carrier)
    (hd : 0 < Module.depth A (maximalIdeal A) M) : Function.Injective g := by
  obtain ⟨r, hr, hreg⟩ := exists_regular_of_depth_ne_zero A (maximalIdeal A) M hd.ne'
  have hi := (ModuleCat.mono_iff_injective (kernel.ι g)).mp inferInstance
  have hregK : IsSMulRegular (kernel g).carrier r := fun x y hxy =>
    hi (hreg (by simpa only [← map_smul] using congrArg (kernel.ι g) hxy))
  exact (ModuleCat.mono_iff_injective g).mp (Preadditive.mono_of_isZero_kernel g
    (ModuleCat.isZero_iff_subsingleton.mpr
      (subsingleton_of_finiteLength_of_isSMulRegular hker hr hregK)))

/-- **The closed-fibre map of a prepared extension whose global sections have depth at least two
is injective.** Dropping the regular element `f` leaves depth at least one, and the kernel has
finite length, so the kernel vanishes. -/
theorem injective_closedFibreMap_of_two_le_depth (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A)
    (T : CoherentTriple A f) (P : PreparedExtension A f T)
    (hfin : Module.Finite A ((moduleSpecΓFunctor (R := .of A)).obj P.F'))
    (hd : 2 ≤ Module.depth A (maximalIdeal A)
      ((moduleSpecΓFunctor (R := .of A)).obj P.F')) :
    Function.Injective P.closedFibreMap := by
  have : P.F'.IsCoherent := P.coherent
  have : P.F'.IsQuasicoherent := isQuasicoherent_of_isCoherent P.F'
  have hr : IsSMulRegular Γ(P.F', ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f) := by
    simpa using P.regular ⊤
  have hdq : 0 < Module.depth A (maximalIdeal A)
      (QuotSMulTop f ((moduleSpecΓFunctor (R := .of A)).obj P.F')) := by
    have h := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
      (maximalIdeal A) ((moduleSpecΓFunctor (R := .of A)).obj P.F')).1 f hf hr
    by_contra hn
    rw [le_antisymm (not_lt.mp hn) bot_le] at h
    rw [← h] at hd
    norm_num at hd
  let E := closedFibreSectionsEquivQuotSMulTop A f P.F'
  have : Module.Finite A ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
      ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).obj
        ((Scheme.Modules.pullback (closedImmersion A f)).obj P.F'))) :=
    Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective
  exact injective_of_finiteLength_kernel_of_depth_pos P.closedFibreMap
    (kernel_finiteLength A f T P)
    (hdq.trans_eq (Module.depth_eq_depth_of_linearEquiv (maximalIdeal A) E).symm)

/-! ### Comparing the two cokernels -/

/-- The data shared by the two comparisons below: for a prepared extension which is the direct
image of the triple's punctured-spectrum member, restriction of global sections to the punctured
spectrum is bijective, restriction along the closed immersion is surjective, and the image of the
closed-fibre map corresponds to the image of the canonical map on global sections. -/
private theorem range_closedFibreMap_map_eq (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F]
    (hdepth : 2 ≤ Module.depth A (maximalIdeal A) A) (P : PreparedExtension A f T)
    (hP : P.F' = (Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj T.F)
    (hρ : Function.Bijective (closedFibreRestriction A f T.F₀)) :
    letI := puncturedSectionsModule A T.F
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
    (LinearMap.range P.closedFibreMap.hom).map
        (LinearEquiv.ofBijective (closedFibreRestriction A f T.F₀) hρ).toLinearMap =
      LinearMap.range (globalSectionsMap A f T) := by
  let := puncturedSectionsModule A T.F
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  have : P.F'.IsCoherent := P.coherent
  have : P.F'.IsQuasicoherent := isQuasicoherent_of_isCoherent P.F'
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.app P.F') :=
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.isIso_app_iff_of_iso
        (eqToIso hP)).mpr (isIso_unit_pushforward_puncturedSpectrum A T.F hdepth)
  have hα : Function.Surjective (P.alpha'.hom.app ⊤) := fun y =>
    ⟨P.alpha'.inv.app ⊤ y, AlgebraicGeometry.SectionsEqualizer.moduleIso_hom_inv_app P.alpha' y⟩
  have hu : Function.Surjective (fun s : Γ(P.F', ⊤) => P.alpha'.hom.app ⊤
      (pullbackGlobalSections (Stacks.Divisors.puncturedSpectrum A).ι P.F' s)) :=
    hα.comp (bijective_pullbackGlobalSections_of_isIso_unit
      (Stacks.Divisors.puncturedSpectrum A).ι P.F').surjective
  have hc := surjective_pullbackGlobalSections_closedImmersion A f P.F'
  rw [← LinearMap.range_comp]
  ext x
  simp only [LinearMap.mem_range, LinearMap.comp_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨s₀, rfl⟩
    obtain ⟨s, rfl⟩ := hc s₀
    exact ⟨P.alpha'.hom.app ⊤
      (pullbackGlobalSections (Stacks.Divisors.puncturedSpectrum A).ι P.F' s),
      (globalSectionsMap_apply A f T _).trans
        (preparedExtension_globalSections_comm A f T P s)⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := hu t
    exact ⟨pullbackGlobalSections (closedImmersion A f) P.F' s,
      ((globalSectionsMap_apply A f T _).trans
        (preparedExtension_globalSections_comm A f T P s)).symm⟩

/-- **The cokernel of the closed-fibre map of the direct-image prepared extension is the cokernel
of the canonical map on global sections.** -/
private theorem cokernel_length_eq_of_pushforward (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F]
    (hdepth : 2 ≤ Module.depth A (maximalIdeal A) A) (P : PreparedExtension A f T)
    (hP : P.F' = (Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj T.F)
    (hρ : Function.Bijective (closedFibreRestriction A f T.F₀)) :
    letI := puncturedSectionsModule A T.F
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
    Module.length A (cokernel P.closedFibreMap).carrier =
      Module.length A
        (Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀, ⊤) ⧸
          LinearMap.range (globalSectionsMap A f T)) := by
  let := puncturedSectionsModule A T.F
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  exact ((ModuleCat.cokernelIsoRangeQuotient P.closedFibreMap).toLinearEquiv.trans
    (Submodule.Quotient.equiv _ _ (LinearEquiv.ofBijective _ hρ)
      (range_closedFibreMap_map_eq A f T hdepth P hP hρ))).length_eq

/-- **The canonical map on global sections is surjective exactly when the closed-fibre map of the
direct-image prepared extension is.** -/
private theorem surjective_globalSectionsMap_iff_closedFibreMap (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F]
    (hdepth : 2 ≤ Module.depth A (maximalIdeal A) A) (P : PreparedExtension A f T)
    (hP : P.F' = (Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj T.F)
    (hρ : Function.Bijective (closedFibreRestriction A f T.F₀)) :
    letI := puncturedSectionsModule A T.F
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
    Function.Surjective (globalSectionsMap A f T) ↔
      Function.Surjective P.closedFibreMap := by
  let := puncturedSectionsModule A T.F
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  have hmap := range_closedFibreMap_map_eq A f T hdepth P hP hρ
  let ρ := LinearEquiv.ofBijective (closedFibreRestriction A f T.F₀) hρ
  constructor
  · intro hs
    rw [← LinearMap.range_eq_top] at hs ⊢
    exact (Submodule.map_eq_top_iff (e := ρ)).mp (hmap.trans hs)
  · intro hs
    rw [← LinearMap.range_eq_top] at hs ⊢
    rw [← hmap, hs, Submodule.map_top, LinearEquiv.range]

/-! ### Finiteness of the cokernel -/

/-- **The cokernel of the canonical map on global sections has finite length.** The restriction
map from the closed fibre to the punctured closed fibre is surjective, by Hartogs extension on
`A / fA`, and restriction along the closed immersion is surjective on global sections, so the
cokernel is a quotient of the cokernel of the closed-fibre map of any prepared extension of the
triple, which has finite length. -/
@[stacks 0F28 "finite length of the cokernel"]
theorem finiteLength_cokernel_globalSectionsMap (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    letI := puncturedSectionsModule A T.F
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
    IsFiniteLength A
      (Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀, ⊤) ⧸
        LinearMap.range (globalSectionsMap A f T)) := by
  classical
  have := isLocalRing_quotient_span_singleton A f hf
  let := puncturedSectionsModule A T.F
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  have := isIso_unit_puncturedClosedFibre A f hf hreg T.F₀ hdepth
  have hρ : Function.Surjective (closedFibreRestriction A f T.F₀) :=
    (bijective_pullbackGlobalSections_of_isIso_unit
      (puncturedClosedFibre A f).ι T.F₀).surjective
  obtain ⟨P⟩ := nonempty_preparedExtension A f hf hreg T
  have : P.F'.IsCoherent := P.coherent
  have : P.F'.IsQuasicoherent := isQuasicoherent_of_isCoherent P.F'
  let π := (LinearMap.range (globalSectionsMap A f T)).mkQ
  let ψ := ModuleCat.ofHom (π.comp (closedFibreRestriction A f T.F₀))
  have hψ : P.closedFibreMap ≫ ψ = 0 := by
    ext x
    obtain ⟨s, rfl⟩ := surjective_pullbackGlobalSections_closedImmersion A f P.F' x
    show π (closedFibreRestriction A f T.F₀ (P.alpha₀'.app ⊤
      (pullbackGlobalSections (closedImmersion A f) P.F' s))) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨P.alpha'.hom.app ⊤
      (pullbackGlobalSections (Stacks.Divisors.puncturedSpectrum A).ι P.F' s),
      (globalSectionsMap_apply A f T _).trans (preparedExtension_globalSections_comm A f T P s)⟩
  have hδ : Function.Surjective (cokernel.desc P.closedFibreMap ψ hψ) := by
    intro x
    obtain ⟨s, hs⟩ :=
      (LinearMap.range (globalSectionsMap A f T)).mkQ_surjective.comp hρ x
    exact ⟨cokernel.π P.closedFibreMap s,
      (ConcreteCategory.congr_hom (cokernel.π_desc P.closedFibreMap ψ hψ) s).trans hs⟩
  exact IsFiniteLength.of_surjective (cokernel_finiteLength A f T P) hδ

/-! ### Comparison with the Euler characteristic -/

/-- **The direct image of the punctured-spectrum member computes the cokernel of the canonical map
on global sections.** For an invertible coherent triple over a Noetherian local ring of depth at
least three there is a prepared extension -- the direct image of the triple's punctured-spectrum
member -- whose closed-fibre map has a cokernel of the same length as the cokernel of the
canonical map on global sections, and which is surjective exactly when that map is.

Together with `Stacks.Algebraization.PreparedExtension.eulerCharacteristic_eq`, which says that
the Euler characteristic does not depend on the prepared extension, and with
`Stacks.Algebraization.injective_closedFibreMap_of_two_le_depth` applied to this extension, this
is the comparison on which the Euler-characteristic formula rests. -/
theorem exists_preparedExtension_length_cokernel_eq (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    letI := puncturedSectionsModule A T.F
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
    ∃ P : PreparedExtension A f T,
      P.F' = (Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj T.F ∧
      Module.length A (cokernel P.closedFibreMap).carrier =
        Module.length A
          (Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀, ⊤) ⧸
            LinearMap.range (globalSectionsMap A f T)) ∧
      (Function.Surjective (globalSectionsMap A f T) ↔
        Function.Surjective P.closedFibreMap) := by
  have := isLocalRing_quotient_span_singleton A f hf
  let := puncturedSectionsModule A T.F
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  have hd2 : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A :=
    (show (2 : ℕ∞) ≤ 3 by decide).trans hdepth
  have := isIso_unit_puncturedClosedFibre A f hf hreg T.F₀ hdepth
  have hρ : Function.Bijective (closedFibreRestriction A f T.F₀) :=
    bijective_pullbackGlobalSections_of_isIso_unit (puncturedClosedFibre A f).ι T.F₀
  obtain ⟨P, hP⟩ := exists_preparedExtension_pushforward A f hf hreg T hdepth
  exact ⟨P, hP, cokernel_length_eq_of_pushforward A f T hd2 P hP hρ,
    surjective_globalSectionsMap_iff_closedFibreMap A f T hd2 P hP hρ⟩

end Stacks.Algebraization

end
