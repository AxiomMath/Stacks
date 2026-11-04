module

public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Modules.AffineOpenAssociatedSheafDerivedPullback
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Perfect.Morphism
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineQuasiIso
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksFrontier.Deformation.SquareZero.Obstruction
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.CompleteIntersection.NaiveCotangentPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.Restriction
public import StacksFrontier.Topology.Sheaves.Cohomology.TransportAlongAnIsomorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
-- `StacksDraft.TorAmplitude.HasTorAmplitudeCanonical` is the Tor amplitude of Stacks 0652 at the
-- canonical derived tensor product of Stacks 0BYI, but it is not exposed, so the ring-level
-- Stacks 0FJV, whose statement spells that tensor product out, does not see the two as the same.
import all StacksFrontier.Homology.TorAmplitude.CanonicalCertificate

/-!
# The naive cotangent complex of a local complete intersection morphism

For a flat morphism of finite presentation, the four conditions of Stacks 0FK3 are equivalent:
being a local complete intersection morphism, being syntomic, Tor amplitude of `NL_{X/Y}` in
`[-1, 0]`, and perfectness of `NL_{X/Y}` together with that Tor amplitude. For an arbitrary
morphism of schemes, `NL_{X/Y}` is perfect with Tor amplitude in `[-1, 0]` as soon as the
morphism is a local complete intersection morphism.

## Main results

* `AlgebraicGeometry.naiveCotangentComplex_tfae`: **Stacks 0FK3**, the four equivalent
  conditions.
* `AlgebraicGeometry.syntomic_of_hasTorAmplitude_naiveCotangentComplex` and
  `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_hasTorAmplitude_naiveCotangentComplex`:
  **Stacks 0FK3**, the implications (3) ⇒ (2) and (3) ⇒ (1).
* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_iff_syntomic`: **Stacks 0FK3**, the
  equivalence of (1) and (2).
* `AlgebraicGeometry.hasTorAmplitude_naiveCotangentComplex_of_isPerfect_of_hasTorAmplitude`:
  **Stacks 0FK3**, the implication (4) ⇒ (3), and **Stacks 0FK2**, the implication (3) ⇒ (2).
* `AlgebraicGeometry.isPerfect_and_hasTorAmplitude_naiveCotangentComplex`: **Stacks 0FV6**, for a
  local complete intersection morphism, `NL_{X/Y}` is perfect with Tor amplitude in `[-1, 0]`.
* `AlgebraicGeometry.hasTorAmplitude_naiveCotangentComplex_of_flat`,
  `AlgebraicGeometry.isPerfect_and_hasTorAmplitude_naiveCotangentComplex_of_flat`: **Stacks
  0FK3**, the implications (1) ⇒ (3) and (1) ⇒ (4).
* `AlgebraicGeometry.hasTorAmplitude_naiveCotangentComplex_of_perfect`,
  `AlgebraicGeometry.isPerfect_and_hasTorAmplitude_naiveCotangentComplex_of_perfect`: **Stacks
  0FK2**, the implications (1) ⇒ (2) and (1) ⇒ (3).

## Implementation notes

`NL_{X/Y}` is `AlgebraicGeometry.Scheme.naiveCotangentComplex`, Stacks 0D0H, a two-term complex
of sheaves of `𝒪_X`-modules in degrees `-1` and `0`; the conditions on it are read at its class
in `D(𝒪_X)`. Tor amplitude is
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, Stacks 08CG, taken against the canonical
derived tensor product of a ringed space, and perfectness is
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, Stacks 08CM. Both are stated at the underlying
ringed space of `X`; the derived category is the standard one, as it is for Stacks 08E9 and
Stacks 08EB.

Flatness of a local complete intersection morphism is not what makes it syntomic by itself: the
equivalence of (1) and (2) is Stacks 069K, and finite presentation is not used for it. It is
carried in the statement because it is a standing hypothesis of Stacks 0FK3.

The implication (4) ⇒ (3) is stated for an arbitrary morphism of schemes, with neither tag's
standing hypotheses, since it uses none of them; in that generality it is the implication
(4) ⇒ (3) of Stacks 0FK3 and the implication (3) ⇒ (2) of Stacks 0FK2 at once.

Both predicates are local on `X`, so the two conditions are checked on an affine open `V` of `X`
lying over an affine open `U` of `Y`. There `NL_{X/Y}|_V` is the complex of associated sheaves of
`NL_{Γ(X, V)/Γ(Y, U)}`, by Stacks 0D0I, and that complex is the derived pullback along
`V ≅ Spec Γ(X, V)` of the derived sheafification of `NL_{Γ(X, V)/Γ(Y, U)}` on `Spec Γ(X, V)`.
Both conditions therefore descend to conditions on `NL_{Γ(X, V)/Γ(Y, U)}` in `D(Γ(X, V))`, by
Stacks 08E9 and Stacks 08EB, and those hold by Stacks 0FV0 because `Γ(Y, U) → Γ(X, V)` is a local
complete intersection homomorphism.

The ring-level statement of Stacks 0FV0 reads Tor amplitude off an arbitrary certified derived
tensor product; it is instantiated at the canonical one of Stacks 0BYI, which is available
because `Γ(Y, U)` and `Γ(X, V)` lie in the same universe as their modules.

The converse implication (3) ⇒ (2) runs the same affine-local chain backwards, every step of it
being an equivalence: Tor amplitude restricts to `V` through the bounded flat representative of
Stacks 08CI, crosses `V ≅ Spec Γ(X, V)` along derived pullback, and descends through derived
sheafification by Stacks 08E9. What it descends to is
Tor amplitude in `[-1, 0]` of `NL_{Γ(X, V)/Γ(Y, U)}`, and `Γ(Y, U) → Γ(X, V)` is flat of finite
presentation, so the ring-level equivalence Stacks 0FJV makes it syntomic. Syntomicity of a
morphism of schemes is exactly this condition on sections at some affine pair around each point
of the source, so no gluing is needed, and (3) ⇒ (1) then follows from the equivalence of (1)
and (2). Quasi-compactness and quasi-separatedness, the two parts of finite presentation beyond
local finite presentation, are never used.

## References

* [Stacks Project, Lemma 37.62.15 (0FV6)](https://stacks.math.columbia.edu/tag/0FV6)
* [Stacks Project, Lemma 37.62.17 (0FK3)](https://stacks.math.columbia.edu/tag/0FK3)
* [Stacks Project, Lemma 37.62.16 (0FK2)](https://stacks.math.columbia.edu/tag/0FK2)
* [Stacks Project, Lemma 37.62.8 (069K)](https://stacks.math.columbia.edu/tag/069K)
* [Stacks Project, Lemma 15.88.1 (0FV0)](https://stacks.math.columbia.edu/tag/0FV0)
* [Stacks Project, Lemma 37.13.2 (07DB)](https://stacks.math.columbia.edu/tag/07DB)
* [Stacks Project, Tag 0D0H](https://stacks.math.columbia.edu/tag/0D0H)
* [Stacks Project, Lemma 36.3.5 (0D0I)](https://stacks.math.columbia.edu/tag/0D0I)
* [Stacks Project, Definition 20.48.1 (08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Definition 20.49.1 (08CM)](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Lemma 36.10.4 (08E9)](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Lemma 36.10.7 (08EB)](https://stacks.math.columbia.edu/tag/08EB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0FK3, the equivalence of (1) and (2).** A flat morphism of finite presentation is a
local complete intersection morphism exactly when it is syntomic.

Finite presentation is a standing hypothesis of the source and is not used: the equivalence holds
for any flat morphism, by Stacks 069K. -/
@[stacks 0FK3 "(1) ⇔ (2): a flat morphism of finite presentation is a local complete \
  intersection morphism iff it is syntomic"]
theorem isLocalCompleteIntersectionMorphism_iff_syntomic {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] (_hfp : FinitePresentation f) :
    IsLocalCompleteIntersectionMorphism f ↔ Syntomic f :=
  ⟨fun hlci => syntomic_of_flat_of_isLocalCompleteIntersectionMorphism ‹Flat f› hlci,
    isLocalCompleteIntersectionMorphism_of_syntomic⟩

/-- **Stacks 0FK3, the implication (4) ⇒ (3).** If `NL_{X/Y}` is perfect with Tor amplitude in
`[-1, 0]`, then it has Tor amplitude in `[-1, 0]`.

The implication is a projection, as it is in the source. The declaration's purpose is to pin
conditions (3) and (4) of the tag to `Stacks.Cohomology.TorAmplitude.HasTorAmplitude` of Stacks
08CG, taken against the canonical derived tensor product of Stacks 06YU, and to
`Stacks.Cohomology.PerfectComplexes.IsPerfect` of Stacks 08CM; the tree carries several further
spellings of each. The tag's standing hypotheses are not needed, so the statement is made for an
arbitrary morphism of schemes. -/
@[stacks 0FK3 "(4) ⇒ (3), which is a projection: NL_{X/Y} perfect with tor-amplitude in [-1,0] \
  has tor-amplitude in [-1,0]. Fixes which library predicates conditions (3) and (4) are read at"]
theorem hasTorAmplitude_naiveCotangentComplex_of_isPerfect_of_hasTorAmplitude
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0 :=
  hf.2

/-! ### The naive cotangent complex of a local complete intersection morphism -/

namespace NaiveCotangentLocalCompleteIntersection

open CategoryTheory.Limits TopologicalSpace
open Stacks.AssociatedSheaf (associatedSheafFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.NaiveCotangentAffineIso (nlSelfModD)

/-! #### Two-term complexes under an additive functor -/

/-- **An additive functor carries a two-term complex to the two-term complex on its image.**
Away from the two degrees carrying the map, the image complex has the image of a zero object
rather than a zero object, so the comparison is an isomorphism and not an equality. -/
def mapDouble {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    (G : C ⥤ D) [G.Additive] {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι}
    (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) {X₀ X₁ : C} (d : X₀ ⟶ X₁) :
    HomologicalComplex.double (G.map d) hi ≅
      (G.mapHomologicalComplex c).obj (HomologicalComplex.double d hi) :=
  HomologicalComplex.doubleIsoOfIsZero (G.map d) hi hne _
    (G.mapIso (HomologicalComplex.doubleXIso₀ d hi).symm)
    (G.mapIso (HomologicalComplex.doubleXIso₁ d hi hne).symm)
    (by
      dsimp only [Functor.mapIso, Iso.symm_hom, Functor.mapHomologicalComplex_obj_d]
      rw [HomologicalComplex.double_d d hi hne, ← G.map_comp, ← G.map_comp]
      simp)
    (fun j _ => by
      dsimp only [Functor.mapIso, Iso.symm_hom, Functor.mapHomologicalComplex_obj_d]
      rw [HomologicalComplex.double_d_eq_zero₀ d hi i₁ j hne.symm, G.map_zero, comp_zero])
    (fun j h₀ h₁ => Functor.map_isZero G (HomologicalComplex.isZero_double_X d hi j h₀ h₁))

/-! #### Derived sheafification on `Spec R` in the two vocabularies -/

/-- **The two sheafifications of a complex of `R`-modules on `Spec R` agree.** The affine
construction `M ↦ M̃` applied degreewise and tensor sheafification along
`R → Γ(Spec R, 𝒪)` applied degreewise are identified by Stacks 01I7 in each degree. -/
def tildeAssociatedComplexIso (R : CommRingCat.{u})
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      ((associatedSheafFunctor.{u, u} (Spec R).toRingedSpace
        (Scheme.ΓSpecIso R).inv.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (tilde.associatedSheafNatIso R).app (K.X i))
    (fun i j _ => ((tilde.associatedSheafNatIso R).hom.naturality (K.d i j)).symm)

/-- **Tensor sheafification of a complex on `Spec R` computes its derived sheafification.** -/
def associatedComplexIsoTilde (R : CommRingCat.{u})
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj (((associatedSheafFunctor.{u, u} (Spec R).toRingedSpace
        (Scheme.ΓSpecIso R).inv.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      (tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj K) :=
  DerivedCategory.Q.mapIso (tildeAssociatedComplexIso R K).symm ≪≫
    ((tilde.functor R).mapDerivedCategoryFactors.app K).symm

/-! #### The local complete intersection condition on sections -/

/-- Equal pairs of opens induce the same local complete intersection condition on sections. -/
theorem isLocalCompleteIntersection_appLE_congr {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U U' : Y.Opens} {V V' : X.Opens} (hU : U' = U) (hV : V' = V)
    {e : V ≤ f ⁻¹ᵁ U} {e' : V' ≤ f ⁻¹ᵁ U'}
    (h : RingHom.IsLocalCompleteIntersection (f.appLE U' V' e').hom) :
    RingHom.IsLocalCompleteIntersection (f.appLE U V e).hom := by
  subst hU
  subst hV
  exact h

/-- The local complete intersection condition on the global sections of a restriction `f|_V^U` is
the same condition on the sections of `f` over the pair `U`, `V`. -/
theorem isLocalCompleteIntersection_appLE_of_appTop {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    (h : RingHom.IsLocalCompleteIntersection ((f.resLE U V hVU).appTop.hom)) :
    RingHom.IsLocalCompleteIntersection ((f.appLE U V hVU).hom) := by
  rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app] at h
  have h1 : RingHom.IsLocalCompleteIntersection
      ((f.resLE U V hVU).appLE ⊤ ⊤ le_top).hom :=
    isLocalCompleteIntersection_appLE_congr _ rfl (by simp) h
  rw [Scheme.Hom.resLE_appLE f hVU ⊤ ⊤ le_top] at h1
  exact isLocalCompleteIntersection_appLE_congr f U.ι_image_top V.ι_image_top h1

/-- **A local complete intersection morphism is one on sections over affine opens.** -/
theorem isLocalCompleteIntersection_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsLocalCompleteIntersectionMorphism f) {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) :
    RingHom.IsLocalCompleteIntersection ((f.appLE U V hVU).hom) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  exact isLocalCompleteIntersection_appLE_of_appTop f hVU
    ((isLocalCompleteIntersectionMorphism_iff_appTop _).mp
      (_root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_resLE f hf U V hVU))

/-! #### The affine-local computation -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U)

/-- **`NL_{Γ(X, V)/Γ(Y, U)}`** as a two-term complex of `Γ(X, V)`-modules in degrees `-1` and
`0`, the algebra structure being the restriction `f.appLE U V` of `f`. -/
abbrev sectionsNaiveCotangentComplex : CochainComplex (ModuleCat.{u} Γ(X, V)) ℤ :=
  HomologicalComplex.double (nlSelfModD f hVU) (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)

/-- The class of `NL_{Γ(X, V)/Γ(Y, U)}` in `D(Γ(X, V))` is the object of Stacks 0FV0: the two
spellings of the canonical presentation agree, and a two-term complex is the mapping cone of the
same map between complexes concentrated in degree zero. -/
def sectionsNaiveCotangentComplexIso :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    DerivedCategory.Q.obj (sectionsNaiveCotangentComplex f hVU) ≅
      NaiveCotangent.naiveCotangentObject Γ(Y, U) Γ(X, V) :=
  letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  DerivedCategory.Q.mapIso (HomologicalComplex.singleConeDoubleIso (nlSelfModD f hVU))

/-- **Stacks 0FV0 at `Γ(Y, U) → Γ(X, V)`.** If the morphism is a local complete intersection on
sections, then `NL_{Γ(X, V)/Γ(Y, U)}` is a perfect object of `D(Γ(X, V))` with Tor amplitude in
`[-1, 0]`, the latter taken against the canonical derived tensor product. -/
theorem isPerfect_and_hasTorAmplitudeCanonical_naiveCotangentObject
    (h : RingHom.IsLocalCompleteIntersection ((f.appLE U V hVU).hom)) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    StacksDraft.Perfect.IsPerfect (NaiveCotangent.naiveCotangentObject Γ(Y, U) Γ(X, V)) ∧
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical Γ(X, V)
        (NaiveCotangent.naiveCotangentObject Γ(Y, U) Γ(X, V)) (-1) 0 := by
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  let cert := StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring Γ(X, V)
  have hFV0 := NaiveCotangent.naiveCotangentComplex_isPerfect_and_hasTorAmplitude
    (A := Γ(Y, U)) (B := Γ(X, V)) h cert.tensor cert.comparison cert.isLeftDerived
  exact ⟨hFV0.1,
    (StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonicalCertified_iff Γ(X, V) _ _ _).1 hFV0.2⟩

/-- **`NL_{X/Y}|_V` is the derived pullback along `V ≅ Spec Γ(X, V)` of the derived
sheafification of `NL_{Γ(X, V)/Γ(Y, U)}`**, for `V` an affine open of `X` lying over an affine
open `U` of `Y`.

The restriction is `NL_{Γ(X, V)/Γ(Y, U)}`-tilde on `V` by Stacks 0D0I, tensor sheafification on
`V` is the pullback of tensor sheafification on `Spec Γ(X, V)` by Stacks 01BJ, and the latter is
the affine construction `M ↦ M̃` by Stacks 01I7. -/
def naiveCotangentComplexRestrictIso (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace V).obj
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ≅
      (derivedPullback
          (Stacks.Cohomology.TransportAlongIso.ringedSpaceIsoOfSchemeIso hV.isoSpec).hom).obj
        ((tilde.functor Γ(X, V)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj (sectionsNaiveCotangentComplex f hVU))) :=
  haveI : IsIso (DerivedCategory.Q.map (Stacks.NaiveCotangentAffineMap.comparisonMap f hVU)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (Stacks.NaiveCotangentAffineQuasiIso.quasiIso_comparisonMap V f hVU hU hV)
  (AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor X V).app _ ≪≫
    (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategoryFactors.app _ ≪≫
    (asIso (DerivedCategory.Q.map
      (Stacks.NaiveCotangentAffineMap.comparisonMap f hVU))).symm ≪≫
    DerivedCategory.Q.mapIso (mapDouble _ _ (by decide) _) ≪≫
    hV.associatedSheafComplexIsoDerivedPullback.app (sectionsNaiveCotangentComplex f hVU) ≪≫
    (derivedPullback hV.isoSpecRingedSpaceHom).mapIso
      (associatedComplexIsoTilde Γ(X, V) (sectionsNaiveCotangentComplex f hVU))

/-- Tor amplitude of an object of `D(𝒪_X)` is invariant under isomorphism. -/
private theorem hasTorAmplitude_iff_of_iso {Z : RingedSpace.{u, u}}
    [HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u} Z)]
    {E E' : DerivedCategory (StrictlyPerfect.OXMod.{u} Z)} (e : E ≅ E') (a b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude Z E a b ↔
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude Z E' a b :=
  ⟨fun h => Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} h e.symm,
    fun h => Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} h e⟩

/-- Tor amplitude of the restriction of `NL_{X/Y}` to `V` is Tor amplitude in `[-1, 0]` of
`NL_{Γ(X, V)/Γ(Y, U)}` in `D(Γ(X, V))`, taken against the canonical derived tensor product. -/
private theorem hasTorAmplitude_restrict_iff (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude
        (X.toRingedSpace.restrict V.isOpenEmbedding)
        ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace V).obj
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f))) (-1) 0 ↔
      letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical Γ(X, V)
        (NaiveCotangent.naiveCotangentObject Γ(Y, U) Γ(X, V)) (-1) 0 :=
  letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  (hasTorAmplitude_iff_of_iso (naiveCotangentComplexRestrictIso f hVU hU hV) _ _).trans
    ((Stacks.Cohomology.TransportAlongIso.hasTorAmplitude_derivedPullback_scheme_iff
      hV.isoSpec _ (-1) 0).trans
      ((hasTorAmplitude_iff_of_iso ((tilde.functor Γ(X, V)).mapDerivedCategory.mapIso
        (sectionsNaiveCotangentComplexIso f hVU)) _ _).trans
        (AlgebraicGeometry.hasTorAmplitude_tilde_iff (R := Γ(X, V)) _ (-1) 0)))

/-- **The two conditions on an affine open of the source.** If the morphism is a local complete
intersection on sections over `U` and `V`, then the restriction of `NL_{X/Y}` to `V` is perfect
with Tor amplitude in `[-1, 0]`. -/
theorem isPerfect_and_hasTorAmplitude_restrict (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : RingHom.IsLocalCompleteIntersection ((f.appLE U V hVU).hom)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
        (X := X.toRingedSpace.restrict V.isOpenEmbedding)
        ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace V).obj
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f))) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude
        (X.toRingedSpace.restrict V.isOpenEmbedding)
        ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace V).obj
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f))) (-1) 0 := by
  obtain ⟨hperf, hamp⟩ := isPerfect_and_hasTorAmplitudeCanonical_naiveCotangentObject f hVU h
  constructor
  · have h1 := (AlgebraicGeometry.isPerfect_tilde_iff (R := Γ(X, V)) _).2 hperf
    have h2 := Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
      ((tilde.functor Γ(X, V)).mapDerivedCategory.mapIso
        (sectionsNaiveCotangentComplexIso f hVU).symm) h1
    have h3 := (Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_scheme_iff
      hV.isoSpec _).2 h2
    exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
      (naiveCotangentComplexRestrictIso f hVU hU hV).symm h3
  · exact (hasTorAmplitude_restrict_iff f hVU hU hV).2 hamp

/-- **Tor amplitude of `NL_{X/Y}` is read on sections over affine opens.** If `NL_{X/Y}` has Tor
amplitude in `[-1, 0]`, then so does `NL_{Γ(X, V)/Γ(Y, U)}` in `D(Γ(X, V))`, for `V` an affine
open of `X` lying over an affine open `U` of `Y`.

This is the chain of `isPerfect_and_hasTorAmplitude_restrict` run backwards: Tor amplitude
restricts to the open `V` through the bounded flat representative of Stacks 08CI, crosses
`V ≅ Spec Γ(X, V)` along derived pullback, and descends through derived sheafification by
Stacks 08E9, all three steps being equivalences. -/
theorem hasTorAmplitudeCanonical_of_hasTorAmplitude (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical Γ(X, V)
      (NaiveCotangent.naiveCotangentObject Γ(Y, U) Γ(X, V)) (-1) 0 := by
  exact (hasTorAmplitude_restrict_iff f hVU hU hV).1
    (Stacks.Cohomology.TorAmplitude.hasTorAmplitude_restrictModules.{u, u + 1} V _ (-1) 0
      (by norm_num) hamp)

/-- **Stacks 0FJV at `Γ(Y, U) → Γ(X, V)`, the implication from Tor amplitude.** If `f` is flat and
locally of finite presentation and `NL_{X/Y}` has Tor amplitude in `[-1, 0]`, then the morphism is
syntomic on sections over an affine open `V` of `X` lying over an affine open `U` of `Y`. -/
theorem syntomic_appLE_of_hasTorAmplitude [Flat f] [LocallyOfFinitePresentation f]
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    Algebra.Syntomic Γ(Y, U) Γ(X, V) := by
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  have : Module.Flat Γ(Y, U) Γ(X, V) :=
    HasRingHomProperty.appLE (@Flat) f ‹Flat f› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  have : Algebra.FinitePresentation Γ(Y, U) Γ(X, V) :=
    LocallyOfFinitePresentation.finitePresentation_appLE f hU hV hVU
  have h := (NaiveCotangent.hasTorAmplitude_tfae_syntomic Γ(Y, U) Γ(X, V)).out 1 3
  exact h.mp (hasTorAmplitudeCanonical_of_hasTorAmplitude f hVU hU hV hamp)

/-- **Every point of the source of a local complete intersection morphism has an open
neighbourhood on which the restriction of `NL_{X/Y}` is perfect with Tor amplitude in
`[-1, 0]`.** -/
theorem exists_restrict_isPerfect_and_hasTorAmplitude {X Y : Scheme.{u}} (g : X ⟶ Y)
    (hg : IsLocalCompleteIntersectionMorphism g) (x : X) :
    ∃ W : X.Opens, x ∈ W ∧
      (Stacks.Cohomology.PerfectComplexes.IsPerfect
          (X := X.toRingedSpace.restrict W.isOpenEmbedding)
          ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace W).obj
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex g))) ∧
        Stacks.Cohomology.TorAmplitude.HasTorAmplitude
          (X.toRingedSpace.restrict W.isOpenEmbedding)
          ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace W).obj
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex g))) (-1) 0) := by
  obtain ⟨U, W, hxW, hWU, -⟩ := (hg x).1
  exact ⟨W.1, hxW, isPerfect_and_hasTorAmplitude_restrict g hWU U.2 W.2
    (isLocalCompleteIntersection_appLE g hg U.2 W.2 hWU)⟩

/-- **Perfectness of `NL_{X/Y}` for a local complete intersection morphism**, obtained from the
local statement because perfectness is local on the space, by Stacks 08CR. -/
@[sga "6 XIV 2.1"]
theorem isPerfect_naiveCotangentComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsLocalCompleteIntersectionMorphism f) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) := by
  classical
  choose V hxV hloc using exists_restrict_isPerfect_and_hasTorAmplitude f hf
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect
    (X := X.toRingedSpace) (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f))
    (fun x => ⟨V x, hxV x, (hloc x).1⟩)

/-- **Tor amplitude in `[-1, 0]` of `NL_{X/Y}` for a local complete intersection morphism**,
obtained from the local statement because the chosen neighbourhoods cover the source. -/
theorem hasTorAmplitude_naiveCotangentComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsLocalCompleteIntersectionMorphism f) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0 := by
  classical
  choose V hxV hloc using exists_restrict_isPerfect_and_hasTorAmplitude f hf
  refine Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top
    (X := X.toRingedSpace) (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0 V
    ?_ (fun x => (hloc x).2)
  exact top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩

end NaiveCotangentLocalCompleteIntersection

/-- **Stacks 0FV6.** The naive cotangent complex of a local complete intersection morphism is a
perfect object of `D(𝒪_X)` of Tor amplitude in `[-1, 0]`.

Near a point of the source the morphism restricts to a morphism of affine schemes whose map on
sections is a local complete intersection homomorphism, and there `NL_{X/Y}` is the derived
pullback of the derived sheafification of the naive cotangent complex of that homomorphism; both
conditions hold on it by Stacks 0FV0 and descend to the restriction by Stacks 08E9 and Stacks
08EB. Both conditions are local on the source, so they hold on `X`. -/
@[stacks 0FV6 "both halves: NL_{X/Y} of a local complete intersection morphism is perfect and \
has tor-amplitude in [-1,0]", sga "6 VIII 2.4" "more general", sga "6 XIV 2.1"]
theorem isPerfect_and_hasTorAmplitude_naiveCotangentComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsLocalCompleteIntersectionMorphism f) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0 :=
  ⟨NaiveCotangentLocalCompleteIntersection.isPerfect_naiveCotangentComplex f hf,
    NaiveCotangentLocalCompleteIntersection.hasTorAmplitude_naiveCotangentComplex f hf⟩

/-- **Stacks 0FK3, the implication (1) ⇒ (3).** If a flat morphism of finite presentation is a
local complete intersection morphism, then `NL_{X/Y}` has Tor amplitude in `[-1, 0]`.

The two standing hypotheses are not used: Tor amplitude in `[-1, 0]` holds for the naive
cotangent complex of any local complete intersection morphism. -/
@[stacks 0FK3 "(1) ⇒ (3): for a flat morphism of finite presentation which is a local complete \
  intersection morphism, NL_{X/Y} has tor-amplitude in [-1,0]"]
theorem hasTorAmplitude_naiveCotangentComplex_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] (_hfp : FinitePresentation f) (hf : IsLocalCompleteIntersectionMorphism f) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0 :=
  (isPerfect_and_hasTorAmplitude_naiveCotangentComplex f hf).2

/-- **Stacks 0FK3, the implication (1) ⇒ (4).** If a flat morphism of finite presentation is a
local complete intersection morphism, then `NL_{X/Y}` is perfect with Tor amplitude in `[-1, 0]`.

The two standing hypotheses are not used: both conditions hold for the naive cotangent complex
of any local complete intersection morphism. -/
@[stacks 0FK3 "(1) ⇒ (4): for a flat morphism of finite presentation which is a local complete \
  intersection morphism, NL_{X/Y} is perfect with tor-amplitude in [-1,0]"]
theorem isPerfect_and_hasTorAmplitude_naiveCotangentComplex_of_flat {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (_hfp : FinitePresentation f)
    (hf : IsLocalCompleteIntersectionMorphism f) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0 :=
  isPerfect_and_hasTorAmplitude_naiveCotangentComplex f hf

/-- **Stacks 0FK2, the implication (1) ⇒ (2).** If a perfect morphism of locally Noetherian
schemes is a local complete intersection morphism, then `NL_{X/Y}` has Tor amplitude in
`[-1, 0]`.

The three standing hypotheses are not used: Tor amplitude in `[-1, 0]` holds for the naive
cotangent complex of any local complete intersection morphism. -/
@[stacks 0FK2 "(1) ⇒ (2): for a perfect morphism of locally Noetherian schemes which is a local \
  complete intersection morphism, NL_{X/Y} has tor-amplitude in [-1,0]"]
theorem hasTorAmplitude_naiveCotangentComplex_of_perfect {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Perfect f]
    (hf : IsLocalCompleteIntersectionMorphism f) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0 :=
  (isPerfect_and_hasTorAmplitude_naiveCotangentComplex f hf).2

/-- **Stacks 0FK2, the implication (1) ⇒ (3).** If a perfect morphism of locally Noetherian
schemes is a local complete intersection morphism, then `NL_{X/Y}` is perfect with Tor amplitude
in `[-1, 0]`.

The three standing hypotheses are not used: both conditions hold for the naive cotangent complex
of any local complete intersection morphism. -/
@[stacks 0FK2 "(1) ⇒ (3): for a perfect morphism of locally Noetherian schemes which is a local \
  complete intersection morphism, NL_{X/Y} is perfect with tor-amplitude in [-1,0]",
  sga "6 VIII 2.4" "partial",
  sga "6 XIV 2.1" "special case"]
theorem isPerfect_and_hasTorAmplitude_naiveCotangentComplex_of_perfect {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Perfect f]
    (hf : IsLocalCompleteIntersectionMorphism f) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0 :=
  isPerfect_and_hasTorAmplitude_naiveCotangentComplex f hf

/-- **Stacks 0FK3, the implication (3) ⇒ (2).** A flat morphism of finite presentation whose
naive cotangent complex has Tor amplitude in `[-1, 0]` is syntomic.

Syntomicity is a condition at each point of the source, asking for affine opens `V ∋ x` of `X`
and `U` of `Y` with `V ⊆ f⁻¹(U)` over which the morphism is syntomic on sections. On such a pair
the hypothesis descends to Tor amplitude in `[-1, 0]` of `NL_{Γ(X, V)/Γ(Y, U)}` in
`D(Γ(X, V))`, and `Γ(Y, U) → Γ(X, V)` is flat of finite presentation, so Stacks 0FJV makes it
syntomic. Quasi-compactness and quasi-separatedness are not used. -/
@[stacks 0FK3 "(3) ⇒ (2): a flat morphism of finite presentation whose naive cotangent complex \
  has tor-amplitude in [-1,0] is syntomic"]
theorem syntomic_of_hasTorAmplitude_naiveCotangentComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] (hfp : FinitePresentation f)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    Syntomic f := by
  have : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
  intro x
  obtain ⟨U, hfxU⟩ : ∃ U : Y.affineOpens, f.base x ∈ U.1 := by
    obtain ⟨-, ⟨U, hU, rfl⟩, hfxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
    exact ⟨⟨U, hU⟩, hfxU⟩
  obtain ⟨V, hxV, hVU⟩ : ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ f ⁻¹ᵁ U.1 := by
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (f ⁻¹ᵁ U.1 : X.Opens) from hfxU) (f ⁻¹ᵁ U.1).2
    exact ⟨⟨V, hV⟩, hxV, hVU⟩
  exact ⟨V, hxV, U, hVU,
    NaiveCotangentLocalCompleteIntersection.syntomic_appLE_of_hasTorAmplitude f hVU U.2 V.2 hamp⟩

/-- **Stacks 0FK3, the implication (3) ⇒ (1).** A flat morphism of finite presentation whose
naive cotangent complex has Tor amplitude in `[-1, 0]` is a local complete intersection
morphism: it is syntomic, and a syntomic morphism is Koszul by Stacks 069K. -/
@[stacks 0FK3 "(3) ⇒ (1): a flat morphism of finite presentation whose naive cotangent complex \
  has tor-amplitude in [-1,0] is a local complete intersection morphism"]
theorem isLocalCompleteIntersectionMorphism_of_hasTorAmplitude_naiveCotangentComplex
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (hfp : FinitePresentation f)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    IsLocalCompleteIntersectionMorphism f :=
  isLocalCompleteIntersectionMorphism_of_syntomic
    (syntomic_of_hasTorAmplitude_naiveCotangentComplex f hfp hamp)

/-- **Stacks 0FK3.** For a flat morphism of finite presentation `f : X ⟶ Y` the following are
equivalent: `f` is a local complete intersection morphism; `f` is syntomic; `NL_{X/Y}` has Tor
amplitude in `[-1, 0]`; `NL_{X/Y}` is perfect with Tor amplitude in `[-1, 0]`. -/
@[stacks 0FK3]
theorem naiveCotangentComplex_tfae {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] (hfp : FinitePresentation f) :
    List.TFAE
      [IsLocalCompleteIntersectionMorphism f,
        Syntomic f,
        Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0,
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
          Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0] := by
  tfae_have 1 ↔ 2 := isLocalCompleteIntersectionMorphism_iff_syntomic f hfp
  tfae_have 1 → 4 := isPerfect_and_hasTorAmplitude_naiveCotangentComplex f
  tfae_have 4 → 3 := hasTorAmplitude_naiveCotangentComplex_of_isPerfect_of_hasTorAmplitude f
  tfae_have 3 → 2 := syntomic_of_hasTorAmplitude_naiveCotangentComplex f hfp
  tfae_finish

end AlgebraicGeometry

end
