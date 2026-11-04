module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineSchemeTorDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.ProperDirectImage
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.RestrictedPushforwardComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.Restriction
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image of a perfect complex along a perfect proper morphism is perfect

Let `S` be a Noetherian scheme, let `f : X ⟶ S` be a perfect proper morphism of schemes and let
`E` be a perfect object of `D(𝒪_X)`. [Stacks, Tag 0B6G] asserts that `Rf_*E` is a perfect object of
`D(𝒪_S)`. By [Stacks, Tag 08CQ] that is pseudo-coherence together with locally finite Tor
dimension; the first half is
`PerfectProperDirectImage.isPseudoCoherent_derivedPushforward_of_isPerfect`, and this file proves
the second and concludes the tag.

## Main results

* `AlgebraicGeometry.restrictedDerivedPushforwardIso` and
  `AlgebraicGeometry.restrictedDerivedPushforwardRestrictFunctorIso`: the vertices of the relative
  Mayer--Vietoris triangle of [Stacks, Tag 08HZ], read as derived direct images of restrictions.
* `AlgebraicGeometry.hasFiniteTorDimension_restrictFunctor`: finite Tor dimension is inherited by
  the restriction to an open subscheme.
* `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_affine_induction`: the
  Mayer--Vietoris induction over a finite affine cover of a quasi-compact quasi-separated source,
  for an arbitrary property of objects inherited by restriction to opens.
* `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine_target`: **the
  Tor-dimension half over an affine base.** For `g : Y ⟶ W` perfect with `W` affine and `Y`
  quasi-compact and quasi-separated, and `A` an object of `D(𝒪_Y)` with quasi-coherent cohomology
  and finite Tor dimension, `Rg_*A` has finite Tor dimension on `W`.
* `PerfectProperDirectImage.hasFiniteTorDimension_derivedPushforward_affineOpen`: for each
  affine open `V ⊆ S`, `R(f|_V)_*(E|_{f^{-1}V})` has finite Tor dimension on `V`.
* `PerfectProperDirectImage.isPerfect_derivedPushforward_of_isPerfect`: [Stacks, Tag 0B6G], that
  `Rf_*E` is a perfect object of `D(𝒪_S)`.

## The proof

The source checks the hypotheses of [Stacks, Tag 08EV] and quotes that tag; its Tor-dimension half
is proved there by tensoring `Rf_*E` with a quasi-coherent module, moving the tensor product inside
`Rf_*` by the projection formula of [Stacks, Tag 08EU], and converting the resulting vanishing into
Tor amplitude by [Stacks, Tag 08EA]. Neither of those two inputs is available in this library at
the generality the argument needs; the route taken instead avoids both.

Locally finite Tor dimension is a statement about a cover of `S`, so by
`PerfectProperDirectImage.locallyHasFiniteTorDimension_derivedPushforward_of_forall_affineOpen`
— [Stacks, Tag 08FE] joined to the affine-locality of the predicate — it suffices to bound the Tor
amplitude of `R(f|_V)_*(E|_{f^{-1}V})` for each affine open `V ⊆ S`. Over such a `V` the source
`f^{-1}V` is quasi-compact and quasi-separated, so the induction principle of [Stacks, Tag 08DR] in
the two-open-cover shape,
`Stacks.Cohomology.DerivedBaseChange.compact_open_immersion_induction_on`, reduces the bound to
the case of an *affine* source. There:

* the inductive step is the relative Mayer--Vietoris triangle of [Stacks, Tag 08HZ]
  (`Stacks.Cohomology.RelativeMayerVietoris.canonicalPushforwardTriangle_distinguished`), whose
  first vertex is the direct image over the open being treated and whose other two vertices are
  the direct images over the two members of the cover and over their intersection. Clause (2) of
  [Stacks, Tag 08CK] (`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_biprod`) bounds the
  biproduct at the second vertex, and clause (1) of [Stacks, Tag 08CJ]
  (`Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₁`) transports the bound to the
  first vertex;
* the base case is `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine`,
  the affine case of the Tor-dimension half of [Stacks, Tag 08EV] at a morphism of affine schemes,
  which rests on [Stacks, Tag 0A9F] and the Tor clause of perfectness of `f`.

The object is universally quantified in the inductive statement rather than restricted along the
way, which is what makes the step formal: the hypotheses on it — quasi-coherent cohomology and
finite Tor dimension — are both inherited by the restriction to an open subscheme
(`AlgebraicGeometry.isQuasicoherent_homology_restrictFunctor_mapDerivedCategory` and
`AlgebraicGeometry.hasFiniteTorDimension_restrictFunctor`), so no compatibility of iterated
restrictions is needed.

## Implementation notes

*Why the triangle needs an identification first.* [Stacks, Tag 08HZ] is stated with the three
restricted direct images as right derived functors of the composites
`Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforwardAlong f i = i^* ⋙ (i ≫ f)_*`; it
contains no functor `D(𝒪_X) ⥤ D(𝒪_U)`. The identification of those vertices with
`R(i ≫ f)_*(E|_U)` is
`Stacks.Cohomology.RelativeMayerVietoris.canonicalRestrictedPushforwardIso`, read at the scheme
spelling below.

*What the hypotheses on `E` and `f` are used for.* Properness of `f` enters only through the
pseudo-coherence half and through quasi-compactness and quasi-separatedness of `X`; the
Tor-dimension statement
`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine_target` assumes no
properness, which is what lets the induction run over opens of `f^{-1}V`, where properness fails.
Noetherianness of `S` is used to see that the cohomology sheaves of `E` are coherent
([Stacks, Tag 0FXU]) and hence quasi-coherent, which is the hypothesis `hA` of the affine base
case.

*Finite Tor dimension of `E` on all of `X`.* A perfect object is of locally finite Tor dimension
([Stacks, Tag 08CS], `Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect`),
and `X` is quasi-compact, being proper over a quasi-compact base, so the local statement is a
global one by `AffineRelativeTorAmplitude.locallyHasFiniteTorDimension_iff_hasFiniteTorDimension`.
The restriction to `f^{-1}V` is then handled by `hasFiniteTorDimension_restrictFunctor`.

## References

* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08CJ](https://stacks.math.columbia.edu/tag/08CJ)
* [Stacks Project, Tag 08CK](https://stacks.math.columbia.edu/tag/08CK)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 0687](https://stacks.math.columbia.edu/tag/0687)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.SchemeCohomology (hom)
open Stacks.Cohomology.TorAmplitude
open Stacks.Cohomology.RelativeMayerVietoris
open Stacks.Cohomology.DerivedBaseChange (compact_open_immersion_induction_on)
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The vertices of the Mayer--Vietoris triangle, as derived direct images of restrictions -/

/-- **A vertex of the relative Mayer--Vietoris triangle, for schemes.** For `G : X ⟶ W` a morphism
of schemes and `i : Z ⟶ X` an open immersion, the canonical right derived functor of
`Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforwardAlong G i` is inverse image along
`i` followed by the derived direct image along `i ≫ G`.

This is `Stacks.Cohomology.RelativeMayerVietoris.canonicalRestrictedPushforwardIso` at the scheme
spelling: inverse image along an open immersion of schemes is exact, so it carries no derivation,
and its witness as a right derived functor is
`CategoryTheory.Functor.isRightDerivedFunctor_of_inverts`. -/
def restrictedDerivedPushforwardIso {Z X W : Scheme.{u}} (G : X ⟶ W) (i : Z ⟶ X)
    [IsOpenImmersion i] :
    canonicalRightDerived (restrictedPushforwardAlong (hom G) (hom i)) ≅
      (Scheme.Modules.pullback i).mapDerivedCategory ⋙ schemeDerivedPushforward (i ≫ G) :=
  have hli : PreservesFiniteLimits (Scheme.Modules.pullback i) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion i
  have hiR : (Scheme.Modules.pullback i).mapDerivedCategory.IsRightDerivedFunctor
      (Scheme.Modules.pullback i).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _
      (Scheme.Modules.pullback i).mapDerivedCategoryFactorsh
  have hgR : (schemeDerivedPushforward (i ≫ G)).IsRightDerivedFunctor
      (schemeDerivedPushforwardUnit (i ≫ G))
      (HomotopyCategory.quasiIso Z.Modules (ComplexShape.up ℤ)) := inferInstance
  @canonicalRestrictedPushforwardIso _ _ _ (hom G) (hom i) _
    (Scheme.Modules.pullback i).mapDerivedCategory (schemeDerivedPushforward (i ≫ G))
    (Scheme.Modules.pullback i).mapDerivedCategoryFactorsh.inv
    (schemeDerivedPushforwardUnit (i ≫ G)) hiR hgR

/-- `AlgebraicGeometry.restrictedDerivedPushforwardIso` with the restriction edge written as
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which is the spelling the Tor-amplitude
statements of this chapter are phrased at. -/
def restrictedDerivedPushforwardRestrictFunctorIso {Z X W : Scheme.{u}} (G : X ⟶ W) (i : Z ⟶ X)
    [IsOpenImmersion i] :
    canonicalRightDerived (restrictedPushforwardAlong (hom G) (hom i)) ≅
      (Scheme.Modules.restrictFunctor i).mapDerivedCategory ⋙
        schemeDerivedPushforward (i ≫ G) :=
  restrictedDerivedPushforwardIso G i ≪≫
    Functor.isoWhiskerRight
      (Scheme.Modules.mapDerivedCategoryRestrictFunctorIsoPullback i).symm
      (schemeDerivedPushforward (i ≫ G))

/-! ### The cover conditions of the triangle, for a two-open cover of a scheme -/

/-- The image of the inclusion of an open subscheme is that open. -/
theorem range_hom_opensι {Z : Scheme.{u}} (U : Z.Opens) :
    Set.range (hom U.ι).hom.base = (U : Set Z) := U.range_ι

/-- Two opens covering a scheme have inclusions whose images cover its space, which is the cover
hypothesis of [Stacks, Tag 08HZ]. -/
theorem range_hom_opensι_union {Z : Scheme.{u}} (U V : Z.Opens) (hUV : U ⊔ V = ⊤) :
    Set.range (hom U.ι).hom.base ∪ Set.range (hom V.ι).hom.base = Set.univ := by
  rw [range_hom_opensι U, range_hom_opensι V, ← TopologicalSpace.Opens.coe_sup, hUV,
    TopologicalSpace.Opens.coe_top]

/-- The inclusion of the intersection of two opens has for image the intersection of their
images, which is the intersection hypothesis of [Stacks, Tag 08HZ]. -/
theorem range_hom_opensι_inter {Z : Scheme.{u}} (U V : Z.Opens) :
    Set.range (hom (U ⊓ V).ι).hom.base =
      Set.range (hom U.ι).hom.base ∩ Set.range (hom V.ι).hom.base := by
  rw [range_hom_opensι U, range_hom_opensι V, range_hom_opensι (U ⊓ V),
    TopologicalSpace.Opens.coe_inf]

/-! ### Finite Tor dimension restricts to an open subscheme -/

/-- **Finite Tor dimension is inherited by the restriction to an open subscheme.** This is
[Stacks, Tag 08CG]'s locality of Tor amplitude
(`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_restrictModules`) read at Mathlib's spelling of
restriction. The interval is replaced by `[min a b, max a b]` because the restriction statement
asks for a nonempty interval and `HasFiniteTorDimension` does not provide one. -/
theorem hasFiniteTorDimension_restrictFunctor {Z : Scheme.{u}} (O : Z.Opens)
    (B : DerivedCategory Z.Modules) (hB : HasFiniteTorDimension Z.toRingedSpace B) :
    HasFiniteTorDimension (O.toScheme).toRingedSpace
      ((Scheme.Modules.restrictFunctor O.ι).mapDerivedCategory.obj B) := by
  obtain ⟨a, b, hab⟩ := hB
  refine ⟨min a b, max a b,
    (Stacks.AlgebraicGeometry.PerfectProperDirectImage.hasTorAmplitude_restrictModules_iff_restrictFunctor
      Z O B _ _).1 ?_⟩
  exact hasTorAmplitude_restrictModules.{u, u + 1} (X := Z.toRingedSpace) O B (min a b) (max a b)
    min_le_max
    (FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} hab (min_le_left a b) (le_max_right a b))

/-! ### The Mayer--Vietoris induction over a quasi-compact quasi-separated source -/

/-- **Finite Tor dimension of a derived direct image, by induction over a finite affine cover of
the source.** Let `g : Y ⟶ W` be a morphism of schemes with `Y` quasi-compact and
quasi-separated, and let `H` be a property of objects of `D(𝒪_Z)` for the open immersions
`jZ : Z ⟶ Y`, inherited by the restriction to an open subscheme of `Z`. If `R(jZ ≫ g)_*B` has
finite Tor dimension on `W` for every affine `Z` and every `B` with `H jZ B`, then `Rg_*A` has
finite Tor dimension on `W` for every `A` with `H (𝟙 Y) A`.

The induction of [Stacks, Tag 08DR], in the shape
`Stacks.Cohomology.DerivedBaseChange.compact_open_immersion_induction_on`, is run on the property
"for every `B` with `H jZ B`, `R(jZ ≫ g)_*B` has finite Tor dimension on `W`". The cover step is
the relative Mayer--Vietoris triangle of [Stacks, Tag 08HZ], read with [Stacks, Tag 08CK] at its
biproduct vertex and [Stacks, Tag 08CJ] (1) at the vertex being bounded. The object is universally
quantified in the inductive statement rather than restricted along the way, so no compatibility of
iterated restrictions is needed. -/
theorem hasFiniteTorDimension_schemeDerivedPushforward_of_affine_induction
    {Y W : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ W)
    (H : ∀ {Z : Scheme.{u}}, (Z ⟶ Y) → DerivedCategory Z.Modules → Prop)
    (hres : ∀ {Z : Scheme.{u}} (jZ : Z ⟶ Y) [IsOpenImmersion jZ] (O : Z.Opens)
      (B : DerivedCategory Z.Modules), H jZ B →
        H (O.ι ≫ jZ) ((Scheme.Modules.restrictFunctor O.ι).mapDerivedCategory.obj B))
    (hbase : ∀ {Z : Scheme.{u}} [IsAffine Z] (jZ : Z ⟶ Y) [IsOpenImmersion jZ]
      (B : DerivedCategory Z.Modules), H jZ B →
        HasFiniteTorDimension W.toRingedSpace ((schemeDerivedPushforward (jZ ≫ g)).obj B))
    (A : DerivedCategory Y.Modules) (hA : H (𝟙 Y) A) :
    HasFiniteTorDimension W.toRingedSpace ((schemeDerivedPushforward g).obj A) := by
  set P : ∀ Z : Scheme.{u}, (Z ⟶ Y) → Prop := fun Z jZ =>
    IsOpenImmersion jZ → ∀ B : DerivedCategory Z.Modules, H jZ B →
      HasFiniteTorDimension W.toRingedSpace ((schemeDerivedPushforward (jZ ≫ g)).obj B)
  have hP : P Y (𝟙 Y) := by
    refine compact_open_immersion_induction_on P ?_ ?_
    · intro Z _ _ _ jZ _ _ B hB
      exact hbase jZ B hB
    · intro Z _ _ jZ _ U V hUV hPU hPV hPUV _ B hB
      have key : ∀ O : Z.Opens, P O.toScheme (O.ι ≫ jZ) →
          HasFiniteTorDimension W.toRingedSpace
            ((canonicalRightDerived
              (restrictedPushforwardAlong (hom (jZ ≫ g)) (hom O.ι))).obj B) := by
        intro O hO
        obtain ⟨a, b, hab⟩ := hO inferInstance _ (hres jZ O B hB)
        rw [Category.assoc] at hab
        exact ⟨a, b, FlatOpcycles.hasTorAmplitude_of_iso (X := W.toRingedSpace) hab
          ((restrictedDerivedPushforwardRestrictFunctorIso (jZ ≫ g) O.ι).app B)⟩
      obtain ⟨a₂, b₂, h₂⟩ := hasFiniteTorDimension_biprod.{u, u + 1} (X := W.toRingedSpace)
        ((canonicalRightDerived (restrictedPushforwardAlong (hom (jZ ≫ g)) (hom U.ι))).obj B)
        ((canonicalRightDerived (restrictedPushforwardAlong (hom (jZ ≫ g)) (hom V.ι))).obj B)
        (key U hPU) (key V hPV)
      obtain ⟨a₃, b₃, h₃⟩ := key (U ⊓ V) hPUV
      have hT := canonicalPushforwardTriangle_distinguished (hom (jZ ≫ g)) (hom U.ι) (hom V.ι)
        (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) B
      have hobj₁ := canonicalPushforwardTriangle_obj₁ (hom (jZ ≫ g)) (hom U.ι) (hom V.ι)
        (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) B
      have hobj₂ := canonicalPushforwardTriangle_obj₂ (hom (jZ ≫ g)) (hom U.ι) (hom V.ι)
        (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) B
      have hobj₃ := canonicalPushforwardTriangle_obj₃ (hom (jZ ≫ g)) (hom U.ι) (hom V.ι)
        (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) B
      refine ⟨min (a₂ - 1) a₃ + 1, max (b₂ - 1) b₃ + 1, ?_⟩
      have hmain := FlatOpcycles.hasTorAmplitude_obj₁.{u, u + 1} (X := W.toRingedSpace) _ hT
        (min (a₂ - 1) a₃) (max (b₂ - 1) b₃)
        (by
          rw [hobj₂]
          exact FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} h₂ (by omega) (by omega))
        (by
          rw [hobj₃]
          exact FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} h₃ (min_le_right _ _)
            (le_max_right _ _))
      rwa [hobj₁] at hmain
  have hfin := hP inferInstance A hA
  rwa [Category.id_comp] at hfin

/-! ### The Tor-dimension half over an affine base -/

/-- **The Tor-dimension half of [Stacks, Tag 08EV] over an affine base.** Let `g : Y ⟶ W` be a
perfect morphism of schemes with `W` affine and `Y` quasi-compact and quasi-separated, and let `A`
be an object of `D(𝒪_Y)` whose cohomology sheaves are quasi-coherent and which has finite Tor
dimension on `Y`. Then `Rg_*A` has finite Tor dimension on `W`.

This is `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_affine_induction` at
the property "quasi-coherent cohomology and finite Tor dimension", which is inherited by the
restriction to an open subscheme. The affine case is
`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine`, available because
an open immersion is perfect (being flat and locally of finite presentation) and perfectness is
stable under composition ([Stacks, Tag 0689]).

No properness is assumed, and none is available: the opens of `Y` that the induction passes
through are not proper over `W`. -/
@[sga "5 III 6.3" "special case"]
theorem hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine_target
    {Y W : Scheme.{u}} [IsAffine W] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : Y ⟶ W) [Perfect g] (A : DerivedCategory Y.Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj A).IsQuasicoherent)
    (hTor : HasFiniteTorDimension Y.toRingedSpace A) :
    HasFiniteTorDimension W.toRingedSpace ((schemeDerivedPushforward g).obj A) :=
  hasFiniteTorDimension_schemeDerivedPushforward_of_affine_induction g
    (fun {Z} _ B =>
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor Z.Modules i).obj B).IsQuasicoherent) ∧
        HasFiniteTorDimension Z.toRingedSpace B)
    (fun _ _ O B hB => ⟨isQuasicoherent_homology_restrictFunctor_mapDerivedCategory O.ι hB.1,
      hasFiniteTorDimension_restrictFunctor O B hB.2⟩)
    (fun jZ _ B hB => by
      have : Perfect jZ := inferInstance
      exact hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine (jZ ≫ g) B hB.1 hB.2)
    A ⟨hqc, hTor⟩

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.PerfectProperDirectImage

open _root_.AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### [Stacks, Tag 0B6G] -/

/-- **The affine-open Tor bound of [Stacks, Tag 0B6G], discharged.** Let `S` be a Noetherian
scheme, let `f : X ⟶ S` be a perfect proper morphism of schemes, let `E` be a perfect object of
`D(𝒪_X)` and let `V ⊆ S` be an affine open. Then `R(f|_V)_*(E|_{f^{-1}V})` has finite Tor dimension
on `V`.

`f|_V` is perfect, perfectness being Zariski local on the target; `f^{-1}V` is quasi-compact,
`f` being quasi-compact and `V` affine, and quasi-separated, being an open of the Noetherian
scheme `X`; the cohomology sheaves of `E` are coherent by [Stacks, Tag 0FXU], hence
quasi-coherent; and `E` has finite Tor dimension on `X` because it is perfect and `X` is
quasi-compact. So
`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine_target` applies. -/
theorem hasFiniteTorDimension_derivedPushforward_affineOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [Perfect f] [IsProper f]
    (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (V : S.affineOpens) :
    Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
      (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding)
      ((schemeDerivedPushforward (f ∣_ (V : S.Opens))).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).mapDerivedCategory.obj E)) := by
  have hX : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : IsAffine (V : S.Opens).toScheme := V.2
  have : Perfect (f ∣_ (V : S.Opens)) :=
    IsZariskiLocalAtTarget.restrict (P := @Perfect) inferInstance _
  have : CompactSpace (f ⁻¹ᵁ (V : S.Opens)).toScheme :=
    isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := f) _ (V : S.Opens).isOpen V.2.isCompact)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ (V : S.Opens)).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated (f ⁻¹ᵁ (V : S.Opens)).ι
  have hqcE : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent := by
    intro i
    have := (isCoherent_homology_and_bounds_of_isPerfect f E hE).1 i
    exact isQuasicoherent_of_isCoherent _
  have hTorE : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension X.toRingedSpace E :=
    (AffineRelativeTorAmplitude.locallyHasFiniteTorDimension_iff_hasFiniteTorDimension
      (X := X.toRingedSpace) E).1
      (Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect
        (X := X.toRingedSpace) E hE)
  exact hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine_target
    (f ∣_ (V : S.Opens)) _
    (isQuasicoherent_homology_restrictFunctor_mapDerivedCategory (f ⁻¹ᵁ (V : S.Opens)).ι hqcE)
    (hasFiniteTorDimension_restrictFunctor (f ⁻¹ᵁ (V : S.Opens)) E hTorE)

/-- **[Stacks, Tag 0B6G].** Let `S` be a Noetherian scheme, let `f : X ⟶ S` be a perfect proper
morphism of schemes and let `E` be a perfect object of `D(𝒪_X)`. Then `Rf_*E` is a perfect object
of `D(𝒪_S)`.

By [Stacks, Tag 08CQ] perfectness is pseudo-coherence together with locally finite Tor dimension.
Pseudo-coherence is `isPseudoCoherent_derivedPushforward_of_isPerfect`, and the Tor-dimension half
is `hasFiniteTorDimension_derivedPushforward_affineOpen` fed into
`isPerfect_derivedPushforward_of_isPerfect_of_forall_affineOpen`. Nothing is assumed beyond the
source's own hypotheses. -/
@[stacks 0B6G,
  sga "6 0 3.1" "special case",
  sga "6 0 4.1",
  sga "6 III 4.8.1" "special case",
  sga "6 IV 2.12" "special case",
  sga "6 IV 3.3.2" "3.3.2.3, special case",
  sga "6 XIV 2.2" "special case"]
theorem isPerfect_derivedPushforward_of_isPerfect {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [Perfect f] [IsProper f] (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  isPerfect_derivedPushforward_of_isPerfect_of_forall_affineOpen f E hE
    fun V => hasFiniteTorDimension_derivedPushforward_affineOpen f E hE V

end Stacks.AlgebraicGeometry.PerfectProperDirectImage

end
