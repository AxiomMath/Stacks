module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksFrontier.AlgebraicGeometry.Conormal.SplitCotangentFibre
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningRestrict
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.TwoImmersionsConormalExact
public import StacksFrontier.AlgebraicGeometry.Morphisms.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairConormalSequence
public import StacksFrontier.RingTheory.NaiveCotangent.Conormal
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of a formally unramified pair over a formally smooth morphism

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be formally unramified morphisms of schemes in a commutative
triangle `i ≫ p = j`, and assume `p : X ⟶ Y` is formally smooth. [Stacks, Tag 067W] asserts
that the canonical sequence

`0 ⟶ 𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0`

of [Stacks, Tag 067V] is exact and **locally split**. Locally split is used in the source in
exactly one sense, the one its proof produces: every point of `Z` has an open neighbourhood over
which the first arrow `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` admits a retraction. The two assertions are not
independent — injectivity of the first arrow, the only strengthening of [Stacks, Tag 067V]'s
right-exact sequence to a short exact one, is deduced from the local retraction.

## Main definitions

* `Stacks.ConormalSequenceUnramifiedPair.conormalSequenceFirstArrow` and
  `Stacks.ConormalSequenceUnramifiedPair.conormalSequenceSecondArrow`: the two arrows of the
  sequence, as morphisms of `AlgebraicGeometry.Scheme.Modules Z`, so that their composite and
  hence the short complex can be written down.
* `Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso`: the identification of the
  two presentations of the conormal sheaf of an immersion used in this library, as the pullback
  of a sectionwise kernel and as the pullback of a categorical kernel.
* `Stacks.ConormalSequenceTwoImmersions.immersionConormalSheafModules`,
  `Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMapModules` and
  `Stacks.ConormalSequenceTwoImmersions.conormalDifferentialModules`: the two arrows of the
  sequence of [Stacks, Tag 067L] for an arbitrary triangle of immersions, with both ends in the
  `Z.Modules` spelling, which is what lets their composite be written down. The second is the
  canonical map of [Stacks, Tag 01R4] and the third the conormal differential of
  [Stacks, Tag 01UZ] read through `conormalSheafComparisonIso`.

## Main results

* `exists_retraction_restrict_universalConormalTransitivityMap` and
  `exists_retraction_restrict_conormalSequenceFirstArrow`, both in this namespace:
  **the sequence is locally split** — every point of `Z` has an open neighbourhood over which the
  first arrow admits a retraction. This needs no exactness input and is the whole constructive
  content of the source's proof.
* `Stacks.ConormalSequenceUnramifiedPair.mono_conormalSequenceFirstArrow`: **the first arrow is a
  monomorphism**, which is the `0 ⟶` at the left-hand end of the sequence. A morphism of modules
  on a scheme which is a monomorphism on a neighbourhood of every point is a monomorphism, and a
  retraction makes one.
* `universalConormalTransitivityMap_eq_conormalTransitivityMap`, in this namespace:
  the first arrow of [Stacks, Tag 067V] is the first arrow of [Stacks, Tag 067L] for the two
  closed immersions of `Z` into the ambient schemes of the two universal first-order thickenings,
  over the canonical morphism between them. This is the reduction the source performs, and it is
  what makes the functoriality of [Stacks, Tag 01R4] available to the proof.
* `conormalSequenceComp_eq_zero`, `conormalSequenceShortComplex_exact` and
  `epi_conormalSequenceSecondArrow`, all in this namespace: **the three assertions of
  [Stacks, Tag 067V]** — the composite of the two arrows vanishes, the sequence is exact at
  `𝒞_{Z/X}`, and the second arrow is an epimorphism.
* `Stacks.ConormalSequenceUnramifiedPair.shortExact_of_comp_eq_zero_of_exact`: **the sequence is
  short exact**; see below.
* `Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMapModules_comp_eq_zero`
  and `Stacks.ConormalSequenceTwoImmersions.conormalShortComplexModules_exact`: **the two
  remaining clauses of [Stacks, Tag 067L]** — for an arbitrary commutative triangle
  `i ≫ p = j` of immersions the two arrows of `𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` compose to zero
  and the sequence is exact at `𝒞_{Z/X}`. These are the statements the clauses of
  [Stacks, Tag 067V] are deduced from.

## The proof of the local splitting

Write `Z ⊂ Z'` for the universal first-order thickening of `Z` over `X` and `Z ⊂ Z''` for the one
over `Y`, and `k : Z' ⟶ Z''` for the canonical morphism between their ambient schemes, which is
`Stacks.ConormalSequenceUnramifiedPair.thickeningComparison`. The source's proof produces, over
an affine open `U'' ⊆ Z''`, a *section of `k` over `U''`*:

* an affine open `U'' ⊆ Z''` through the chosen point, with `U = (Z ⟶ Z'')^{-1} U''` affine and
  `U ⟶ U''` again a first-order thickening by [Stacks, Tag 04FA];
* formal smoothness of `p` lifts `U ⟶ Z ⟶ X` along `U ⟶ U''` to `h : U'' ⟶ X` over `Y`;
* the universal property of `Z'` turns `h` into `g : U'' ⟶ Z'` restricting to `U ⟶ Z ⟶ Z'`, and
  the universal property of `Z''` forces `g ≫ k` to be the inclusion `U'' ⟶ Z''`, since both it
  and the inclusion lift the same datum.

That is `Stacks.ConormalSequenceUnramifiedPair.exists_local_section_of_formallySmooth`. The
retraction is then pure functoriality of [Stacks, Tag 01R4]. For the square of `U ⟶ U''` over
`(V.ι, W.ι)` the canonical map `(U ⟶ Z)^* 𝒞_{Z/Z''} ⟶ 𝒞_{U/U''}` is an isomorphism by
[Stacks, Tag 0473], the square being cartesian and `U'' ⟶ Z''` flat; the square of `U ⟶ U''` over
`(U ⟶ Z, g)` gives a second map `(U ⟶ Z)^* 𝒞_{Z/Z'} ⟶ 𝒞_{U/U''}`; and because `g ≫ k` is the
inclusion, the composition law
`Stacks.Immersion.immersionConormalSheafMap_comp` of [Stacks, Tag 04G2] says that the first map
is the pullback of the first arrow followed by the second. Inverting the first map therefore
retracts the pullback of the first arrow, and restriction along an open immersion is isomorphic
to that pullback.

## The two arrows

The first arrow is `Stacks.ConormalSequenceUnramifiedPair.universalConormalTransitivityMap` of
[Stacks, Tag 067V]. The second is the conormal differential of [Stacks, Tag 01UZ] for the
immersion `Z ⟶ Z'` over `Z''`, which is the second arrow of the sequence of [Stacks, Tag 067L]
that the source's proof reduces to, moved onto `i^*Ω_{X/Y}` by
`Stacks.ConormalSequenceUnramifiedPair.thirdTermIso` — the identification of the third term that
[Stacks, Tag 067V] supplies, and which is [Stacks, Tag 04FB] followed by the vanishing of
`Ω_{Z''/Y}`.

The two arrows are stated as morphisms of `AlgebraicGeometry.Scheme.Modules Z` rather than of
`CategoryTheory.SheafOfModules (structureSheafRing Z.toRingedSpace)`, which is
where the conormal sheaf of an immersion is built. The two categories are definitionally equal but
not reducibly so, and typeclass resolution does not find the `Zero` instance on a `Hom` type whose
two ends are written in the two spellings. Naming the objects with their type declared to be
`Z.Modules`, which is `Stacks.ConormalSequenceUnramifiedPair.conormalSheafModules`, lets the
equation `a ≫ b = 0` be stated.

## The three assertions of Tag 067V

[Stacks, Tag 067W] says the sequence of [Stacks, Tag 067V] *is exact and locally split*. Locally
split and injectivity of the first arrow belong to this tag and are proved above. The rest of the
exactness belongs to [Stacks, Tag 067V]: the composite of the two arrows vanishes, the sequence is
exact at `𝒞_{Z/X}`, and the second arrow is an epimorphism. All three are proved below.

Each follows from the corresponding statement for the two closed immersions `Z ⟶ Z'`, `Z ⟶ Z''`
over the comparison morphism `k`, which is the reduction the source performs and which is carried
out here for an arbitrary pair of immersions `i : Z ⟶ X`, `j : Z ⟶ Y` in a triangle `i ≫ p = j`.

* The composite vanishes because the second arrow carries the conormal class of a local section
  `a` of the ideal sheaf of `j`, pushed into `𝒪_X` along `p`, to `1 ⊗ d (p^♯ a)`, and the
  universal derivation of `X` over `Y` kills a section pulled back along `p`.
* Exactness at the middle term is checked on stalks. At a point `z` of `Z`, write
  `W = i.coborderRange` and `g = i.liftCoborder` for the closed factor of `i`; the tower of local
  rings `𝒪_{Y, j z} ⟶ 𝒪_{W, g z} ⟶ 𝒪_{Z, z}` has surjective composite because `j` is an
  immersion, the three stalks of the sequence are `I/I²`, `J/J²` and
  `𝒪_{Z,z} ⊗ Ω[𝒪_{W,g z}⁄𝒪_{Y,j z}]`, and the two arrows become `Ideal.mapCotangent` and
  `KaehlerDifferential.kerCotangentToTensor`. Exactness of that pair of algebraic maps, together
  with surjectivity of the second one, is
  `exact_mapCotangent_kerCotangentToTensor_and_surjective`, which is [Stacks, Tag 065V].
* Surjectivity of the second arrow is
  `Stacks.ConormalSequenceTwoImmersions.epi_conormalDifferential`, the `⟶ 0` clause of
  [Stacks, Tag 067L], transported along the two flanking isomorphisms.

Two presentations of the conormal sheaf meet in that reduction: the first arrow is built on the
pullback of a categorical kernel, `Stacks.Conormal.conormalSheaf`, and the second on the pullback
of a sectionwise kernel, `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf`.
`Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso` identifies them, and the
identification is used in one place only, to read a conormal class in one presentation as a
conormal class in the other.

## References

* [Stacks Project, Tag 067W](https://stacks.math.columbia.edu/tag/067W)
* [Stacks Project, Tag 067V](https://stacks.math.columbia.edu/tag/067V), the sequence.
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L), the statement for two
  immersions, to which the source reduces this one.
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4), the first arrow.
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2), its functoriality.
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473), flat base change for it.
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the second arrow.
* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0), formal smoothness.
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3), the universal
  first-order thickening.
* [Stacks Project, Tag 04FA](https://stacks.math.columbia.edu/tag/04FA), its restriction to an
  open.
* [Stacks Project, Tag 065V](https://stacks.math.columbia.edu/tag/065V), the commutative-algebra
  statement behind exactness at the middle term.
* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S), the sibling statement
  for two immersions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RelativeDifferentialStalkMap
open Stacks.Thickenings Stacks.Immersion Stacks.ClosedImmersion
open Stacks.ConormalSequenceRight (stalkAb stalkAb_map_germ conormalDifferential
  coborderPullbackDifferentialsIso conormalComparison_comp_conormalDifferential
  exists_germ_eq_of_mem_ker germ_mem_ker_stalkMap)
open scoped TensorProduct

universe u

namespace Stacks.ConormalSequenceUnramifiedPair

/-! ### Coherence of the pullback pseudofunctor at an identity -/

/-- **The composition isomorphism of pullbacks at a composite `f ≫ 𝟙` is the identity
isomorphism of `f`.** For `f : V ⟶ Z` the component at `C` of
`RingedSpaceModuleAdjunction.modulePullbackComp f (𝟙 Z)` is `f^*` applied to the component
of the identification of pullback along `𝟙 Z` with the identity functor. -/
private theorem modulePullbackComp_id_hom_app {V Z : Scheme.{u}} (f : V ⟶ Z)
    (C : SheafOfModules.{u}
      (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)) :
    (modulePullbackComp (Scheme.Hom.toLRSHom f).toShHom
        (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).hom.app C =
      (modulePullback (Scheme.Hom.toLRSHom f).toShHom).map
        ((Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).inv.app C) :=
  congrArg (fun e => e.inv.app C)
    (SheafOfModules.pullback_id_comp (φ := structureSheafHom (Scheme.Hom.toLRSHom f).toShHom))

/-- **A retraction transported along a natural isomorphism of functors.** If `a : A ⟶ B` is a
morphism, `G a` followed by some `b` is an isomorphism `c`, and `F ≅ G`, then `F a` admits a
retraction. -/
private theorem exists_retraction_of_iso_comp {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (a : A ⟶ B) {T : D} (b : G.obj B ⟶ T) (c : G.obj A ⟶ T)
    (hc : IsIso c) (hkey : G.map a ≫ b = c) :
    ∃ r : F.obj B ⟶ F.obj A, F.map a ≫ r = 𝟙 _ := by
  obtain ⟨ρ, hρ, -⟩ := hc.1
  refine ⟨e.hom.app B ≫ b ≫ ρ ≫ e.inv.app A, ?_⟩
  rw [e.hom.naturality_assoc, ← Category.assoc (G.map a) b, hkey, ← Category.assoc c ρ, hρ]
  simp

/-- **The canonical map of [Stacks, Tag 01R4] only depends on the bottom morphism of the square
through the commutativity it witnesses.** Its source and target mention the top morphism but not
the bottom one, so equal bottom morphisms give equal maps. -/
private theorem immersionConormalSheafMap_congr_bottom {Z₁ Z₂ X₁ X₂ : Scheme.{u}}
    (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂) [IsImmersion i₁] [IsImmersion i₂] (f : Z₁ ⟶ Z₂)
    {g g' : X₁ ⟶ X₂} (hgg' : g = g')
    (comm : (Scheme.Hom.toLRSHom i₁).toShHom ≫ (Scheme.Hom.toLRSHom g).toShHom =
      (Scheme.Hom.toLRSHom f).toShHom ≫ (Scheme.Hom.toLRSHom i₂).toShHom)
    (comm' : (Scheme.Hom.toLRSHom i₁).toShHom ≫ (Scheme.Hom.toLRSHom g').toShHom =
      (Scheme.Hom.toLRSHom f).toShHom ≫ (Scheme.Hom.toLRSHom i₂).toShHom) :
    immersionConormalSheafMap i₁ i₂ f g comm = immersionConormalSheafMap i₁ i₂ f g' comm' := by
  subst hgg'
  rfl

/-! ### The retraction attached to a local section of the comparison morphism -/

/-- **A section of the comparison morphism over an open retracts the conormal transitivity map
there.** Let `i' : Z ⟶ Z'` and `j' : Z ⟶ Z''` be closed immersions with `i' ≫ k = j'`, and let
`g : W ⟶ Z'` be defined on an open `W ⊆ Z''` with `g ≫ k` the inclusion of `W` and `g` restricting
to `i'` on `V = (j')^{-1} W`. Then the first arrow `𝒞_{Z/Z''} ⟶ 𝒞_{Z/Z'}` of
[Stacks, Tag 067L] admits a retraction after restriction to `V`. -/
private theorem exists_retraction_of_local_section {Z Z' Z'' : Scheme.{u}}
    (i' : Z ⟶ Z') (j' : Z ⟶ Z'') [IsClosedImmersion i'] [IsClosedImmersion j'] (k : Z' ⟶ Z'')
    (hk : i' ≫ k = j') (W : Z''.Opens) (g : W.toScheme ⟶ Z')
    (hg : j' ∣_ W ≫ g = (j' ⁻¹ᵁ W).ι ≫ i') (hgk : g ≫ k = W.ι) :
    ∃ r : (Scheme.Modules.restrictFunctor (j' ⁻¹ᵁ W).ι).obj (Stacks.Conormal.conormalSheaf i') ⟶
        (Scheme.Modules.restrictFunctor (j' ⁻¹ᵁ W).ι).obj (Stacks.Conormal.conormalSheaf j'),
      (Scheme.Modules.restrictFunctor (j' ⁻¹ᵁ W).ι).map
          (Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i' j' k hk) ≫ r =
        𝟙 _ := by
  have sq : IsPullback (j' ∣_ W) (j' ⁻¹ᵁ W).ι W.ι j' := isPullback_morphismRestrict j' W
  have : IsClosedImmersion (j' ∣_ W) :=
    IsZariskiLocalAtTarget.restrict ‹IsClosedImmersion j'› W
  set α := immersionConormalSheafMap (j' ∣_ W) j' (j' ⁻¹ᵁ W).ι W.ι (toShHom_square sq.w) with hα0
  set β := immersionConormalSheafMap (j' ∣_ W) i' (j' ⁻¹ᵁ W).ι g (toShHom_square hg) with hβ0
  have hisoα : IsIso α :=
    isIso_immersionConormalSheafMap_of_flat (j' ∣_ W) j' (j' ⁻¹ᵁ W).ι W.ι sq
  have hcomm₂ : i' ≫ k = 𝟙 Z ≫ j' := by rw [Category.id_comp]; exact hk
  have hcompose : j' ∣_ W ≫ (g ≫ k) = (j' ⁻¹ᵁ W).ι ≫ j' := by
    rw [← Category.assoc, hg, Category.assoc, hk]
  have hkey' : (modulePullback (Scheme.Hom.toLRSHom (j' ⁻¹ᵁ W).ι).toShHom).map
        (Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i' j' k hk) ≫
      β = α := by
    have hcomp : immersionConormalSheafMap (j' ∣_ W) j' (j' ⁻¹ᵁ W).ι (g ≫ k)
          (toShHom_square hcompose) =
        (modulePullbackComp (Scheme.Hom.toLRSHom (j' ⁻¹ᵁ W).ι).toShHom
              (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).hom.app (Stacks.Conormal.conormalSheaf j') ≫
          (modulePullback (Scheme.Hom.toLRSHom (j' ⁻¹ᵁ W).ι).toShHom).map
              (immersionConormalSheafMap i' j' (𝟙 Z) k (toShHom_square hcomm₂)) ≫
            β :=
      immersionConormalSheafMap_comp (j' ∣_ W) i' j' (j' ⁻¹ᵁ W).ι g hg (𝟙 Z) k hcomm₂
    have hα : immersionConormalSheafMap (j' ∣_ W) j' (j' ⁻¹ᵁ W).ι (g ≫ k)
          (toShHom_square hcompose) = α :=
      immersionConormalSheafMap_congr_bottom _ _ _ hgk _ _
    rw [Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap, Functor.map_comp,
      Category.assoc, ← hα, hcomp, modulePullbackComp_id_hom_app]
    rfl
  have hkey : (Scheme.Modules.pullback (j' ⁻¹ᵁ W).ι).map
        (Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i' j' k hk) ≫
      β = α := hkey'
  exact exists_retraction_of_iso_comp (Scheme.Modules.restrictFunctorIsoPullback (j' ⁻¹ᵁ W).ι)
    (Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i' j' k hk) β α hisoα hkey

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)
  [FormallyUnramified i] [FormallyUnramified j]

/-- **Formal smoothness of `p` gives a local section of the comparison morphism `Z' ⟶ Z''`.**
Every point of `Z` lies in `(Z ⟶ Z'')^{-1} W` for an open `W` of the ambient scheme `Z''` of the
universal first-order thickening of `Z` over `Y` carrying a morphism `g : W ⟶ Z'` to the ambient
scheme of the universal first-order thickening of `Z` over `X` which restricts to `Z ⟶ Z'` and
satisfies `g ≫ k = W ⟶ Z''` for the canonical morphism `k`. -/
private theorem exists_local_section_of_formallySmooth (h : i ≫ p = j)
    (hp : FormallySmooth p) (z : Z) :
    ∃ (W : (universalFirstOrderThickening j).ambient.Opens)
      (g : W.toScheme ⟶ (universalFirstOrderThickening i).ambient),
      z ∈ (universalFirstOrderThickening j).inclusion ⁻¹ᵁ W ∧
        (universalFirstOrderThickening j).inclusion ∣_ W ≫ g =
          ((universalFirstOrderThickening j).inclusion ⁻¹ᵁ W).ι ≫
            (universalFirstOrderThickening i).inclusion ∧
          g ≫ thickeningComparison i j p h = W.ι := by
  obtain ⟨W, hWaff, hzW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show (universalFirstOrderThickening j).inclusion z ∈
      (⊤ : (universalFirstOrderThickening j).ambient.Opens) from trivial)
  have hVaff : IsAffineOpen ((universalFirstOrderThickening j).inclusion ⁻¹ᵁ W) :=
    hWaff.preimage (universalFirstOrderThickening j).inclusion
  have hthick : Stacks.Thickenings.IsFirstOrderThickening
      ((universalFirstOrderThickening j).inclusion ∣_ W) :=
    Stacks.Thickenings.IsFirstOrderThickening.morphismRestrict
      (universalFirstOrderThickening j).isUniversal.isFirstOrderThickening W
  have hι : (universalFirstOrderThickening j).inclusion ∣_ W ≫ W.ι =
      ((universalFirstOrderThickening j).inclusion ⁻¹ᵁ W).ι ≫
        (universalFirstOrderThickening j).inclusion :=
    morphismRestrict_ι (universalFirstOrderThickening j).inclusion W
  have hbase : (universalFirstOrderThickening j).inclusion ∣_ W ≫
      (W.ι ≫ (universalFirstOrderThickening j).toBase) =
        ((universalFirstOrderThickening j).inclusion ⁻¹ᵁ W).ι ≫ j := by
    rw [← Category.assoc, hι, Category.assoc,
      (universalFirstOrderThickening j).isUniversal.inclusion_toBase]
  obtain ⟨gX, hgXp, hgXι⟩ := hp hVaff hWaff
    ((universalFirstOrderThickening j).inclusion ∣_ W) hthick
    (((universalFirstOrderThickening j).inclusion ⁻¹ᵁ W).ι ≫ i)
    (W.ι ≫ (universalFirstOrderThickening j).toBase) (by rw [Category.assoc, h, hbase])
  obtain ⟨g, ⟨hg₁, hg₂⟩, -⟩ := (universalFirstOrderThickening i).isUniversal.existsUnique_lift
    ((universalFirstOrderThickening j).inclusion ∣_ W) hthick
    ((universalFirstOrderThickening j).inclusion ⁻¹ᵁ W).ι gX hgXι
  obtain ⟨q, -, huniq⟩ := (universalFirstOrderThickening j).isUniversal.existsUnique_lift
    ((universalFirstOrderThickening j).inclusion ∣_ W) hthick
    ((universalFirstOrderThickening j).inclusion ⁻¹ᵁ W).ι
    (W.ι ≫ (universalFirstOrderThickening j).toBase) hbase
  refine ⟨W, g, hzW, hg₁, (huniq _ ⟨?_, ?_⟩).trans (huniq _ ⟨hι, rfl⟩).symm⟩
  · rw [← Category.assoc, hg₁, Category.assoc, inclusion_comp_thickeningComparison]
  · rw [Category.assoc, thickeningComparison_comp_toBase, ← Category.assoc, hg₂, hgXp]

/-! ### The first arrow of Tag 067V is the first arrow of Tag 067L -/

/-- **The first arrow of [Stacks, Tag 067V] is the first arrow of [Stacks, Tag 067L].** For the
two closed immersions `Z ⟶ Z'` and `Z ⟶ Z''` of `Z` into the ambient schemes of the universal
first-order thickenings of `i` and of `j`, over the canonical morphism
`Stacks.ConormalSequenceUnramifiedPair.thickeningComparison` between them, the canonical map of
[Stacks, Tag 01R4] of `Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap` is the
morphism of conormal sheaves of [Stacks, Tag 04F7] read through the three identifications of
`Stacks.ConormalSequenceUnramifiedPair.universalConormalTransitivityMap`. -/
theorem universalConormalTransitivityMap_eq_conormalTransitivityMap (h : i ≫ p = j) :
    universalConormalTransitivityMap i j p h =
      Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap
        (universalFirstOrderThickening i).inclusion
        (universalFirstOrderThickening j).inclusion (thickeningComparison i j p h)
        (inclusion_comp_thickeningComparison i j p h) := by
  rw [universalConormalTransitivityMap,
    Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap,
    Stacks.Immersion.immersionConormalSheafMap,
    ← (Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).inv.naturality_assoc]
  rfl

/-! ### The local retraction -/

/-- **[Stacks, Tag 067W]: the conormal sequence is locally split.** For formally unramified
`i : Z ⟶ X` and `j : Z ⟶ Y` in a commutative triangle `i ≫ p = j` with `p` formally smooth, every
point of `Z` has an open neighbourhood `V` over which the first arrow `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of
[Stacks, Tag 067V] admits a retraction. -/
@[stacks 067W "locally split, in the sense the source's proof produces and its final sentence
defines: every point of Z has an open neighbourhood over which the first arrow 𝒞_{Z/Y} ⟶ 𝒞_{Z/X}
of Tag 067V admits a retraction"]
theorem exists_retraction_restrict_universalConormalTransitivityMap (h : i ≫ p = j)
    (hp : FormallySmooth p) (z : Z) :
    ∃ V : Z.Opens, z ∈ V ∧
      ∃ r : (Scheme.Modules.restrictFunctor V.ι).obj (universalConormalSheaf i) ⟶
          (Scheme.Modules.restrictFunctor V.ι).obj (universalConormalSheaf j),
        (Scheme.Modules.restrictFunctor V.ι).map (universalConormalTransitivityMap i j p h) ≫ r =
          𝟙 _ := by
  obtain ⟨W, g, hzW, hg, hgk⟩ := exists_local_section_of_formallySmooth i j p h hp z
  refine ⟨(universalFirstOrderThickening j).inclusion ⁻¹ᵁ W, hzW, ?_⟩
  rw [universalConormalTransitivityMap_eq_conormalTransitivityMap i j p h]
  exact exists_retraction_of_local_section (universalFirstOrderThickening i).inclusion
    (universalFirstOrderThickening j).inclusion (thickeningComparison i j p h)
    (inclusion_comp_thickeningComparison i j p h) W g hg hgk

/-! ### Injectivity of the first arrow -/

/-- **A morphism of modules on a scheme which is a monomorphism near every point is a
monomorphism.** -/
@[sga "4 IV 8.5.1" "partial"]
private theorem mono_of_locally_mono {Z : Scheme.{u}} {M N : Z.Modules} (a : M ⟶ N)
    (ha : ∀ z : Z, ∃ V : Z.Opens, z ∈ V ∧
      Mono ((Scheme.Modules.restrictFunctor V.ι).map a)) : Mono a := by
  constructor
  intro P g h e
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  apply M.isSheaf.section_ext
  intro z hz
  obtain ⟨V, hzV, hV⟩ := ha z
  let R := Scheme.Modules.restrictFunctor V.ι
  have : Mono (R.map a) := hV
  have he : R.map g = R.map h := by
    apply (cancel_mono (R.map a)).mp
    simpa only [← R.map_comp] using congrArg R.map e
  refine ⟨V.ι ''ᵁ (V.ι ⁻¹ᵁ U), V.ι.image_preimage_le U, ⟨⟨z, hzV⟩, hz, rfl⟩, ?_⟩
  have hh : g.app (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) = h.app (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) :=
    congrArg (fun q => Scheme.Modules.Hom.app q (V.ι ⁻¹ᵁ U)) he
  have hgs := congrArg (fun q => q s)
    (g.mapPresheaf.naturality (homOfLE (V.ι.image_preimage_le U)).op)
  have hhs := congrArg (fun q => q s)
    (h.mapPresheaf.naturality (homOfLE (V.ι.image_preimage_le U)).op)
  change g.app (V.ι ''ᵁ (V.ι ⁻¹ᵁ U))
    (P.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op s) = _ at hgs
  change h.app (V.ι ''ᵁ (V.ι ⁻¹ᵁ U))
    (P.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op s) = _ at hhs
  exact hgs.symm.trans ((congrArg (fun q => q (P.presheaf.map
    (homOfLE (V.ι.image_preimage_le U)).op s)) hh).trans hhs)

/-! ### The two arrows, read in the category of modules over the scheme -/

/-- **The conormal sheaf of a formally unramified morphism, as an object of `Z.Modules`.** The
conormal sheaf of [Stacks, Tag 04F4] part (2) is built on the ringed space underlying `Z`, so it
is an object of `CategoryTheory.SheafOfModules (structureSheafRing ...)`; this
is the same object with its type declared to be `AlgebraicGeometry.Scheme.Modules Z`, which is the
category the sheaf of relative differentials lives in. -/
abbrev conormalSheafModules {Z X : Scheme.{u}} (f : Z ⟶ X) [FormallyUnramified f] : Z.Modules :=
  universalConormalSheaf f

/-- **The first arrow `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of [Stacks, Tag 067V], as a morphism of
`Z.Modules`.** -/
def conormalSequenceFirstArrow (h : i ≫ p = j) :
    conormalSheafModules j ⟶ conormalSheafModules i :=
  universalConormalTransitivityMap i j p h

/-- **The two presentations of the conormal sheaf of an immersion agree.** [Stacks, Tag 01R2] is
realized in this library twice: as the pullback along the closed factor of the *sectionwise*
kernel of the structure-sheaf map, which is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf` and is what the conormal differential
of [Stacks, Tag 01UZ] is built on, and as the pullback of the *categorical* kernel, which is
`Stacks.Conormal.conormalSheaf` and is what the canonical map of [Stacks, Tag 01R4] is built on.
The two ideal sheaves are the two kernels of one and the same morphism. -/
def conormalSheafComparisonIso {Z X' : Scheme.{u}} (i' : Z ⟶ X') [IsImmersion i'] :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i' ≅
      Stacks.Conormal.conormalSheaf i' :=
  (modulePullback (Scheme.Hom.toLRSHom (Scheme.Hom.liftCoborder i')).toShHom).mapIso
    (Stacks.AlgebraicGeometry.kernelSubmoduleIso
      (structureSheafModuleHom (Scheme.Hom.toLRSHom (Scheme.Hom.liftCoborder i')).toShHom))

/-- **The second arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` of [Stacks, Tag 067V].** It is the conormal
differential of [Stacks, Tag 01UZ] for the closed immersion `Z ⟶ Z'` of `Z` into the ambient
scheme of its universal first-order thickening over `X`, taken over the ambient scheme `Z''` of
the universal first-order thickening over `Y` — that is, the second arrow of the sequence of
[Stacks, Tag 067L] that the proof of [Stacks, Tag 067V] reduces to — with its target moved onto
`i^*Ω_{X/Y}` by `Stacks.ConormalSequenceUnramifiedPair.thirdTermIso` and its source read through
`Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso`. -/
@[stacks 067V "the second arrow 𝒞_{Z/X} ⟶ i^*Ω_{X/Y}, built as the conormal differential of Tag
01UZ for Z ⟶ Z' over Z'' and moved along the identification thirdTermIso of the third term"]
def conormalSequenceSecondArrow (h : i ≫ p = j) :
    conormalSheafModules i ⟶
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) :=
  (conormalSheafComparisonIso (universalFirstOrderThickening i).inclusion).inv ≫
    Stacks.ConormalSequenceRight.conormalDifferential
        (universalFirstOrderThickening i).inclusion (thickeningComparison i j p h) ≫
      (thirdTermIso i j p h).inv

/-- **[Stacks, Tag 067W]: the first arrow of the conormal sequence is a monomorphism.** This is
the `0 ⟶` at the left-hand end of the sequence, and the only strengthening of the right-exact
sequence of [Stacks, Tag 067V] to a short exact one. -/
@[stacks 067W "exact on the left: the first arrow 𝒞_{Z/Y} ⟶ 𝒞_{Z/X} of Tag 067V is a
monomorphism, which is the only strengthening of Tag 067V's right-exact sequence to a short exact
one that this tag asserts; obtained from the local splitting"]
theorem mono_conormalSequenceFirstArrow (h : i ≫ p = j) (hp : FormallySmooth p) :
    Mono (conormalSequenceFirstArrow i j p h) := by
  apply mono_of_locally_mono
  intro z
  obtain ⟨V, hzV, r, hr⟩ :=
    exists_retraction_restrict_universalConormalTransitivityMap i j p h hp z
  have : IsSplitMono ((Scheme.Modules.restrictFunctor V.ι).map
    (conormalSequenceFirstArrow i j p h)) := ⟨⟨r, hr⟩⟩
  exact ⟨V, hzV, inferInstance⟩

/-- **The local splitting, stated for
`Stacks.ConormalSequenceUnramifiedPair.conormalSequenceFirstArrow`.** This is the `locallySplit`
clause in the shape the library uses for the sibling tag [Stacks, Tag 062S], namely
`Stacks.AlgebraicGeometry.IsSplitExactConormalSequence.locallySplit`. -/
@[stacks 067W "locally split, in the shape of the locallySplit clause the library uses for the
sibling tag 062S"]
theorem exists_retraction_restrict_conormalSequenceFirstArrow (h : i ≫ p = j)
    (hp : FormallySmooth p) (z : Z) :
    ∃ V : Z.Opens, z ∈ V ∧
      ∃ r : (Scheme.Modules.restrictFunctor V.ι).obj (conormalSheafModules i) ⟶
          (Scheme.Modules.restrictFunctor V.ι).obj (conormalSheafModules j),
        (Scheme.Modules.restrictFunctor V.ι).map (conormalSequenceFirstArrow i j p h) ≫ r =
          𝟙 _ :=
  exists_retraction_restrict_universalConormalTransitivityMap i j p h hp z

/-! ### The three assertions of Tag 067V, for an arbitrary pair of immersions -/

section TwoImmersions


private theorem hom_eq_zero_of_stalk {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N)
    (hφ : ∀ (z : Z) (x), (stalkAb Z z).map φ x = 0) : φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  refine TopCat.Presheaf.section_ext (⟨N.val.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab.{u} Z) U _ _
    fun z hz => ?_
  exact (stalkAb_map_germ φ z U hz s).symm.trans ((hφ z _).trans (map_zero _).symm)

private noncomputable def conormalMod {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    Z.Modules := Stacks.Conormal.conormalSheaf i

private noncomputable abbrev regularConormalMod {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    Z.Modules := Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i

private noncomputable abbrev pullbackIdObj {Z : Scheme.{u}} (M : Z.Modules) : Z.Modules :=
  (modulePullback (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).obj M

private noncomputable def pullbackIdMod {Z X : Scheme.{u}} (j : Z ⟶ X) [IsImmersion j] :
    Z.Modules :=
  (modulePullback (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).obj (Stacks.Conormal.conormalSheaf j)

private theorem homEquiv_id_zero {Z : Scheme.{u}} (M N : Z.Modules) :
    (modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).homEquiv M N
        (0 : pullbackIdObj M ⟶ N) = (0 : M ⟶ N) :=
  (Adjunction.homEquiv_unit _ _ _ _).trans comp_zero

private noncomputable abbrev regularClass {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : Opens i.coborderRange.toScheme)
    (s : (definingIdeal i).toSheafOfModules.val.obj (op V)) :
    (regularConormalMod i).val.obj (op (i.liftCoborder ⁻¹ᵁ V)) :=
  ((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
    ((definingIdeal i).toSheafOfModules)).val.app (op V) s

private noncomputable abbrev coborderClass {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : Opens i.coborderRange.toScheme)
    (t : (idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj (op V)) :
    (conormalMod i).val.obj (op (i.liftCoborder ⁻¹ᵁ V)) :=
  ((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
    (idealSheaf i.liftCoborder.toLRSHom.toShHom)).val.app (op V) t

/-- the germ of the conormal class of a defining-ideal section, after comparison. -/
private noncomputable abbrev germRegularClass {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (z : Z) (V : Opens i.coborderRange.toScheme) (hzV : i.liftCoborder.base z ∈ V)
    (s : (definingIdeal i).toSheafOfModules.val.obj (op V)) :
    ToType ((stalkAb Z z).obj (conormalMod i)) :=
  TopCat.Presheaf.germ (C := Ab.{u}) (conormalMod i).val.presheaf (i.liftCoborder ⁻¹ᵁ V) z hzV
    ((conormalSheafComparisonIso i).hom.val.app (op (i.liftCoborder ⁻¹ᵁ V)) (regularClass i V s))

section Bridge

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

private theorem conormalSheafComparisonIso_hom_regularClass
    (V : Opens i.coborderRange.toScheme)
    (s : (definingIdeal i).toSheafOfModules.val.obj (op V)) :
    (conormalSheafComparisonIso i).hom.val.app (op (i.liftCoborder ⁻¹ᵁ V)) (regularClass i V s) =
      coborderClass i V ((Stacks.AlgebraicGeometry.kernelSubmoduleIso
        (structureSheafModuleHom i.liftCoborder.toLRSHom.toShHom)).hom.val.app (op V) s) :=
  (congr($((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.naturality
    (Stacks.AlgebraicGeometry.kernelSubmoduleIso
      (structureSheafModuleHom i.liftCoborder.toLRSHom.toShHom)).hom).val.app (op V) s)).symm

private theorem idealSection_kernelSubmoduleIso_hom (V : Opens i.coborderRange.toScheme)
    (s : (definingIdeal i).toSheafOfModules.val.obj (op V)) :
    Stacks.Conormal.idealSection i.liftCoborder V
        ((Stacks.AlgebraicGeometry.kernelSubmoduleIso
          (structureSheafModuleHom i.liftCoborder.toLRSHom.toShHom)).hom.val.app (op V) s) =
      s.1 :=
  congr($(Stacks.AlgebraicGeometry.kernelSubmoduleIso_hom_comp_ι
    (structureSheafModuleHom i.liftCoborder.toLRSHom.toShHom)).val.app (op V) s)

/-- **The cotangent class of the germ of a conormal class of a defining-ideal section.** -/
private theorem conormalSheafStalkEquivCotangent_germRegularClass (z : Z)
    (V : Opens i.coborderRange.toScheme) (hzV : i.liftCoborder.base z ∈ V)
    (s : (definingIdeal i).toSheafOfModules.val.obj (op V)) :
    Stacks.Conormal.conormalSheafStalkEquivCotangent i z (germRegularClass i z V hzV s) =
      (RingHom.ker (i.liftCoborder.stalkMap z).hom).toCotangent
        ⟨i.coborderRange.toScheme.presheaf.germ V (i.liftCoborder.base z) hzV s.1,
          germ_mem_ker_stalkMap i.liftCoborder z V hzV s⟩ := by
  refine Eq.trans (congrArg (Stacks.Conormal.conormalSheafStalkEquivCotangent i z)
    (congrArg (TopCat.Presheaf.germ (C := Ab.{u}) (conormalMod i).val.presheaf
      (i.liftCoborder ⁻¹ᵁ V) z hzV) (conormalSheafComparisonIso_hom_regularClass i V s))) ?_
  refine (Stacks.Conormal.conormalSheafStalkEquivCotangent_germ i z V hzV _).trans ?_
  refine congrArg (Ideal.toCotangent _) (Subtype.ext ?_)
  exact congrArg (fun c => (i.coborderRange.toScheme.presheaf.germ V
    (i.liftCoborder.base z) hzV) c) (idealSection_kernelSubmoduleIso_hom i V s)

/-- **Every conormal class is a conormal class of the closed factor, on germs.** -/
private theorem exists_germRegularClass_eq (z : Z) (A : X.Opens) (hA : z ∈ i ⁻¹ᵁ A)
    (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op A)) :
    ∃ (V : Opens i.coborderRange.toScheme) (hzV : i.liftCoborder.base z ∈ V)
      (s : (definingIdeal i).toSheafOfModules.val.obj (op V)),
      i.coborderRange.toScheme.presheaf.germ V (i.liftCoborder.base z) hzV s.1 =
          (Stacks.Conormal.coborderStalkEquiv i z).hom.hom
            (X.presheaf.germ A (i.base z) hA (Stacks.Conormal.idealSection i A y)) ∧
        TopCat.Presheaf.germ (C := Ab.{u}) (conormalMod i).val.presheaf (i ⁻¹ᵁ A) z hA
            ((canonicalConormalQuotientMap i).val.app (op A) y) =
          germRegularClass i z V hzV s := by
  obtain ⟨V, hzV, s, hgerm⟩ := exists_germ_eq_of_mem_ker i.liftCoborder z _
    (Stacks.Conormal.coborderStalkEquiv_mem_ker i z _
      (Stacks.Conormal.germ_idealSection_mem_ker_stalkMap i z A hA y))
  refine ⟨V, hzV, s, hgerm, (Stacks.Conormal.conormalSheafStalkEquivCotangent i z).injective ?_⟩
  refine (Stacks.Conormal.germ_canonicalConormalQuotientMap i z A hA y).trans ?_
  refine Eq.trans ?_ (conormalSheafStalkEquivCotangent_germRegularClass i z V hzV s).symm
  exact congrArg (Ideal.toCotangent _) (Subtype.ext hgerm.symm)

end Bridge

section SecondArrow

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ Y)

/-- **The second arrow of the sequence of Tag 067L**, read on the conormal sheaf in the
categorical-kernel presentation. -/
private noncomputable def secondArrow :
    conormalMod i ⟶ (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) :=
  (conormalSheafComparisonIso i).inv ≫ conormalDifferential i p

/-- the second arrow carries the conormal class of a defining-ideal section `s` to `1 ⊗ d s`. -/
private theorem stalkAb_secondArrow_germRegularClass (z : Z)
    (V : Opens i.coborderRange.toScheme) (hzV : i.liftCoborder.base z ∈ V)
    (s : (definingIdeal i).toSheafOfModules.val.obj (op V)) :
    (stalkAb Z z).map (secondArrow i p) (germRegularClass i z V hzV s) =
      (stalkAb Z z).map (coborderPullbackDifferentialsIso i p).hom
        (TopCat.Presheaf.germ (C := Ab.{u})
          ((Scheme.Modules.pullback i.liftCoborder).obj
            (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.presheaf
          (i.liftCoborder ⁻¹ᵁ V) z hzV
          (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
              (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.app (op V)
            ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d s.1))) := by
  have hcancel : (conormalSheafComparisonIso i).hom ≫ secondArrow i p =
      conormalDifferential i p :=
    Iso.hom_inv_id_assoc (conormalSheafComparisonIso i) (conormalDifferential i p)
  refine Eq.trans (stalkAb_map_germ (secondArrow i p) z (i.liftCoborder ⁻¹ᵁ V) hzV _) ?_
  refine Eq.trans ?_ (stalkAb_map_germ (coborderPullbackDifferentialsIso i p).hom z
    (i.liftCoborder ⁻¹ᵁ V) hzV _).symm
  refine congrArg (TopCat.Presheaf.germ (C := Ab.{u})
    ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
    (i.liftCoborder ⁻¹ᵁ V) z hzV) ?_
  refine Eq.trans (congrArg (fun m => (m.val.app (op (i.liftCoborder ⁻¹ᵁ V))).hom
    (regularClass i V s)) hcancel) ?_
  exact congrArg (fun m => (m.val.app (op V)).hom s)
    (conormalComparison_comp_conormalDifferential i p)

/-- **The second arrow is an epimorphism once the conormal differential is.** The comparison of
the two presentations is an isomorphism, so it transfers surjectivity. -/
private theorem epi_secondArrow (hcd : Epi (conormalDifferential i p)) : Epi (secondArrow i p) :=
  epi_comp' (IsIso.epi_of_iso (conormalSheafComparisonIso i).inv) hcd

end SecondArrow

section Realization

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- the stalk map of an immersion carries the inverse coborder identification of `b` to the
stalk map of the closed factor at `b`. -/
private theorem stalkMap_coborderStalkEquiv_inv_apply (z : Z)
    (b : ToType (i.coborderRange.toScheme.presheaf.stalk (i.liftCoborder.base z))) :
    (i.stalkMap z).hom ((Stacks.Conormal.coborderStalkEquiv i z).inv.hom b) =
      (i.liftCoborder.stalkMap z).hom b := by
  rw [← Stacks.Conormal.stalkMap_coborderStalkEquiv i z,
    Iso.inv_hom_id_apply (Stacks.Conormal.coborderStalkEquiv i z) b]

/-- the stalk map of an immersion is surjective. -/
private theorem stalkMap_surjective_of_isImmersion (z : Z) :
    Function.Surjective (i.stalkMap z).hom := by
  intro c
  obtain ⟨b, hb⟩ := i.liftCoborder.stalkMap_surjective z c
  exact ⟨_, (stalkMap_coborderStalkEquiv_inv_apply i z b).trans hb⟩

/-- **Every element of a stalk of the conormal sheaf is the conormal class of a section of the
defining ideal of the closed factor.** -/
private theorem exists_eq_germRegularClass (z : Z)
    (m : ToType ((stalkAb Z z).obj (conormalMod i))) :
    ∃ (V : Opens i.coborderRange.toScheme) (hzV : i.liftCoborder.base z ∈ V)
      (s : (definingIdeal i).toSheafOfModules.val.obj (op V)),
      m = germRegularClass i z V hzV s := by
  obtain ⟨w, hw⟩ := Ideal.toCotangent_surjective (RingHom.ker (i.liftCoborder.stalkMap z).hom)
    (Stacks.Conormal.conormalSheafStalkEquivCotangent i z m)
  obtain ⟨V, hzV, s, hgerm⟩ := exists_germ_eq_of_mem_ker i.liftCoborder z w.1 w.2
  refine ⟨V, hzV, s, (Stacks.Conormal.conormalSheafStalkEquivCotangent i z).injective ?_⟩
  refine Eq.trans hw.symm (Eq.trans ?_
    (conormalSheafStalkEquivCotangent_germRegularClass i z V hzV s).symm)
  exact congrArg (Ideal.toCotangent _) (Subtype.ext hgerm.symm)

end Realization

section Triangle

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)
  [IsImmersion i] [IsImmersion j]

omit [IsImmersion i] [IsImmersion j] in
private theorem preimage_eq_of_triangle (h : i ≫ p = j) (A : Y.Opens) :
    j ⁻¹ᵁ A = i ⁻¹ᵁ (p ⁻¹ᵁ A) := by
  change _ = (i ≫ p) ⁻¹ᵁ A
  rw [h]

/-- **A section of the ideal sheaf of `g` pulls back along `q` to one of the ideal sheaf of `f`.**
The triangle makes the pullback of the section vanish on the source. -/
private theorem exists_idealSheaf_section_map {S T U : Scheme.{u}} (f : S ⟶ T) (g : S ⟶ U)
    (q : T ⟶ U) (h : f ≫ q = g) (A : U.Opens)
    (y : (idealSheaf g.toLRSHom.toShHom).val.obj (op A)) :
    ∃ E : (idealSheaf f.toLRSHom.toShHom).val.obj (op (q ⁻¹ᵁ A)),
      (idealSheafι f.toLRSHom.toShHom).val.app (op (q ⁻¹ᵁ A)) E =
        (Scheme.Hom.app q A).hom ((idealSheafι g.toLRSHom.toShHom).val.app (op A) y) := by
  refine exists_idealSheaf_section_of_app_eq_zero f.toLRSHom.toShHom (q ⁻¹ᵁ A) _ ?_
  change ((f ≫ q).app A).hom _ = 0
  rw [h]
  exact Stacks.Conormal.AffineCotangent.Sections.app_idealSheaf_section_eq_zero g A y

/-- the first arrow of Tag 067L before the identity-pullback is cancelled. -/
private noncomputable def firstArrowPullback (h : i ≫ p = j) :
    pullbackIdMod j ⟶ conormalMod i :=
  immersionConormalSheafMap i j (𝟙 Z) p (toShHom_square (h.trans (Category.id_comp j).symm))

/-- **The first arrow carries the conormal class of a section `y` of the ideal sheaf of `j` to
the conormal class of any section of the ideal sheaf of `i` lying over `p^♯ y`.** -/
private theorem stalkAb_firstArrowPullback_germ (h : i ≫ p = j) (z : Z) (A : Y.Opens)
    (hA : z ∈ j ⁻¹ᵁ A)
    (y : (idealSheaf j.toLRSHom.toShHom).val.obj (op A))
    (E : (idealSheaf i.toLRSHom.toShHom).val.obj (op (p ⁻¹ᵁ A)))
    (hE : (idealSheafι i.toLRSHom.toShHom).val.app (op (p ⁻¹ᵁ A)) E =
      (Scheme.Hom.app p A).hom ((idealSheafι j.toLRSHom.toShHom).val.app (op A) y)) :
    (stalkAb Z z).map (firstArrowPullback i j p h)
        (TopCat.Presheaf.germ (C := Ab.{u}) (pullbackIdMod j).val.presheaf
          ((𝟙 Z) ⁻¹ᵁ (j ⁻¹ᵁ A)) z hA
          (((modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).unit.app
              (Stacks.Conormal.conormalSheaf j)).val.app (op (j ⁻¹ᵁ A))
            ((canonicalConormalQuotientMap j).val.app (op A) y))) =
      TopCat.Presheaf.germ (C := Ab.{u}) (conormalMod i).val.presheaf (i ⁻¹ᵁ (p ⁻¹ᵁ A)) z
        (le_of_eq (preimage_eq_of_triangle i j p h A) hA)
        ((canonicalConormalQuotientMap i).val.app (op (p ⁻¹ᵁ A)) E) := by
  have hcomm : i ≫ p = 𝟙 Z ≫ j := h.trans (Category.id_comp j).symm
  have hC : (j ⁻¹ᵁ A) ≤ i ⁻¹ᵁ (p ⁻¹ᵁ A) := le_of_eq (preimage_eq_of_triangle i j p h A)
  have hC' : (j ⁻¹ᵁ A) ≤ (𝟙 Z) ⁻¹ᵁ (j ⁻¹ᵁ A) := le_rfl
  have hD := Stacks.Conormal.conormalClass_homEquiv_immersionConormalSheafMap i j (𝟙 Z) p hcomm
    A (j ⁻¹ᵁ A) hC hC' y E hE
  have hhe := congr($(Adjunction.homEquiv_unit
      (adj := modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom)
      (f := firstArrowPullback i j p h)).val.app
    (op (j ⁻¹ᵁ A)) ((canonicalConormalQuotientMap j).val.app (op A) y))
  refine (stalkAb_map_germ (firstArrowPullback i j p h) z
    ((𝟙 Z) ⁻¹ᵁ (j ⁻¹ᵁ A)) (hC' hA) _).trans ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := Ab.{u}) (conormalMod i).val.presheaf
      ((𝟙 Z) ⁻¹ᵁ (j ⁻¹ᵁ A)) z (hC' hA)) hhe.symm) ?_
  refine (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) (conormalMod i).val.presheaf
      (homOfLE hC') z hA _).symm.trans ?_
  refine (congrArg (TopCat.Presheaf.germ (C := Ab.{u}) (conormalMod i).val.presheaf
      (j ⁻¹ᵁ A) z hA) hD).trans ?_
  exact TopCat.Presheaf.germ_res_apply (C := Ab.{u}) (conormalMod i).val.presheaf
    (homOfLE hC) z hA _

end Triangle

section Tower

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ Y)

/-- the identification with the local ring of the coborder carries the pullback of a section of
`𝒪_Y` to its image under the stalk map of the coborder neighbourhood over `Y`. -/
private theorem coborderStalkEquiv_germ_app (z : Z) (A : Y.Opens) (hA : i.base z ∈ p ⁻¹ᵁ A)
    (hA' : i.liftCoborder.base z ∈ i.coborderRange.ι ⁻¹ᵁ (p ⁻¹ᵁ A)) (a : Γ(Y, A)) :
    (Stacks.Conormal.coborderStalkEquiv i z).hom.hom
        (X.presheaf.germ (p ⁻¹ᵁ A) (i.base z) hA ((p.app A).hom a)) =
      ((i.coborderRange.ι ≫ p).stalkMap (i.liftCoborder.base z)).hom
        (Y.presheaf.germ A ((i.coborderRange.ι ≫ p).base (i.liftCoborder.base z)) hA' a) := by
  rw [Scheme.Hom.germ_stalkMap_apply (i.coborderRange.ι ≫ p) A (i.liftCoborder.base z) hA' a]
  exact Stacks.Conormal.coborderStalkEquiv_germ i z (p ⁻¹ᵁ A) hA hA' ((p.app A).hom a)

/-- **The second arrow kills the conormal class of a section pulled back from the base.** The
second arrow sends that class to `1 ⊗ d (p^♯ a)`, and the universal derivation over `Y` kills
a section pulled back along `p`. -/
private theorem secondArrow_canonicalConormalQuotientMap_eq_zero (A : Y.Opens) (a : Γ(Y, A))
    (E : (idealSheaf i.toLRSHom.toShHom).val.obj (op (p ⁻¹ᵁ A)))
    (hE : (idealSheafι i.toLRSHom.toShHom).val.app (op (p ⁻¹ᵁ A)) E = (p.app A).hom a) :
    (secondArrow i p).val.app (op (i ⁻¹ᵁ (p ⁻¹ᵁ A)))
        ((canonicalConormalQuotientMap i).val.app (op (p ⁻¹ᵁ A)) E) = 0 := by
  classical
  refine TopCat.Presheaf.section_ext
    (⟨((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf,
      ((Scheme.Modules.pullback i).obj
        (Scheme.Hom.relativeDifferentials p)).isSheaf⟩ : TopCat.Sheaf Ab.{u} Z)
    (i ⁻¹ᵁ (p ⁻¹ᵁ A)) _ _ fun z hz => ?_
  let R : Type u :=
    ToType (Y.presheaf.stalk ((i.coborderRange.ι ≫ p).base (i.liftCoborder.base z)))
  let B : Type u := ToType (i.coborderRange.toScheme.presheaf.stalk (i.liftCoborder.base z))
  let C : Type u := ToType (Z.presheaf.stalk z)
  let : Algebra R B := algebraStalkMap (i.coborderRange.ι ≫ p) (i.liftCoborder.base z)
  let : Algebra B C := (i.liftCoborder.stalkMap z).hom.toAlgebra
  let : Algebra R C := algebraStalkMap (i.liftCoborder ≫ (i.coborderRange.ι ≫ p)) z
  let : IsScalarTower R B C :=
    Scheme.Hom.isScalarTower_stalkMap i.liftCoborder (i.coborderRange.ι ≫ p) z
  obtain ⟨V, hzV, s, hgermV, hclass⟩ := exists_germRegularClass_eq i z (p ⁻¹ᵁ A) hz E
  obtain ⟨eM, heMgerm, -⟩ := Scheme.Hom.exists_relativeDifferentialsPullbackStalkEquiv
    i.liftCoborder (i.coborderRange.ι ≫ p) z
  have hmemcob := Stacks.Conormal.mem_coborder_preimage i z (p ⁻¹ᵁ A) hz
  have hgerm_s : i.coborderRange.toScheme.presheaf.germ V (i.liftCoborder.base z) hzV s.1 =
      algebraMap R B (Y.presheaf.germ A
        ((i.coborderRange.ι ≫ p).base (i.liftCoborder.base z)) hmemcob a) := by
    refine hgermV.trans ?_
    refine Eq.trans (congrArg (fun c => (Stacks.Conormal.coborderStalkEquiv i z).hom.hom
      ((X.presheaf.germ (p ⁻¹ᵁ A) (i.base z) hz) c)) hE) ?_
    exact coborderStalkEquiv_germ_app i p z A hz hmemcob a
  have hzero : TopCat.Presheaf.germ (C := Ab.{u})
      ((Scheme.Modules.pullback i.liftCoborder).obj
        (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.presheaf
      (i.liftCoborder ⁻¹ᵁ V) z hzV
      (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
          (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.app (op V)
        ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d s.1)) = 0 := by
    refine eM.injective (Eq.trans ((heMgerm V hzV s.1).trans ?_) (map_zero eM).symm)
    refine Eq.trans (congrArg (fun x => (1 : C) ⊗ₜ[B] (KaehlerDifferential.D R B x)) hgerm_s) ?_
    refine Eq.trans (congrArg (fun y => (1 : C) ⊗ₜ[B] y)
      ((KaehlerDifferential.D R B).map_algebraMap _)) ?_
    exact TensorProduct.tmul_zero _ _
  refine Eq.trans (stalkAb_map_germ (secondArrow i p) z (i ⁻¹ᵁ (p ⁻¹ᵁ A)) hz _).symm ?_
  refine Eq.trans ?_ (map_zero _).symm
  rw [hclass, stalkAb_secondArrow_germRegularClass i p z V hzV s, hzero]
  exact map_zero _

private theorem stalkAb_map_comp_apply {Z : Scheme.{u}} {M N P : Z.Modules} (f : M ⟶ N)
    (g : N ⟶ P) (z : Z) (x : ToType ((stalkAb Z z).obj M)) :
    (stalkAb Z z).map g ((stalkAb Z z).map f x) = (stalkAb Z z).map (f ≫ g) x :=
  (ConcreteCategory.congr_hom (Functor.map_comp (stalkAb Z z) f g) x).symm

private theorem stalkAb_map_id_apply {Z : Scheme.{u}} {M : Z.Modules} (z : Z)
    (x : ToType ((stalkAb Z z).obj M)) : (stalkAb Z z).map (𝟙 M) x = x :=
  ConcreteCategory.congr_hom (CategoryTheory.Functor.map_id (stalkAb Z z) M) x

private theorem stalkAb_map_inv_map_hom {Z : Scheme.{u}} {M N : Z.Modules} {f : M ⟶ N}
    {g : N ⟶ M} (hfg : f ≫ g = 𝟙 M) (z : Z) (x : ToType ((stalkAb Z z).obj M)) :
    (stalkAb Z z).map g ((stalkAb Z z).map f x) = x :=
  (stalkAb_map_comp_apply f g z x).trans
    ((congrArg (fun t => ((stalkAb Z z).map t) x) hfg).trans (stalkAb_map_id_apply z x))

/-- **Exactness at the middle term of the sequence of Tag 067L, on stalks.** -/
private theorem exists_stalkAb_firstArrowPullback_eq (j : Z ⟶ Y) [IsImmersion j]
    (h : i ≫ p = j) (z : Z) (m : ToType ((stalkAb Z z).obj (conormalMod i)))
    (hm : (stalkAb Z z).map (secondArrow i p) m = 0) :
    ∃ l, (stalkAb Z z).map (firstArrowPullback i j p h) l = m := by
  classical
  let R : Type u :=
    ToType (Y.presheaf.stalk ((i.coborderRange.ι ≫ p).base (i.liftCoborder.base z)))
  let B : Type u := ToType (i.coborderRange.toScheme.presheaf.stalk (i.liftCoborder.base z))
  let C : Type u := ToType (Z.presheaf.stalk z)
  let : Algebra R B := algebraStalkMap (i.coborderRange.ι ≫ p) (i.liftCoborder.base z)
  let : Algebra B C := (i.liftCoborder.stalkMap z).hom.toAlgebra
  let : Algebra R C := algebraStalkMap (i.liftCoborder ≫ (i.coborderRange.ι ≫ p)) z
  let : IsScalarTower R B C :=
    Scheme.Hom.isScalarTower_stalkMap i.liftCoborder (i.coborderRange.ι ≫ p) z
  have hqj : i.liftCoborder ≫ (i.coborderRange.ι ≫ p) = j := by
    rw [← Category.assoc, i.liftCoborder_ι, h]
  have : IsImmersion (i.liftCoborder ≫ (i.coborderRange.ι ≫ p)) := hqj ▸ ‹IsImmersion j›
  have hsurjRC : Function.Surjective (algebraMap R C) :=
    stalkMap_surjective_of_isImmersion (i.liftCoborder ≫ (i.coborderRange.ι ≫ p)) z
  have hle : RingHom.ker (algebraMap R C) ≤
      Ideal.comap (Algebra.ofId R B) (RingHom.ker (algebraMap B C)) := by
    intro r hr
    rw [RingHom.mem_ker] at hr
    rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.ofId_apply, ← IsScalarTower.algebraMap_apply]
    exact hr
  obtain ⟨V₀, hzV₀, s₀, hm0⟩ := exists_eq_germRegularClass i z m
  obtain ⟨eM, heMgerm, -⟩ := Scheme.Hom.exists_relativeDifferentialsPullbackStalkEquiv
    i.liftCoborder (i.coborderRange.ι ≫ p) z
  have hem : Stacks.Conormal.conormalSheafStalkEquivCotangent i z m =
      (RingHom.ker (i.liftCoborder.stalkMap z).hom).toCotangent
        ⟨i.coborderRange.toScheme.presheaf.germ V₀ (i.liftCoborder.base z) hzV₀ s₀.1,
          germ_mem_ker_stalkMap i.liftCoborder z V₀ hzV₀ s₀⟩ :=
    (congrArg (Stacks.Conormal.conormalSheafStalkEquivCotangent i z) hm0).trans
      (conormalSheafStalkEquivCotangent_germRegularClass i z V₀ hzV₀ s₀)
  -- the second arrow kills `m`, so the universal differential of `s₀` dies in the stalk
  have hdzero : TopCat.Presheaf.germ (C := Ab.{u})
      ((Scheme.Modules.pullback i.liftCoborder).obj
        (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.presheaf
      (i.liftCoborder ⁻¹ᵁ V₀) z hzV₀
      (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
          (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.app (op V₀)
        ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d s₀.1)) = 0 := by
    have hmid : (stalkAb Z z).map (coborderPullbackDifferentialsIso i p).hom _ = 0 :=
      ((stalkAb_secondArrow_germRegularClass i p z V₀ hzV₀ s₀).symm.trans
        (congrArg ((stalkAb Z z).map (secondArrow i p)) hm0.symm)).trans hm
    refine (stalkAb_map_inv_map_hom
      (coborderPullbackDifferentialsIso i p).hom_inv_id z _).symm.trans ?_
    exact (congrArg ((stalkAb Z z).map (coborderPullbackDifferentialsIso i p).inv) hmid).trans
      (map_zero _)
  have hker : KaehlerDifferential.kerCotangentToTensor R B C
      (Stacks.Conormal.conormalSheafStalkEquivCotangent i z m) = 0 := by
    refine Eq.trans (congrArg (KaehlerDifferential.kerCotangentToTensor R B C) hem) ?_
    refine Eq.trans (KaehlerDifferential.kerCotangentToTensor_toCotangent R B C _) ?_
    refine Eq.trans (heMgerm V₀ hzV₀ s₀.1).symm ?_
    exact (congrArg eM hdzero).trans (map_zero eM)
  obtain ⟨v, hv⟩ := ((exact_mapCotangent_kerCotangentToTensor_and_surjective
    R B C hsurjRC hle).1 _).mp hker
  obtain ⟨yy, hyy⟩ := Ideal.toCotangent_surjective (RingHom.ker (algebraMap R C)) v
  obtain ⟨A, hA, sy, hsy⟩ :=
    exists_germ_eq_of_mem_ker (i.liftCoborder ≫ (i.coborderRange.ι ≫ p)) z yy.1 yy.2
  have hAj : z ∈ j ⁻¹ᵁ A := hqj ▸ hA
  have hzi : z ∈ i ⁻¹ᵁ (p ⁻¹ᵁ A) := le_of_eq (preimage_eq_of_triangle i j p h A) hAj
  have h0 : (structureSheafModuleHom j.toLRSHom.toShHom).val.app (op A) sy.1 = 0 := by
    rw [← hqj]; exact sy.2
  obtain ⟨y, hyeq⟩ := exists_idealSheaf_section_of_app_eq_zero j.toLRSHom.toShHom A sy.1 h0
  obtain ⟨E, hE⟩ := exists_idealSheaf_section_map i j p h A y
  have hEeq := hE.trans (congrArg (fun c => (p.app A).hom c) hyeq)
  have hmv : Stacks.Conormal.conormalSheafStalkEquivCotangent i z m =
      (RingHom.ker (i.liftCoborder.stalkMap z).hom).toCotangent
        ⟨Algebra.ofId R B yy.1, hle yy.2⟩ :=
    hv.symm.trans ((congrArg (Ideal.mapCotangent (RingHom.ker (algebraMap R C))
      (RingHom.ker (algebraMap B C)) (Algebra.ofId R B) hle) hyy.symm).trans
      (Ideal.mapCotangent_toCotangent _ _ _ _ yy))
  have hmemcob := Stacks.Conormal.mem_coborder_preimage i z (p ⁻¹ᵁ A) hzi
  refine ⟨_, (stalkAb_firstArrowPullback_germ i j p h z A hAj y E hE).trans ?_⟩
  refine (Stacks.Conormal.conormalSheafStalkEquivCotangent i z).injective ?_
  refine (Stacks.Conormal.germ_canonicalConormalQuotientMap i z (p ⁻¹ᵁ A) hzi E).trans ?_
  refine Eq.trans ?_ hmv.symm
  refine congrArg (Ideal.toCotangent _) (Subtype.ext ?_)
  refine Eq.trans (congrArg (fun c => (Stacks.Conormal.coborderStalkEquiv i z).hom.hom
    ((X.presheaf.germ (p ⁻¹ᵁ A) (i.base z) hzi) c)) hEeq) ?_
  refine (coborderStalkEquiv_germ_app i p z A hzi hmemcob sy.1).trans ?_
  exact congrArg (fun c => algebraMap R B c) hsy


end Tower

/-- **Every element of a stalk of the conormal sheaf is the conormal class of a section of the
ideal sheaf of the immersion itself.** -/
private theorem exists_eq_germ_canonicalConormalQuotientMap {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsImmersion f] (z : Z) (m : ToType ((stalkAb Z z).obj (conormalMod f))) :
    ∃ (A : X.Opens) (hA : z ∈ f ⁻¹ᵁ A)
      (y : (idealSheaf f.toLRSHom.toShHom).val.obj (op A)),
      m = TopCat.Presheaf.germ (C := Ab.{u}) (conormalMod f).val.presheaf (f ⁻¹ᵁ A) z hA
        ((canonicalConormalQuotientMap f).val.app (op A) y) := by
  obtain ⟨w, hw⟩ := Ideal.toCotangent_surjective (RingHom.ker (f.liftCoborder.stalkMap z).hom)
    (Stacks.Conormal.conormalSheafStalkEquivCotangent f z m)
  have hc : (Stacks.Conormal.coborderStalkEquiv f z).inv.hom w.1 ∈
      RingHom.ker (f.stalkMap z).hom := by
    rw [RingHom.mem_ker, stalkMap_coborderStalkEquiv_inv_apply f z w.1]
    exact w.2
  obtain ⟨A, hA, sj, hsj⟩ := exists_germ_eq_of_mem_ker f z _ hc
  obtain ⟨y, hyeq⟩ := exists_idealSheaf_section_of_app_eq_zero f.toLRSHom.toShHom A sj.1 sj.2
  refine ⟨A, hA, y, (Stacks.Conormal.conormalSheafStalkEquivCotangent f z).injective ?_⟩
  refine Eq.trans hw.symm (Eq.trans ?_
    (Stacks.Conormal.germ_canonicalConormalQuotientMap f z A hA y).symm)
  refine congrArg (Ideal.toCotangent _) (Subtype.ext ?_)
  refine Eq.symm (Eq.trans (congrArg (fun c => (Stacks.Conormal.coborderStalkEquiv f z).hom.hom
    ((X.presheaf.germ A (f.base z) hA) c)) hyeq) ?_)
  exact (congrArg (fun c => (Stacks.Conormal.coborderStalkEquiv f z).hom.hom c) hsj).trans
    (Iso.inv_hom_id_apply (Stacks.Conormal.coborderStalkEquiv f z) w.1)

section Transpose

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)
  [IsImmersion i] [IsImmersion j]

/-- the first arrow of Tag 067L, transposed along the identity adjunction. -/
private noncomputable def firstArrowTranspose (h : i ≫ p = j) : conormalMod j ⟶ conormalMod i :=
  (modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).homEquiv _ _
    (firstArrowPullback i j p h)

private theorem stalkAb_firstArrowTranspose_germ (h : i ≫ p = j) (z : Z) (A : Y.Opens)
    (hA : z ∈ j ⁻¹ᵁ A)
    (y : (idealSheaf j.toLRSHom.toShHom).val.obj (op A))
    (E : (idealSheaf i.toLRSHom.toShHom).val.obj (op (p ⁻¹ᵁ A)))
    (hE : (idealSheafι i.toLRSHom.toShHom).val.app (op (p ⁻¹ᵁ A)) E =
      (Scheme.Hom.app p A).hom ((idealSheafι j.toLRSHom.toShHom).val.app (op A) y)) :
    (stalkAb Z z).map (firstArrowTranspose i j p h)
        (TopCat.Presheaf.germ (C := Ab.{u}) (conormalMod j).val.presheaf (j ⁻¹ᵁ A) z hA
          ((canonicalConormalQuotientMap j).val.app (op A) y)) =
      TopCat.Presheaf.germ (C := Ab.{u}) (conormalMod i).val.presheaf (i ⁻¹ᵁ (p ⁻¹ᵁ A)) z
        (le_of_eq (preimage_eq_of_triangle i j p h A) hA)
        ((canonicalConormalQuotientMap i).val.app (op (p ⁻¹ᵁ A)) E) := by
  have hhe := congr($(Adjunction.homEquiv_unit
      (adj := modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom)
      (f := firstArrowPullback i j p h)).val.app
    (op (j ⁻¹ᵁ A)) ((canonicalConormalQuotientMap j).val.app (op A) y))
  refine (stalkAb_map_germ (firstArrowTranspose i j p h) z (j ⁻¹ᵁ A) hA _).trans ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := Ab.{u}) (conormalMod i).val.presheaf
      (j ⁻¹ᵁ A) z hA) hhe) ?_
  exact (stalkAb_map_germ (firstArrowPullback i j p h) z _ hA _).symm.trans
    (stalkAb_firstArrowPullback_germ i j p h z A hA y E hE)

/-- **The two arrows of the sequence of Tag 067L compose to zero**, with the first arrow in its
transposed spelling. -/
private theorem firstArrowTranspose_comp_secondArrow_eq_zero (h : i ≫ p = j) :
    firstArrowTranspose i j p h ≫ secondArrow i p = 0 := by
  refine hom_eq_zero_of_stalk _ fun z m => ?_
  obtain ⟨A, hA, y, hm⟩ := exists_eq_germ_canonicalConormalQuotientMap j z m
  obtain ⟨E, hEeq⟩ := exists_idealSheaf_section_map i j p h A y
  have hzi : z ∈ i ⁻¹ᵁ (p ⁻¹ᵁ A) := le_of_eq (preimage_eq_of_triangle i j p h A) hA
  refine Eq.trans (congrArg ((stalkAb Z z).map (firstArrowTranspose i j p h ≫ secondArrow i p))
    hm) ?_
  refine Eq.trans (stalkAb_map_comp_apply (firstArrowTranspose i j p h) (secondArrow i p) z _).symm
    ?_
  refine Eq.trans (congrArg ((stalkAb Z z).map (secondArrow i p))
    (stalkAb_firstArrowTranspose_germ i j p h z A hA y E hEeq)) ?_
  refine (stalkAb_map_germ (secondArrow i p) z (i ⁻¹ᵁ (p ⁻¹ᵁ A)) hzi _).trans ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := Ab.{u})
    ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
    (i ⁻¹ᵁ (p ⁻¹ᵁ A)) z hzi)
    (secondArrow_canonicalConormalQuotientMap_eq_zero i p A _ E hEeq)) ?_
  exact map_zero _

/-- **The first arrow of the sequence of Tag 067L**, with its two ends ascribed in the category of
modules over the scheme. -/
private noncomputable def firstArrow (h : i ≫ p = j) : conormalMod j ⟶ conormalMod i :=
  Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i j p h

/-- **[Stacks, Tag 067L]: the two arrows of the conormal sequence compose to zero.** -/
private theorem firstArrow_comp_secondArrow_eq_zero (h : i ≫ p = j) :
    firstArrow i j p h ≫ secondArrow i p = 0 := by
  have h0 := homEquiv_id_zero (conormalMod j)
    ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p))
  have hψ : firstArrowPullback i j p h ≫ secondArrow i p = 0 :=
    (modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).homEquiv _ _
      |>.injective
      (((Adjunction.homEquiv_naturality_right
        (adj := modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom)
        (firstArrowPullback i j p h) (secondArrow i p)).trans
        (firstArrowTranspose_comp_secondArrow_eq_zero i j p h)).trans h0.symm)
  refine Eq.trans (Category.assoc
    ((Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).inv.app
      (Stacks.Conormal.conormalSheaf j)) (firstArrowPullback i j p h) (secondArrow i p)) ?_
  exact (congrArg (fun t => (Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).inv.app
    (Stacks.Conormal.conormalSheaf j) ≫ t) hψ).trans comp_zero

/-- **[Stacks, Tag 067L]: the conormal sequence of two immersions is exact at its middle
term.** -/
private theorem conormalShortComplexTwo_exact (h : i ≫ p = j) :
    (ShortComplex.mk (firstArrow i j p h) (secondArrow i p)
      (firstArrow_comp_secondArrow_eq_zero i j p h)).Exact := by
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact Z.ringCatSheaf
    (ShortComplex.mk (firstArrow i j p h) (secondArrow i p)
      (firstArrow_comp_secondArrow_eq_zero i j p h))).2 fun z => ?_
  refine (ShortComplex.ab_exact_iff _).2 fun m hm => ?_
  obtain ⟨l, hl⟩ := exists_stalkAb_firstArrowPullback_eq i p j h z m hm
  refine ⟨(stalkAb Z z).map ((Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).hom.app
    (Stacks.Conormal.conormalSheaf j)) l, ?_⟩
  refine Eq.trans (stalkAb_map_comp_apply
    ((Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).inv.app
      (Stacks.Conormal.conormalSheaf j)) (firstArrowPullback i j p h) z _).symm ?_
  refine Eq.trans (congrArg ((stalkAb Z z).map (firstArrowPullback i j p h))
    (stalkAb_map_inv_map_hom
      ((Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).hom_inv_id_app
        (Stacks.Conormal.conormalSheaf j)) z l)) hl


/-- the two arrows compose to zero after any postcomposition, in the spelling the sequence of
Tag 067V uses. -/
private theorem firstArrow_comp_eq_zero (h : i ≫ p = j) {T : Z.Modules}
    (ε : (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) ⟶ T)
    (F : conormalMod j ⟶ conormalMod i) (hF : F = firstArrow i j p h) :
    F ≫ ((conormalSheafComparisonIso i).inv ≫ conormalDifferential i p ≫ ε) = 0 := by
  subst hF
  have h0 : firstArrow i j p h ≫ secondArrow i p = 0 :=
    firstArrow_comp_secondArrow_eq_zero i j p h
  refine Eq.trans (congrArg (fun t : conormalMod i ⟶ T => firstArrow i j p h ≫ t)
    (show (conormalSheafComparisonIso i).inv ≫ conormalDifferential i p ≫ ε =
      secondArrow i p ≫ ε from (Category.assoc _ _ _).symm)) ?_
  exact ((Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ ε) h0)).trans zero_comp

/-- **[Stacks, Tag 067L]: exactness at the middle term**, in the spelling the sequence of
Tag 067V uses. -/
private theorem shortComplex_comp_exact (h : i ≫ p = j) {T : Z.Modules}
    (ε : (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) ≅ T)
    (F : conormalMod j ⟶ conormalMod i) (hF : F = firstArrow i j p h)
    (hz : F ≫ ((conormalSheafComparisonIso i).inv ≫ conormalDifferential i p ≫ ε.hom) = 0) :
    (ShortComplex.mk F ((conormalSheafComparisonIso i).inv ≫
      conormalDifferential i p ≫ ε.hom) hz).Exact := by
  subst hF
  have hS := conormalShortComplexTwo_exact i j p h
  refine ShortComplex.exact_of_iso ?_ hS
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) ε ?_ ?_
  · simp
  · refine Eq.trans ?_ (Category.assoc _ _ _).symm
    simp [secondArrow]

end Transpose

end TwoImmersions

/-! ### The three assertions of Tag 067V -/

/-- **[Stacks, Tag 067V]: the two arrows form a complex.** The composite
`𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` vanishes. -/
@[stacks 067V "the composite of the two arrows 𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} vanishes, so the
two arrows form a complex"]
theorem conormalSequenceComp_eq_zero (h : i ≫ p = j) :
    conormalSequenceFirstArrow i j p h ≫ conormalSequenceSecondArrow i j p h = 0 :=
  firstArrow_comp_eq_zero (universalFirstOrderThickening i).inclusion
    (universalFirstOrderThickening j).inclusion (thickeningComparison i j p h)
    (inclusion_comp_thickeningComparison i j p h) (thirdTermIso i j p h).inv
    (conormalSequenceFirstArrow i j p h)
    (universalConormalTransitivityMap_eq_conormalTransitivityMap i j p h)

/-- **[Stacks, Tag 067V]: the second arrow is an epimorphism.** This is the `⟶ 0` at the
right-hand end of the sequence. -/
@[stacks 067V "surjectivity of the second arrow 𝒞_{Z/X} ⟶ i^*Ω_{X/Y}, which is the ⟶ 0 at the
right-hand end of the sequence"]
theorem epi_conormalSequenceSecondArrow (h : i ≫ p = j) :
    Epi (conormalSequenceSecondArrow i j p h) := by
  have hsa : Epi (secondArrow (universalFirstOrderThickening i).inclusion
      (thickeningComparison i j p h)) :=
    epi_secondArrow (universalFirstOrderThickening i).inclusion (thickeningComparison i j p h)
      (Stacks.ConormalSequenceTwoImmersions.epi_conormalDifferential
        (universalFirstOrderThickening i).inclusion (universalFirstOrderThickening j).inclusion
        (thickeningComparison i j p h) (inclusion_comp_thickeningComparison i j p h))
  have h0 : Epi (thirdTermIso i j p h).inv := IsIso.epi_of_iso _
  change Epi (secondArrow (universalFirstOrderThickening i).inclusion
    (thickeningComparison i j p h) ≫ (thirdTermIso i j p h).inv)
  exact epi_comp' hsa h0

/-- **[Stacks, Tag 067V]: the sequence is exact at `𝒞_{Z/X}`.** The kernel of the second arrow is
the image of the first. -/
@[stacks 067V "exactness at the middle term 𝒞_{Z/X}: the kernel of the second arrow is the image
of the first"]
theorem conormalSequenceShortComplex_exact (h : i ≫ p = j) :
    (ShortComplex.mk _ _ (conormalSequenceComp_eq_zero i j p h)).Exact :=
  shortComplex_comp_exact (universalFirstOrderThickening i).inclusion
    (universalFirstOrderThickening j).inclusion (thickeningComparison i j p h)
    (inclusion_comp_thickeningComparison i j p h) (thirdTermIso i j p h).symm
    (conormalSequenceFirstArrow i j p h)
    (universalConormalTransitivityMap_eq_conormalTransitivityMap i j p h)
    (conormalSequenceComp_eq_zero i j p h)

/-! ### The split short exact sequence -/

/-- **[Stacks, Tag 067W]: the conormal sequence is short exact.** For formally unramified
`i : Z ⟶ X` and `j : Z ⟶ Y` in a commutative triangle `i ≫ p = j` with `p` formally smooth, the
sequence `0 ⟶ 𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0` of [Stacks, Tag 067V] is short exact.

Exactness at the middle term and surjectivity of the second arrow are the assertions of
[Stacks, Tag 067V]; what this tag adds is injectivity of the first arrow. -/
@[stacks 067W "the sequence of Tag 067V is short exact: exactness at the middle term and
surjectivity of the second arrow are the assertions of Tag 067V, and injectivity of the first
arrow is what this tag adds, by way of the local splitting its proof produces"]
theorem shortExact_of_comp_eq_zero_of_exact (h : i ≫ p = j) (hp : FormallySmooth p) :
    (ShortComplex.mk _ _ (conormalSequenceComp_eq_zero i j p h)).ShortExact where
  exact := conormalSequenceShortComplex_exact i j p h
  mono_f := mono_conormalSequenceFirstArrow i j p h hp
  epi_g := epi_conormalSequenceSecondArrow i j p h

end Stacks.ConormalSequenceUnramifiedPair

/-! ### The two remaining clauses of Tag 067L -/

namespace Stacks.ConormalSequenceTwoImmersions

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)
  [IsImmersion i] [IsImmersion j]

/-- **The conormal sheaf of an immersion, as an object of `Z.Modules`.** This is
`Stacks.Conormal.conormalSheaf` with its type declared to be
`AlgebraicGeometry.Scheme.Modules Z`, which is the category the sheaf of relative differentials
lives in. -/
def immersionConormalSheafModules : Z.Modules := Stacks.Conormal.conormalSheaf i

/-- **The first arrow `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of [Stacks, Tag 067L]**, with both ends in the
spelling `Stacks.ConormalSequenceTwoImmersions.immersionConormalSheafModules`. It is
`Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap`. -/
def conormalTransitivityMapModules (h : i ≫ p = j) :
    immersionConormalSheafModules j ⟶ immersionConormalSheafModules i :=
  conormalTransitivityMap i j p h

/-- **The second arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` of [Stacks, Tag 067L]**, with its source in the
spelling the first arrow uses. The conormal differential of [Stacks, Tag 01UZ] is built on the
pullback of a *sectionwise* kernel and the first arrow on the pullback of the *categorical*
kernel; `Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso` identifies the two
presentations, and this arrow is the conormal differential read through it. -/
@[stacks 067L "the second arrow 𝒞_{Z/X} ⟶ i^*Ω_{X/Y}, in the spelling that composes with the
first arrow: the conormal differential of Tag 01UZ for i over p, read through the identification
conormalSheafComparisonIso of the two presentations of 𝒞_{Z/X}"]
def conormalDifferentialModules :
    immersionConormalSheafModules i ⟶
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) :=
  (Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso i).inv ≫
    Stacks.ConormalSequenceRight.conormalDifferential i p

/-- **[Stacks, Tag 067L]: the two arrows of the conormal sequence form a complex.** The composite
`𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` vanishes, for immersions `i : Z ⟶ X` and `j : Z ⟶ Y` in a
commutative triangle `i ≫ p = j` and with no hypothesis on `p`. -/
@[stacks 067L "the composite 𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} of the two arrows vanishes, so they
form a complex; only the commutative triangle i ≫ p = j of immersions is assumed"]
theorem conormalTransitivityMapModules_comp_eq_zero (h : i ≫ p = j) :
    conormalTransitivityMapModules i j p h ≫ conormalDifferentialModules i p = 0 :=
  Stacks.ConormalSequenceUnramifiedPair.firstArrow_comp_secondArrow_eq_zero i j p h

/-- **[Stacks, Tag 067L]: the conormal sequence of two immersions is exact at `𝒞_{Z/X}`.** The
kernel of the second arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` is exactly the image of the first arrow
`𝒞_{Z/Y} ⟶ 𝒞_{Z/X}`, for immersions `i : Z ⟶ X` and `j : Z ⟶ Y` in a commutative triangle
`i ≫ p = j` and with no hypothesis on `p`. -/
@[stacks 067L "exactness at the middle term 𝒞_{Z/X}: the image of the first arrow
𝒞_{Z/Y} ⟶ 𝒞_{Z/X} is the kernel of the second arrow 𝒞_{Z/X} ⟶ i^*Ω_{X/Y}; only the commutative
triangle i ≫ p = j of immersions is assumed"]
theorem conormalShortComplexModules_exact (h : i ≫ p = j) :
    (ShortComplex.mk _ _
      (conormalTransitivityMapModules_comp_eq_zero i j p h)).Exact :=
  Stacks.ConormalSequenceUnramifiedPair.conormalShortComplexTwo_exact i j p h

end Stacks.ConormalSequenceTwoImmersions

end

