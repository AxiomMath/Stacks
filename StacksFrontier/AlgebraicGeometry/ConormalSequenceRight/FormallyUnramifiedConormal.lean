module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalDifferentials
public import StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairSplitConormalSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of a formally unramified morphism

Let `h : Z ⟶ X` be a formally unramified morphism of schemes over `p : X ⟶ S`.
[Stacks, Tag 04FC] asserts that the sequence

`𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0`

of `𝒪_Z`-modules is exact, the first arrow being induced by the universal derivation `d_{Z'/S}`
on the ambient scheme `Z'` of the universal first-order thickening of `Z` over `X`.

This file constructs that first arrow and proves exactness at the middle term. Exactness at the
right term is `Stacks.ConormalSequenceRight.epi_relativeDifferentialsMap_of_formallyUnramified`
of `StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.FormallyUnramified`.

## Main definitions

* `Stacks.ConormalSequenceRight.universalThickeningDifferentialsIso`: the isomorphism
  `ι^*Ω_{Z'/S} ≅ h^*Ω_{X/S}` supplied by [Stacks, Tag 04FB].
* `Stacks.ConormalSequenceRight.universalConormalDifferential`: the first arrow
  `𝒞_{Z/X} ⟶ h^*Ω_{X/S}`.
* `Stacks.ConormalSequenceRight.universalConormalShortComplex`: the two arrows, packaged.

## Main results

* `Stacks.ConormalSequenceRight.universalConormalShortComplex_exact`: exactness at the middle
  term, which is the assertion [Stacks, Tag 04FC] makes beyond the vanishing of the composite.
* `Stacks.ConormalSequenceRight.epi_universalConormalShortComplex_g`: the sequence ends in zero.

## Route

This is the source's own proof. Write `Z'` for the ambient scheme of the universal first-order
thickening `Stacks.Thickenings.universalFirstOrderThickening h` of `Z` over `X`, `ι : Z ⟶ Z'`
for its inclusion and `h' : Z' ⟶ X` for its structure morphism, so that `ι ≫ h' = h`. The
inclusion is a closed immersion, hence an immersion, so [Stacks, Tag 01UZ] applies to it over
the base morphism `h' ≫ p` and gives the exact sequence

`𝒞_{Z/Z'} ⟶ ι^*Ω_{Z'/S} ⟶ Ω_{Z/S} ⟶ 0`,

which is `Stacks.ConormalSequenceRight.conormalShortComplex` together with
`Stacks.ConormalSequenceRight.conormalShortComplex_exact`. Its left-hand term is `𝒞_{Z/X}` by
the definition [Stacks, Tag 04F4] makes, and its middle term is carried onto `h^*Ω_{X/S}` by
[Stacks, Tag 04FB]. Exactness transports along that isomorphism of short complexes.

Three identifications are needed to make the transport typecheck, and each is a renaming rather
than mathematical content.

* The left-hand term. The library realizes the conormal sheaf of an immersion twice, as the
  pullback of a sectionwise kernel and as the pullback of a categorical kernel;
  [Stacks, Tag 01UZ] is built on the first and [Stacks, Tag 04F4] on the second. They are
  identified by `Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso`.
* The middle term. `universalThickeningDifferentialsIso` assembles the isomorphism of
  [Stacks, Tag 04FB] with the pseudofunctoriality isomorphism `ι^*(h')^* ≅ (ι ≫ h')^* = h^*`.
* The right-hand term. [Stacks, Tag 01UZ] states its second arrow with target
  `Ω_{Z/S}` presented as the relative differentials of `ι ≫ (h' ≫ p)`, whereas the sequence of
  [Stacks, Tag 04FC] presents the same morphism as `h ≫ p`. The two morphisms of schemes are
  equal but not syntactically so, and `relativeDifferentialsMap_comp_eqToHom` moves the
  canonical map of [Stacks, Tag 01UV] between the two presentations of its target.

## References

* [Stacks Project, Tag 04FC](https://stacks.math.columbia.edu/tag/04FC)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
* [Stacks Project, Tag 04FB](https://stacks.math.columbia.edu/tag/04FB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ConormalSequenceRight

/-- **The canonical map of [Stacks, Tag 01UV] does not depend on how its target is presented.**
Two equal morphisms `r = r'` out of the source give the same sheaf of relative differentials,
and the canonical maps into the two presentations differ by the resulting `eqToHom`. -/
theorem relativeDifferentialsMap_comp_eqToHom {Z X S : Scheme.{u}} (f : Z ⟶ X) (p : X ⟶ S)
    {r r' : Z ⟶ S} (hrr : r = r') (g g' : S ⟶ S) (hc : f ≫ p = r ≫ g) (hc' : f ≫ p = r' ≫ g') :
    Scheme.Hom.relativeDifferentialsMap f p r g hc ≫
        eqToHom (congrArg (fun q : Z ⟶ S => Scheme.Hom.relativeDifferentials q) hrr) =
      Scheme.Hom.relativeDifferentialsMap f p r' g' hc' := by
  subst hrr
  simpa using Scheme.Hom.relativeDifferentialsMap_eq_of_comm g g' hc hc'

open Stacks.Thickenings

variable {Z X S : Scheme.{u}} (h : Z ⟶ X) [FormallyUnramified h] (p : X ⟶ S)

/-- The inclusion of `Z` into the ambient scheme of its universal first-order thickening,
followed by the restriction of the base morphism, is `h ≫ p`. -/
theorem inclusion_comp_toBase_comp :
    (universalFirstOrderThickening h).inclusion ≫
      ((universalFirstOrderThickening h).toBase ≫ p) = h ≫ p := by
  rw [← Category.assoc, (universalFirstOrderThickening h).isUniversal.inclusion_toBase]

/-- The commutative square over the identity of `S` that the inclusion into the universal
first-order thickening sits in. -/
theorem inclusion_comp_toBase_comp' :
    (universalFirstOrderThickening h).inclusion ≫
      ((universalFirstOrderThickening h).toBase ≫ p) = (h ≫ p) ≫ 𝟙 S := by
  rw [inclusion_comp_toBase_comp h p, Category.comp_id]

/-- **[Stacks, Tag 04FB] as an identification of the middle term.** For the universal
first-order thickening `ι : Z ⟶ Z'` of `h : Z ⟶ X` with structure morphism `h' : Z' ⟶ X`, the
restriction along `ι` of the canonical map `(h')^*Ω_{X/S} ⟶ Ω_{Z'/S}` is an isomorphism, so
`ι^*Ω_{Z'/S}` is `ι^*(h')^*Ω_{X/S} = h^*Ω_{X/S}`. -/
noncomputable def universalThickeningDifferentialsIso :
    (Scheme.Modules.pullback (universalFirstOrderThickening h).inclusion).obj
        (Scheme.Hom.relativeDifferentials
          ((universalFirstOrderThickening h).toBase ≫ p)) ≅
      (Scheme.Modules.pullback h).obj (Scheme.Hom.relativeDifferentials p) :=
  haveI := Stacks.Thickenings.isIso_thickeningRelativeDifferentialsMap
    (universalFirstOrderThickening h).isUniversal p
  (asIso (Scheme.Hom.thickeningRelativeDifferentialsMap
        (universalFirstOrderThickening h).inclusion
        (universalFirstOrderThickening h).toBase p)).symm ≪≫
    (Scheme.Modules.pullbackComp (universalFirstOrderThickening h).inclusion
        (universalFirstOrderThickening h).toBase).app _ ≪≫
      (Scheme.Modules.pullbackCongr
        (universalFirstOrderThickening h).isUniversal.inclusion_toBase).app _

/-- **The identification of the middle term carries the second arrow of the sequence of
[Stacks, Tag 04FC] to the second arrow of the sequence of [Stacks, Tag 01UZ] for `ι` over
`h' ≫ p`.** Both are the canonical map of [Stacks, Tag 01UV], and the composite of the two
canonical maps of the stacked square is the canonical map of its outer square. -/
theorem universalThickeningDifferentialsIso_inv_comp :
    (universalThickeningDifferentialsIso h p).inv ≫
        Scheme.Hom.relativeDifferentialsMap (universalFirstOrderThickening h).inclusion
          ((universalFirstOrderThickening h).toBase ≫ p) (h ≫ p) (𝟙 S)
          (inclusion_comp_toBase_comp' h p) =
      Scheme.Hom.relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp) := by
  have hb := Scheme.Hom.isRelativeDifferentialsMap_relativeDifferentialsMap
    (universalFirstOrderThickening h).toBase p
    ((universalFirstOrderThickening h).toBase ≫ p) (𝟙 S) (by simp)
  have hi := Scheme.Hom.isRelativeDifferentialsMap_relativeDifferentialsMap
    (universalFirstOrderThickening h).inclusion
    ((universalFirstOrderThickening h).toBase ≫ p) (h ≫ p) (𝟙 S)
    (inclusion_comp_toBase_comp' h p)
  refine Eq.trans ?_ (((hb.comp hi).congr_left
    (universalFirstOrderThickening h).isUniversal.inclusion_toBase).eq_relativeDifferentialsMap
      (𝟙 S) (by simp))
  simp [universalThickeningDifferentialsIso,
    Scheme.Hom.thickeningRelativeDifferentialsMap]

/-- The same identity read on the other side of the identification. -/
theorem universalThickeningDifferentialsIso_hom_comp :
    (universalThickeningDifferentialsIso h p).hom ≫
        Scheme.Hom.relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp) =
      Scheme.Hom.relativeDifferentialsMap (universalFirstOrderThickening h).inclusion
        ((universalFirstOrderThickening h).toBase ≫ p) (h ≫ p) (𝟙 S)
        (inclusion_comp_toBase_comp' h p) := by
  rw [← universalThickeningDifferentialsIso_inv_comp h p, Iso.hom_inv_id_assoc]

/-- **The conormal sheaf of the inclusion into the universal first-order thickening, as an
object of `Z.Modules`.** This is the left-hand term of the sequence of [Stacks, Tag 01UZ] for
that inclusion, in the sectionwise-kernel presentation the conormal differential of that tag is
built on. Declaring its type to be `AlgebraicGeometry.Scheme.Modules Z` is what lets it sit in a
composite next to a sheaf of relative differentials; the reason is the one spelled out in
`StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairConormalSequence`. -/
noncomputable abbrev idealConormalModules : Z.Modules :=
  Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf
    (universalFirstOrderThickening h).inclusion

/-- **The two presentations of `𝒞_{Z/X}` agree**, read in `Z.Modules`. This is
`Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso` at the inclusion into the
universal first-order thickening. -/
noncomputable def idealConormalModulesIso :
    idealConormalModules h ≅ Stacks.ConormalSequenceUnramifiedPair.conormalSheafModules h :=
  Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso
    (universalFirstOrderThickening h).inclusion

/-- **The first arrow of [Stacks, Tag 01UZ] for the inclusion into the universal first-order
thickening**, read in `Z.Modules`. This is
`Stacks.ConormalSequenceRight.conormalDifferential` at `ι` over `h' ≫ p`. -/
noncomputable def idealConormalFirstArrow :
    idealConormalModules h ⟶
      (Scheme.Modules.pullback (universalFirstOrderThickening h).inclusion).obj
        (Scheme.Hom.relativeDifferentials ((universalFirstOrderThickening h).toBase ≫ p)) :=
  conormalDifferential (universalFirstOrderThickening h).inclusion
    ((universalFirstOrderThickening h).toBase ≫ p)

/-- The two arrows of [Stacks, Tag 01UZ] for the inclusion into the universal first-order
thickening compose to zero. -/
theorem idealConormalFirstArrow_comp_relativeDifferentialsMap :
    idealConormalFirstArrow h p ≫
      Scheme.Hom.relativeDifferentialsMap (universalFirstOrderThickening h).inclusion
        ((universalFirstOrderThickening h).toBase ≫ p)
        ((universalFirstOrderThickening h).inclusion ≫
          ((universalFirstOrderThickening h).toBase ≫ p)) (𝟙 S) (by simp) = 0 :=
  (conormalShortComplex (universalFirstOrderThickening h).inclusion
    ((universalFirstOrderThickening h).toBase ≫ p)).zero

/-- **The first arrow, out of the sectionwise-kernel presentation of the conormal sheaf.** It is
the first arrow of [Stacks, Tag 01UZ] for the closed immersion `ι : Z ⟶ Z'` over `h' ≫ p`, with
its target moved onto `h^*Ω_{X/S}` by [Stacks, Tag 04FB]. -/
noncomputable def idealConormalDifferential :
    idealConormalModules h ⟶
      (Scheme.Modules.pullback h).obj (Scheme.Hom.relativeDifferentials p) :=
  idealConormalFirstArrow h p ≫ (universalThickeningDifferentialsIso h p).hom

/-- The first arrow, followed by the second, vanishes. The composite is the one of
[Stacks, Tag 01UZ] for `ι` over `h' ≫ p`, whose target has only been renamed. -/
theorem idealConormalDifferential_comp_relativeDifferentialsMap :
    idealConormalDifferential h p ≫
      Scheme.Hom.relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp) = 0 := by
  rw [idealConormalDifferential, Category.assoc,
    universalThickeningDifferentialsIso_hom_comp,
    ← relativeDifferentialsMap_comp_eqToHom (universalFirstOrderThickening h).inclusion
      ((universalFirstOrderThickening h).toBase ≫ p) (inclusion_comp_toBase_comp h p)
      (𝟙 S) (𝟙 S) (by simp) (inclusion_comp_toBase_comp' h p),
    ← Category.assoc, idealConormalFirstArrow_comp_relativeDifferentialsMap, zero_comp]

/-- **[Stacks, Tag 04FC], the first arrow.** For a formally unramified morphism `h : Z ⟶ X` of
schemes over `S`, the canonical morphism `𝒞_{Z/X} ⟶ h^*Ω_{X/S}` induced by the universal
derivation `d_{Z'/S}` on the ambient scheme of the universal first-order thickening of `Z` over
`X`.

It is the first arrow of [Stacks, Tag 01UZ] for the closed immersion `ι : Z ⟶ Z'` over
`h' ≫ p`, whose source is the conormal sheaf of `ι`, that is `𝒞_{Z/X}` by the definition
[Stacks, Tag 04F4] makes, and whose target is moved onto `h^*Ω_{X/S}` by [Stacks, Tag 04FB]. -/
@[stacks 04FC "the first arrow induced by the universal derivation"]
noncomputable def universalConormalDifferential :
    Stacks.ConormalSequenceUnramifiedPair.conormalSheafModules h ⟶
      (Scheme.Modules.pullback h).obj (Scheme.Hom.relativeDifferentials p) :=
  (idealConormalModulesIso h).inv ≫ idealConormalDifferential h p

/-- **[Stacks, Tag 04FC], the two arrows form a complex.** The composite
`𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S}` vanishes, because the corresponding composite of
[Stacks, Tag 01UZ] for the inclusion into the universal first-order thickening does. -/
theorem universalConormalDifferential_comp_relativeDifferentialsMap :
    universalConormalDifferential h p ≫
      Scheme.Hom.relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp) = 0 := by
  rw [universalConormalDifferential, Category.assoc,
    idealConormalDifferential_comp_relativeDifferentialsMap, comp_zero]

/-- **[Stacks, Tag 04FC], the conormal sequence of a formally unramified morphism**
`h : Z ⟶ X` over `S`, as a short complex `𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S}` of
`𝒪_Z`-modules. -/
noncomputable def universalConormalShortComplex : ShortComplex Z.Modules :=
  ShortComplex.mk (universalConormalDifferential h p)
    (Scheme.Hom.relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp))
    (universalConormalDifferential_comp_relativeDifferentialsMap h p)

/-- **The conormal sequence of `h` is the conormal sequence of the inclusion into the universal
first-order thickening.** The three identifications are the comparison of the two presentations
of the conormal sheaf, the isomorphism of [Stacks, Tag 04FB] and the renaming of
`ι ≫ (h' ≫ p)` as `h ≫ p`. -/
noncomputable def universalConormalShortComplexIso :
    conormalShortComplex (universalFirstOrderThickening h).inclusion
        ((universalFirstOrderThickening h).toBase ≫ p) ≅
      universalConormalShortComplex h p :=
  ShortComplex.isoMk (idealConormalModulesIso h) (universalThickeningDifferentialsIso h p)
    (eqToIso (congrArg (fun q : Z ⟶ S => Scheme.Hom.relativeDifferentials q)
      (inclusion_comp_toBase_comp h p)))
    (by
      dsimp only [universalConormalShortComplex, conormalShortComplex,
        universalConormalDifferential, idealConormalDifferential]
      exact Iso.hom_inv_id_assoc _ _)
    (by
      dsimp only [universalConormalShortComplex, conormalShortComplex]
      exact (universalThickeningDifferentialsIso_hom_comp h p).trans
        (relativeDifferentialsMap_comp_eqToHom (universalFirstOrderThickening h).inclusion
          ((universalFirstOrderThickening h).toBase ≫ p) (inclusion_comp_toBase_comp h p)
          (𝟙 S) (𝟙 S) (by simp) (inclusion_comp_toBase_comp' h p)).symm)

/-- **[Stacks, Tag 04FC], exactness at the middle term.** For a formally unramified morphism
`h : Z ⟶ X` of schemes over `S` the sequence `𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S}` is exact at
`h^*Ω_{X/S}`.

This is [Stacks, Tag 01UZ] for the closed immersion of `Z` into the ambient scheme of its
universal first-order thickening over `X`, transported along the identifications of
`Stacks.ConormalSequenceRight.universalConormalShortComplexIso`. -/
@[stacks 04FC "exactness at the middle term", sga "7 XI 1.3" "partial"]
theorem universalConormalShortComplex_exact :
    (universalConormalShortComplex h p).Exact :=
  ShortComplex.exact_of_iso (universalConormalShortComplexIso h p)
    (conormalShortComplex_exact (universalFirstOrderThickening h).inclusion
      ((universalFirstOrderThickening h).toBase ≫ p))

/-- **The conormal sequence of a formally unramified morphism ends in zero**, which is
`Stacks.ConormalSequenceRight.epi_relativeDifferentialsMap_of_formallyUnramified` read on the
short complex. -/
theorem epi_universalConormalShortComplex_g :
    Epi (universalConormalShortComplex h p).g :=
  epi_relativeDifferentialsMap_of_formallyUnramified h p

/-! ### Faithfulness

One `example` per labelled assertion, stating it over library names. The tagged statement of
[Stacks, Tag 04FC] writes the conormal sheaf as `Stacks.Thickenings.universalConormalSheaf` and
the sheaves of differentials as the module of differentials (Tag 08RM) of the inverse image of
the structure map (Tag 01SA); the library name for
the latter is `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, as recorded in
`StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic`. -/

/-- `04FC "the first arrow induced by the universal derivation"`: a morphism from the conormal
sheaf of the formally unramified morphism to the pullback of the relative differentials of the
target. -/
noncomputable example :
    Stacks.Thickenings.universalConormalSheaf h ⟶
      (Scheme.Modules.pullback h).obj (Scheme.Hom.relativeDifferentials p) :=
  universalConormalDifferential h p

/-- `04FC "exactness at the middle term"`: the two arrows compose to zero and the sequence they
form is exact at the pulled-back relative differentials. -/
example :
    ∃ hc : universalConormalDifferential h p ≫
        Scheme.Hom.relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp) = 0,
      (ShortComplex.mk (universalConormalDifferential h p)
        (Scheme.Hom.relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp)) hc).Exact :=
  ⟨universalConormalDifferential_comp_relativeDifferentialsMap h p,
    universalConormalShortComplex_exact h p⟩

end Stacks.ConormalSequenceRight

end
