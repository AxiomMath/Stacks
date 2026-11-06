module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersionEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of differentials of an immersion of algebraic spaces vanishes

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  Stacks 05Z9 asserts that
`Ω_{X/Y}` is zero when `f` is an immersion.

The source's displayed statement writes `Ω_{X/S}`, which cannot be what is meant — the identity
of the affine line over a field is an immersion with nonvanishing `Ω_{X/S}` — and the scheme
lemma it reduces to, Morphisms, Lemma 01UY, reads "if `X → S` is an immersion, or more generally
a monomorphism, then `Ω_{X/S}` is zero" with `S` the *target* of the immersion.  The subscript
there names the immersion itself, and `S` is reused in the spaces chapter for the base scheme; the
statement is read here as `Ω_{X/Y}`, the sheaf of differentials of the immersion, which is also
what the source's proof produces.

The vanishing is proved unconditionally, in two halves.

* Local surjectivity of the structure map forces the vanishing, by the universal property of
  `Ω_{X/Y}`: a `Y`-derivation kills the image of `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` and commutes with
  restriction, so if `f♯` is locally surjective then every `Y`-derivation into a *sheaf* of
  `𝒪_X`-modules vanishes locally on every section, hence vanishes, the target being separated;
  and `Ω_{X/Y}` corepresents the functor of `Y`-derivations
  (`AlgebraicGeometry.Space.universalDerivation_isUniversal`), so every endomorphism of
  `Ω_{X/Y}` is then determined by the same derivation, forcing `𝟙 = 0`.
* The structure map of an immersion *is* locally surjective, which is proved below.

## Local surjectivity of the structure map of an immersion

The inverse-image form `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` is by construction the adjunct of the direct-image
form `f♯ : 𝒪_Y ⟶ f_*𝒪_X` under `f⁻¹ ⊣ f_*`, so on underlying sheaves of sets it is
`f⁻¹(f♯) ≫ ε` for the counit `ε : f⁻¹f_*𝒪_X ⟶ 𝒪_X`
(`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget`).  For a *closed* immersion all
three factors are controlled:

* `ε` is invertible.  The small étale direct image of a closed immersion is fully faithful, which
  is part (1) of Stacks 04E5
  (`AlgebraicGeometry.Space.isEmbedding_smallToposMorphismTypeU`), i.e. the morphism of topoi is
  an embedding in the sense of Stacks 08LU, and the counit of an embedding is an isomorphism
  (`MorphismOfTopoi.isEmbedding_iff_isIso_counit_app`).
* `f♯` in direct-image form is locally surjective: that is the surjectivity clause of
  Stacks 03MB, `AlgebraicGeometry.Space.isLocallySurjective_structureSharp`.
* `f⁻¹` preserves epimorphisms, being a left adjoint.

A general immersion is reduced to that case by Stacks 04CE: it factors as a closed immersion
`c` into the complement of the boundary of its image followed by the inclusion `a` of that open
subspace, and an open immersion is étale
(`AlgebraicGeometry.Space.immersionClosedFactorization_comp_immersionAmbientInclusion`,
`AlgebraicGeometry.Space.isClosedImmersion_boundaryComplementLift`,
`AlgebraicGeometry.Space.isEtale_immersionAmbientInclusion`).  The étale-base comparison of
Stacks 04CU identifies `(c ≫ a)♯` with `c♯` up to an isomorphism of the source
(`AlgebraicGeometry.Space.etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage`),
so local surjectivity transfers from `c` to `c ≫ a`.

## Why this is not the source's route

The source reduces to the scheme case, Morphisms, Lemma 01UY, by the étale localization of
Stacks 04CU.  That route needs the *final sentence* of Stacks 04CU — the identification of
`Ω_{U/V}` for a morphism of schemes with the usual, Zariski, sheaf of differentials — which is
the comparison of Stacks 04CS and is available in this development only as a map, not as an
isomorphism (`AlgebraicGeometry.SmallEtale.differentialsComparison` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentials.lean`).  The same
gap is what Stacks 04G9 carries as `AlgebraicGeometry.Space.SheafOfDifferentialsChartComparison`
and what Stacks 04CV carries as `hschemeChart`.  The comparison proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsEtaleComparison.lean` is a different
statement — that the identification of Stacks 04CU is the comparison map of Stacks 04CX, hence
that that map is invertible along an étale morphism — and does not supply it.  The route taken
here does not need it: the étale-base step of Stacks 04CU that it does use,
`etaleBaseInverseImageStructureSheafIso`, is proved outright from Stacks 03G8 and the clause
`b⁻¹𝒪_Y = 𝒪_V` of Stacks 03LV.

## Main results

* `AlgebraicGeometry.RingedToposHom.isLocallySurjective_fSharpInverseImage`: for a morphism of
  ringed topoi which is an embedding of topoi and whose direct-image structure map is locally
  surjective, the inverse-image structure map is locally surjective.
* `AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage_of_isClosedImmersion`:
  the inverse-image form of the structure map of a closed immersion of algebraic spaces is
  locally surjective.
* `AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage_of_isImmersion`: the
  same for an immersion — the inverse-image form of the surjectivity clause of Stacks 03MB.
* `AlgebraicGeometry.Space.derivation_d_eq_zero_of_isLocallySurjective`: a `Y`-derivation into a
  sheaf of `𝒪_X`-modules kills every section of `𝒪_X` when `f♯` is locally surjective.
* `AlgebraicGeometry.Space.derivation_eq_of_isLocallySurjective`: consequently there is at most
  one `Y`-derivation into any given sheaf of `𝒪_X`-modules.
* `AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_isLocallySurjective`: **Stacks 05Z9**,
  the vanishing itself, from local surjectivity of `f♯`.
* `AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_isImmersion`: **Stacks 05Z9** as the
  source states it, carrying local surjectivity of the structure map of an immersion as the
  hypothesis `hsharp`.
* `AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_isImmersion_unconditional`: the same
  with `hsharp` discharged — for an immersion and with no further hypothesis.

## Implementation notes

Separatedness of the target is Mathlib's `CategoryTheory.Presheaf.IsSheaf.isSeparated`, which
needs the sheaf condition at the topology `AlgebraicGeometry.Space.SmallEtale.topology` rather
than at the projection `(AlgebraicGeometry.Space.smallEtaleRingedSite ‹_›).J` to which it is
definitionally equal; the two readings carry different `CategoryTheory.Category` instance terms
on the same category, so the restriction maps of the module are compared by `Eq.trans` on
`have`-statements rather than rewritten, which would elaborate at the other reading.

`AlgebraicGeometry.RingedToposHom.isLocallySurjective_fSharpInverseImage` is stated for an
abstract morphism of ringed topoi rather than inlined at the small étale ringed topos hom of a
morphism of algebraic spaces.  Its proof rewrites the goal by
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget`, and at the small étale spelling the
two sides of that equation are large enough that the rewrite exhausts the default heartbeat
budget; stated generically the same rewrite is cheap, and no `maxHeartbeats` has to be raised.

Local surjectivity of a morphism of sheaves of commutative rings is by definition that of the
underlying morphism of sheaves of sets, and `Presheaf.isLocallySurjective_iff_whisker_forget` is
the passage between the two readings; `AlgebraicGeometry.RingedTopos.forgetRing` is the forgetful
functor of `CommRingCat` factored through `RingCat`, which is how the structure map of a
`RingedToposHom` is typed.

## References

* [Stacks Project, Tag 05Z9](https://stacks.math.columbia.edu/tag/05Z9)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces and its universal derivation.
* [Stacks Project, Tag 01UY](https://stacks.math.columbia.edu/tag/01UY), the scheme case, which
  the source reduces to.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), whose surjectivity
  clause is proved here in its inverse-image form.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map of a
  morphism of algebraic spaces in its two adjunct forms.
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE), the factorisation of an
  immersion as a closed immersion into an open subspace.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1), full
  faithfulness of the small étale direct image along a closed immersion.
* [Stacks Project, Tag 08LU](https://stacks.math.columbia.edu/tag/08LU), embeddings of topoi.
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV), the clause
  `b⁻¹𝒪_Y = 𝒪_V` for an étale `b`.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  of the sheaf of differentials, whose étale-base step is used.
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the
  differentials of a morphism of schemes on its small Zariski and small étale sites, which the
  source's own route would need and this one does not.
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU), part (5), immersions of
  algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w v' u' w'

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- The inverse image of a morphism of topoi preserves epimorphisms of sheaves of sets, being a
left adjoint: an epimorphism may be cancelled on the left after transposing along `f⁻¹ ⊣ f_*`. -/
theorem inverseImage_map_epi (f : RingedToposHom X Y)
    {F G : Sheaf Y.J (Type w')} (g : F ⟶ G) (hg : Epi g) :
    Epi (f.toToposHom.inverseImage.map g) := by
  refine ⟨fun {T} u v huv => ?_⟩
  have h1 : g ≫ f.toToposHom.adj.homEquiv _ T u = g ≫ f.toToposHom.adj.homEquiv _ T v := by
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left, huv]
  exact (f.toToposHom.adj.homEquiv _ T).injective ((cancel_epi g).1 h1)

/-- If the underlying morphism of topoi of a morphism of ringed topoi is an embedding and its
direct-image structure map `f♯ : O_D ⟶ f_*O_C` is locally surjective, then its inverse-image
structure map `f♯ : f⁻¹O_D ⟶ O_C` is locally surjective.

On underlying sheaves of sets the inverse-image form is `f⁻¹(f♯) ≫ ε` for the counit `ε` of
`f⁻¹ ⊣ f_*`, by `AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget`.  The first factor
is an epimorphism because `f⁻¹` is a left adjoint and a locally surjective morphism of sheaves of
sets is an epimorphism; the second is an isomorphism because the counit of an embedding of topoi
is one. -/
theorem isLocallySurjective_fSharpInverseImage [HasSheafify X.J (Type w)]
    (f : RingedToposHom X Y) (hemb : f.toToposHom.IsEmbedding)
    (hsurj : Sheaf.IsLocallySurjective (Y.forgetRing.map f.fSharp)) :
    Sheaf.IsLocallySurjective (X.forgetRing.map f.fSharpInverseImage) := by
  have hL : Epi (f.toToposHom.inverseImage.map (Y.forgetRing.map f.fSharp)) :=
    inverseImage_map_epi f _ (Sheaf.epi_of_isLocallySurjective _)
  have hiso : IsIso (f.toToposHom.adj.counit.app (X.forgetRing.obj X.O)) :=
    (MorphismOfTopoi.isEmbedding_iff_isIso_counit_app f.toToposHom).1 hemb _
  have hepi2 : Epi (f.toToposHom.adj.counit.app (X.forgetRing.obj X.O)) := inferInstance
  refine (Sheaf.isLocallySurjective_iff_epi _).2 ?_
  rw [fSharpInverseImage_forget f]
  -- the two `Epi` arguments are supplied by name: the composite's factors are large enough that
  -- instance search does not reach the hypotheses above.
  exact @epi_comp _ _ _ _ _ _ hL _ hepi2

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### Local surjectivity of the structure map of an immersion -/

section StructureSharp

variable {Z A : AlgebraicSpaces B S hS}

/-- **The surjectivity clause of Stacks 03MB in inverse-image form, for a closed immersion.**
For a closed immersion `c : Z ⟶ A` of algebraic spaces over `S` the structure map
`c♯ : c⁻¹𝒪_A ⟶ 𝒪_Z` is locally surjective.

`AlgebraicGeometry.RingedToposHom.isLocallySurjective_fSharpInverseImage` reduces this to two
facts about a closed immersion: its small étale direct image is fully faithful, which is part (1)
of Stacks 04E5, and its structure map in direct-image form `𝒪_A ⟶ c_*𝒪_Z` is locally surjective,
which is the surjectivity clause of Stacks 03MB. -/
theorem isLocallySurjective_structureSharpInverseImage_of_isClosedImmersion (c : Z ⟶ A)
    (hc : IsClosedImmersion B S hS c.hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Z.1)
      (structureSharpInverseImage B S hS c).hom := by
  have hdirSet : Sheaf.IsLocallySurjective
      ((smallEtaleRingedTopos B S hS A).forgetRing.map
        (smallEtaleRingedToposHom B S hS c).fSharp) := by
    rw [forgetRing_map_fSharp]
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ _).1
      (isLocallySurjective_structureSharp B S hS c hc)
  exact (Presheaf.isLocallySurjective_iff_whisker_forget _ _).2
    (AlgebraicGeometry.RingedToposHom.isLocallySurjective_fSharpInverseImage
      (smallEtaleRingedToposHom B S hS c)
      (isEmbedding_smallToposMorphismTypeU B S hS c hc) hdirSet)

/-- **The surjectivity clause of Stacks 03MB in inverse-image form, for an immersion.**  For an
immersion `i : Z ⟶ X` of algebraic spaces over `S` the structure map `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` is
locally surjective.

By Stacks 04CE the immersion factors as a closed immersion `c` into the complement of the
boundary of its image followed by the inclusion `a` of that open subspace, which is étale.  The
étale-base comparison of Stacks 04CU carries `c♯ : c⁻¹𝒪_A ⟶ 𝒪_Z` to `(c ≫ a)♯` along an
isomorphism of its source, so local surjectivity for `c`
(`AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage_of_isClosedImmersion`)
gives local surjectivity for `c ≫ a`, which is `i`. -/
theorem isLocallySurjective_structureSharpInverseImage_of_isImmersion (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Z.1)
      (structureSharpInverseImage B S hS i).hom := by
  have ha : IsEtale B S hS (immersionAmbientInclusion B S hS i hi).hom :=
    isEtale_immersionAmbientInclusion B S hS i hi
  have hiso : Sheaf.IsLocallySurjective
      (etaleBaseInverseImageStructureSheafIso B S hS
        (immersionClosedFactorization B S hS X.2 Z.2 i.hom hi)
        (immersionAmbientInclusion B S hS i hi) ha).hom :=
    Sheaf.isLocallySurjective_of_iso _
  have hclosed : Sheaf.IsLocallySurjective (structureSharpInverseImage B S hS
      (immersionClosedFactorization B S hS X.2 Z.2 i.hom hi)) :=
    isLocallySurjective_structureSharpInverseImage_of_isClosedImmersion B S hS _
      (isClosedImmersion_boundaryComplementLift B S hS X.2 Z.2 i.hom hi)
  have hcomp : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Z.1)
      (structureSharpInverseImage B S hS
        (immersionClosedFactorization B S hS X.2 Z.2 i.hom hi ≫
          immersionAmbientInclusion B S hS i hi)).hom := by
    rw [← etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage B S hS
      (immersionClosedFactorization B S hS X.2 Z.2 i.hom hi)
      (immersionAmbientInclusion B S hS i hi) ha]
    exact Sheaf.isLocallySurjective_comp _ _
  rwa [immersionClosedFactorization_comp_immersionAmbientInclusion B S hS i hi] at hcomp

end StructureSharp

/-! ### The vanishing -/

/-- If the structure map `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of a morphism `f : X ⟶ Y` of algebraic spaces is
locally surjective, then every `Y`-derivation with values in a sheaf of `𝒪_X`-modules kills
every section of `𝒪_X`.

A derivation vanishes on the image of `f♯` and commutes with restriction, so it vanishes on the
restrictions of the given section to the members of the covering sieve on which that section is
in the image of `f♯`; the target is a sheaf, hence separated, so the value itself vanishes. -/
theorem derivation_d_eq_zero_of_isLocallySurjective (f : X ⟶ Y)
    (hsharp : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (structureSharpInverseImage B S hS f).hom)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (D : PresheafOfModulesOfCommRing.Derivation' F.val (structureSharpInverseImage B S hS f).hom)
    {U : SmallEtale B S hS X.1}
    (x : ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U) : CommRingCat.{u})) :
    D.d x = 0 := by
  have hsep : Presheaf.IsSeparated (SmallEtale.topology B S hS X.1) F.val.presheaf :=
    F.isSheaf.isSeparated
  refine hsep U (Presheaf.imageSieve (structureSharpInverseImage B S hS f).hom x)
    (hsharp.imageSieve_mem _) (D.d x) 0 ?_
  rintro V g ⟨t, ht⟩
  have hres : D.d ((smallEtaleRingedTopos B S hS X).O.obj.map g.op x) = 0 := by
    rw [← ht]
    exact D.d_app t
  rw [map_zero]
  exact (D.d_map g.op x).symm.trans hres

/-- If the structure map `f♯` of a morphism `f : X ⟶ Y` of algebraic spaces is locally
surjective, then a sheaf of `𝒪_X`-modules carries at most one `Y`-derivation: by
`AlgebraicGeometry.Space.derivation_d_eq_zero_of_isLocallySurjective` the underlying additive
map of any two of them is zero. -/
theorem derivation_eq_of_isLocallySurjective (f : X ⟶ Y)
    (hsharp : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (structureSharpInverseImage B S hS f).hom)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (D D' : PresheafOfModulesOfCommRing.Derivation' F.val
      (structureSharpInverseImage B S hS f).hom) : D = D' := by
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext W z
  exact (derivation_d_eq_zero_of_isLocallySurjective B S hS f hsharp F D z).trans
    (derivation_d_eq_zero_of_isLocallySurjective B S hS f hsharp F D' z).symm

/-- **Stacks 05Z9**, with local surjectivity of the structure map in place of the hypothesis
that `f` is an immersion.  If `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` is locally surjective then `Ω_{X/Y}` is zero.

`Ω_{X/Y}` corepresents the functor of `Y`-derivations, and by
`AlgebraicGeometry.Space.derivation_eq_of_isLocallySurjective` that functor takes at most one
value at each sheaf of `𝒪_X`-modules; so the identity and the zero endomorphism of `Ω_{X/Y}`
both factor the same derivation and are therefore equal.

An immersion has locally surjective structure map, by
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage_of_isImmersion`, which is
how `AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_isImmersion_unconditional` reaches
the source's statement. -/
@[stacks 05Z9 "the vanishing Ω_{X/Y} = 0, from local surjectivity of `f♯`; the gap to the
  source's hypothesis is that an immersion of algebraic spaces has locally surjective structure
  map, which is the inverse-image form of the surjectivity clause of 03MB"]
theorem isZero_sheafOfDifferentials_of_isLocallySurjective (f : X ⟶ Y)
    (hsharp : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (structureSharpInverseImage B S hS f).hom) :
    IsZero (sheafOfDifferentials B S hS f) := by
  rw [IsZero.iff_id_eq_zero]
  obtain ⟨g, -, hg⟩ := universalDerivation_isUniversal B S hS f (sheafOfDifferentials B S hS f)
    ((universalDerivation B S hS f).postcomp
      (𝟙 (sheafOfDifferentials B S hS f) :
        sheafOfDifferentials B S hS f ⟶ sheafOfDifferentials B S hS f).val)
  exact (hg _ rfl).trans
    (hg 0 (derivation_eq_of_isLocallySurjective B S hS f hsharp _ _ _)).symm

/-- **Stacks 05Z9.**  If `f : X ⟶ Y` is an immersion of algebraic spaces over `S` then
`Ω_{X/Y}` is zero.

The hypothesis `hsharp` is the one input not proved in this development: the structure map
`f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of an immersion of algebraic spaces is locally surjective.  It is the
inverse-image form of the surjectivity clause of Stacks 03MB, which
`AlgebraicGeometry.Space.isLocallySurjective_structureSharp` supplies only in the direct-image
form `𝒪_Y ⟶ f_*𝒪_X` and only for closed immersions, and it is carried here universally
quantified over all immersions of algebraic spaces over `S`.

That input is no longer unproved: it is
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage_of_isImmersion` above, so
the hypothesis-free form of this statement is
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_isImmersion_unconditional`. -/
@[stacks 05Z9 "the source's statement, carrying local surjectivity of the structure map of an
  immersion (the inverse-image form of the surjectivity clause of 03MB) as `hsharp`, quantified
  over all immersions of algebraic spaces over `S`"]
theorem isZero_sheafOfDifferentials_of_isImmersion
    (hsharp : ∀ (X' Y' : AlgebraicSpaces B S hS) (g : X' ⟶ Y'), IsImmersion B S hS g.hom →
      Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X'.1)
        (structureSharpInverseImage B S hS g).hom)
    (f : X ⟶ Y) (hf : IsImmersion B S hS f.hom) :
    IsZero (sheafOfDifferentials B S hS f) :=
  isZero_sheafOfDifferentials_of_isLocallySurjective B S hS f (hsharp X Y f hf)

/-- **Stacks 05Z9.**  If `f : X ⟶ Y` is an immersion of algebraic spaces over `S` then
`Ω_{X/Y}` is zero, with no hypothesis beyond the immersion.

The structure map `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of an immersion is locally surjective
(`AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage_of_isImmersion`), and
local surjectivity forces the vanishing
(`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_isLocallySurjective`).  This is
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_isImmersion` with its hypothesis
`hsharp` discharged. -/
@[stacks 05Z9 "the source's statement: the sheaf of differentials of an immersion of algebraic \
spaces over `S` is a zero object, with no hypothesis beyond the immersion"]
theorem isZero_sheafOfDifferentials_of_isImmersion_unconditional (f : X ⟶ Y)
    (hf : IsImmersion B S hS f.hom) :
    IsZero (sheafOfDifferentials B S hS f) :=
  isZero_sheafOfDifferentials_of_isLocallySurjective B S hS f
    (isLocallySurjective_structureSharpInverseImage_of_isImmersion B S hS f hf)

end AlgebraicGeometry.Space

end
