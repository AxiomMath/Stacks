module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageKernelIdealCounit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleUnit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ExtendedCech

/-!
# The direct image of the counit as a morphism of sheaves of modules

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  `StacksFrontier/AlgebraicGeometry/Spaces/MorphismKernelIdealInverseImage.lean` carries
the sequence `𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X` of `𝒪_Y`-modules through `f⁻¹` and then through `f_*`, and
proves that its first map is a kernel of its third.  The third term of the result is
`f_*f⁻¹f_*𝒪_X`, while the sequence it came from ends in `f_*𝒪_X`.  This file builds the
comparison between the two **as a morphism of `𝒪_Y`-modules**, out of the homomorphism of
sheaves of rings of
`StacksFrontier/AlgebraicGeometry/Spaces/DirectImageKernelIdealCounit.lean`, and uses it to carry
the kernel across.

## Main definitions

* `AlgebraicGeometry.Space.directImageKernelIdealUnitIso`: the identification of
  `f_*f⁻¹f_*𝒪_X`, as it occurs in the sequence above, with the unit module of the sheaf of rings
  `f_*f⁻¹f_*𝒪_X` with its scalars restricted along `𝒪_Y ⟶ f_*f⁻¹f_*𝒪_X`.  It is the identity on
  underlying sheaves of sets.
* `AlgebraicGeometry.Space.directImageKernelIdealModuleCounit`: **the direct image of the
  counit of `f⁻¹ ⊣ f_*` at `𝒪_X`, as a morphism `f_*f⁻¹f_*𝒪_X ⟶ f_*𝒪_X` of `𝒪_Y`-modules**, at
  an arbitrary morphism of algebraic spaces.
* `AlgebraicGeometry.Space.directImageKernelIdealProjection`: the projection
  `f_*f⁻¹𝒪_Y ⟶ f_*𝒪_X` of `𝒪_Y`-modules it factors.

## Main results

* `SheafOfModules.mono_unitRestrictScalarsMapOfComp_of_retraction`: a homomorphism of sheaves
  of rings over `R` with a retraction is a monomorphism of sheaves of `R`-modules.
* `AlgebraicGeometry.Space.isIso_ringCounit_of_isClosedImmersion`: the counit
  `f⁻¹f_*𝒪_X ⟶ 𝒪_X` of a closed immersion is invertible as a homomorphism of sheaves of
  **rings**, which is the form in which monomorphy can be read off.
* `AlgebraicGeometry.Space.mono_directImageKernelIdealModuleCounit`: **the direct image of the
  counit is a monomorphism at an arbitrary closed immersion.**
* `AlgebraicGeometry.Space.isLimitKernelFork_directImageKernelIdealProjection`:
  **`f_*f⁻¹𝓘_f ⟶ f_*f⁻¹𝒪_Y` is a kernel of the projection `f_*f⁻¹𝒪_Y ⟶ f_*𝒪_X`** at an
  arbitrary closed immersion, with
  `AlgebraicGeometry.Space.mem_range_directImageKernelIdealProjection_val_app` reading that on
  sections.  Injectivity of that inclusion on sections needs no closed immersion and is
  `AlgebraicGeometry.Space.injective_directImageKernelIdeal_f_val_app`.

## Implementation notes

**Why there is no module-level counit to take.**  The adjunction of Stacks 03D3 is
`f⁻¹ ⊣ f_*`, so `f_*f⁻¹` is a *monad* on sheaves of `𝒪_Y`-modules: its structure map is the
unit `G ⟶ f_*f⁻¹G`, and there is no natural map `f_*f⁻¹G ⟶ G`.  The morphism built here is
therefore not `f_*` of a module-level counit; it exists only because the module in question is
the unit module of a sheaf of rings, where the ring-level counit is available.

**The two layers of restriction of scalars.**  The third term of the sequence is
`f_*f⁻¹((f_*𝒪_X) as an 𝒪_Y-module)`, and `f_*𝒪_X` is an `𝒪_Y`-module by restriction of scalars
along `f♯`.  The inverse image does **not** commute with restriction of scalars
definitionally — the comparison is
`Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso`, an isomorphism which
is the identity on underlying sheaves of sets — so a hand-written `ModuleCat.homMk` out of the
third term leaves a `smul` obligation about those two layers rather than about the counit.
`AlgebraicGeometry.Space.directImageKernelIdealUnitIso` moves both layers out of the way
first, after which `SheafOfModules.unitRestrictScalarsMapOfComp` reads the ring homomorphism as
a morphism of modules with no transport at all.

**`SheafOfModules.unitRestrictScalarsMapOfComp` needs its two scalar maps by name.**  Left to
unification, it takes `αA` to be the first factor `ringUnit` of the composite rather than the
whole of `𝒪_Y ⟶ f_*f⁻¹f_*𝒪_X`, and reports a type mismatch naming
`AlgebraicGeometry.Space.structureRingSheafDirectImage` as the expected type of `β`.  The
map is therefore built through `SheafOfModules.pullbackPullbackUnitRestrictScalarsMap`, which
takes the two factors of `αA` separately and `αB` by name, and whose source is spelled as the
target of `AlgebraicGeometry.Space.directImageKernelIdealUnitIso`: identifying the two spellings
at this concrete morphism is what exhausts the heartbeat budget, and at the generic level it is
cheap.  That map is given a name of its own rather than
inlined because the monomorphy of
`AlgebraicGeometry.Space.directImageKernelIdealModuleCounit` is instance resolution against
`CategoryTheory.mono_comp`, and instance resolution matches up to reducible transparency only:
against the inlined composite it rediscovers the scalar maps in a different spelling and the
`Mono` hypothesis on hand no longer applies.

**Monomorphy is read through the isomorphism factors, not on sections.**  The comparison is an
isomorphism by construction, so `CategoryTheory.mono_comp` reduces monomorphy of the whole to
monomorphy of `AlgebraicGeometry.Space.directImageKernelIdealCounitUnitMap`, and that follows
from a retraction of the underlying homomorphism of sheaves of rings.  Nothing here evaluates
either morphism on sections: the value of
`AlgebraicGeometry.Space.directImageKernelIdealModuleCounit` on sections is not syntactically
the ring counit, because the direct image of the identity comparison is not syntactically an
identity.

**The counit is inverted at `RingCat`, not at `CommRingCat`.**  Only
`AlgebraicGeometry.Space.isIso_commRingCounit_of_isClosedImmersion` is available, and
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction_counit_forgetCommRing` carries it to
the `RingCat`-valued counit, which is the one `AlgebraicGeometry.Space.directImageRingCounit`
is built from.  The rewrite is stated with
`AlgebraicGeometry.Space.smallToposMorphismTypeU` on the right, as the
`CommRingCat`-level statement spells it; that it agrees with
`(AlgebraicGeometry.Space.smallEtaleRingedToposHom …).toToposHom`, and that
`AlgebraicGeometry.Space.structureRingSheaf` agrees with `Stacks.ringSheaf` of the ringed
topos, are both `rfl`.

**No type below is restated.**  Writing out a type that mentions
`Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf` makes its universe parameters default,
and the argument is then rejected at `Sheaf.{0, 0, 0, 1}`; the sheaf of modules that
`Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso` needs is spelled
`pullbackModuleObj … (SheafOfModules.unit …)` instead, which is definitionally the unit module
of the inverse-image sheaf of rings and mentions no inverse-image sheaf of rings.  For the same
reason the kernel fork below has no ascribed type: the vanishing composite it forks over is the
one `CategoryTheory.Limits.isKernelCompMono` constructs, and stating it separately asks for a
`Zero` on a hom type whose instance search does not terminate here.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1), the direct image, and
  [Tag 03D3](https://stacks.math.columbia.edu/tag/03D3), its adjunction.
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6), part (1), and
  [Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the direct image of modules read
  through the structure map.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1), behind the
  invertibility of the counit of a closed immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u v w

/-! ## A homomorphism of sheaves of rings with a retraction is a monomorphism of modules -/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R A D : Sheaf J RingCat.{w}}

/-- **A homomorphism of sheaves of rings over `R` with a retraction is a monomorphism of
sheaves of `R`-modules.**  If `β : A ⟶ D` is a homomorphism of sheaves of rings over `R`, in
the sense that `αA ≫ β = αB`, and `δ` retracts it, then `δ` is itself a homomorphism over `R`
and retracts `β` as a morphism of `R`-modules, so `SheafOfModules.unitRestrictScalarsMapOfComp`
of `β` is a split monomorphism.

A retraction rather than an inverse is asked for because that is the weaker hypothesis; at a
closed immersion the counit this is applied to is in fact invertible.  The identity of
`A` is reached through `SheafOfModules.unitRestrictScalarsMap_congr`, `β ≫ δ` being equal to
it but not syntactically so. -/
theorem mono_unitRestrictScalarsMapOfComp_of_retraction {αA : R ⟶ A} {αB : R ⟶ D}
    (β : A ⟶ D) (h : αA ≫ β = αB) (δ : D ⟶ A) (hβδ : β ≫ δ = 𝟙 A) :
    Mono (unitRestrictScalarsMapOfComp β h) := by
  have h' : αB ≫ δ = αA := by rw [← h, Category.assoc, hβδ, Category.comp_id]
  have hcomp : αA ≫ β ≫ δ = αA := by rw [hβδ, Category.comp_id]
  have e : unitRestrictScalarsMapOfComp (β ≫ δ) hcomp =
      𝟙 ((restrictScalars.{w} αA).obj (unit A)) :=
    (unitRestrictScalarsMap_congr hcomp (Category.comp_id αA) hβδ).trans
      (unitRestrictScalarsMap_id (Category.comp_id αA))
  exact IsSplitMono.mono (unitRestrictScalarsMapOfComp β h)
    (hf := IsSplitMono.mk' ⟨_, (unitRestrictScalarsMap_comp h h' hcomp).trans e⟩)

end SheafOfModules

/-! ## The counit map with its source spelled as the comparison's target -/

namespace SheafOfModules

section PullbackPullback

universe ww ww' vv uu vv' uu'

variable {C₁ : Type uu} [Category.{vv} C₁] {C₂ : Type uu'} [Category.{vv'} C₂]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
  [J₁.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J₂.HasSheafCompose (CategoryTheory.forget RingCat.{ww'})]
  [J₁.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})]
  [J₂.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf J₂ (Type ww') ⥤ Sheaf J₁ (Type ww)) [PreservesFiniteProducts Φ]
  (Ψ : Sheaf J₁ (Type ww) ⥤ Sheaf J₂ (Type ww')) [PreservesFiniteProducts Ψ]

/-- `SheafOfModules.unitRestrictScalarsMapOfComp`, for a homomorphism `β` out of the sheaf of
rings `Ψ(Φ O)` over `R` through the composite `a ≫ b`, with its source written as the unit
module `Ψ(Φ(unit O))` with its scalars restricted first along `b` and then along `a`.  The two
spellings of the source are definitionally equal
(`Stacks.Sheaves.ToposPullback.pullbackModuleObj_unit` twice, and restriction of scalars along a
composite); this records the identification once, at the generic level, where unifying the two
spellings is cheap.  At a concrete morphism of algebraic spaces the same unification exhausts
the heartbeat budget. -/
noncomputable def pullbackPullbackUnitRestrictScalarsMap (O : Sheaf J₂ RingCat.{ww'})
    {R R₁ E : Sheaf J₂ RingCat.{ww'}} (a : R ⟶ R₁)
    (b : R₁ ⟶ Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₂ Ψ
      (Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₁ Φ O))
    {αB : R ⟶ E}
    (β : Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₂ Ψ
      (Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₁ Φ O) ⟶ E)
    (h : (a ≫ b) ≫ β = αB) :
    (restrictScalars.{ww'} a).obj ((restrictScalars.{ww'} b).obj
        (Stacks.Sheaves.ToposPullback.pullbackModuleObj J₂ Ψ
          (Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₁ Φ O)
          (Stacks.Sheaves.ToposPullback.pullbackModuleObj J₁ Φ O (unit O)))) ⟶
      (restrictScalars.{ww'} αB).obj (unit E) :=
  (unitRestrictScalarsMapOfComp β h :)

/-- `SheafOfModules.mono_unitRestrictScalarsMapOfComp_of_retraction` for
`SheafOfModules.pullbackPullbackUnitRestrictScalarsMap`. -/
theorem mono_pullbackPullbackUnitRestrictScalarsMap_of_retraction (O : Sheaf J₂ RingCat.{ww'})
    {R R₁ E : Sheaf J₂ RingCat.{ww'}} (a : R ⟶ R₁)
    (b : R₁ ⟶ Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₂ Ψ
      (Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₁ Φ O))
    {αB : R ⟶ E}
    (β : Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₂ Ψ
      (Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₁ Φ O) ⟶ E)
    (h : (a ≫ b) ≫ β = αB)
    (δ : E ⟶ Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₂ Ψ
      (Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₁ Φ O))
    (hβδ : β ≫ δ = 𝟙 _) :
    Mono (pullbackPullbackUnitRestrictScalarsMap Φ Ψ O a b β h) :=
  (mono_unitRestrictScalarsMapOfComp_of_retraction β h δ hβδ :)

end PullbackPullback

end SheafOfModules

/-! ## The direct image of the counit as a morphism of sheaves of modules -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **`f_*f⁻¹f_*𝒪_X` is the unit module of a sheaf of rings.**  The third term of the direct
image of the inverse image of the sequence `𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X`, identified with the unit
module of the sheaf of rings `f_*f⁻¹f_*𝒪_X` whose scalars are restricted along the composite
`𝒪_Y ⟶ f_*f⁻¹𝒪_Y ⟶ f_*f⁻¹f_*𝒪_X` of the unit of `f⁻¹ ⊣ f_*` with `f_*f⁻¹(f♯)`.

It is built from two instances of
`Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso`, which move the
restriction of scalars along `f♯` out of `f⁻¹` and then out of `f_*`; each is the identity on
underlying sheaves of sets, and so is this.  The type is left to be inferred; see the
implementation notes. -/
noncomputable def directImageKernelIdealUnitIso (f : X ⟶ Y) :=
  (directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).mapIso
    (pullbackModuleObjRestrictScalarsIso (SmallEtale.topology B S hS X.1)
      (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
      (structureSharp B S hS f)
      (SheafOfModules.unit (structureRingSheafDirectImage B S hS f))).symm ≪≫
  (SheafOfModules.restrictScalars
      (ringUnit (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y))).mapIso
    (pullbackModuleObjRestrictScalarsIso (SmallEtale.topology B S hS Y.1)
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
      (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
        (structureSharp B S hS f))
      (pullbackModuleObj (SmallEtale.topology B S hS X.1)
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
        (structureRingSheafDirectImage B S hS f)
        (SheafOfModules.unit (structureRingSheafDirectImage B S hS f)))).symm

/-- **The direct image of the counit, read between unit modules.**  The homomorphism of sheaves
of rings `AlgebraicGeometry.Space.directImageRingCounit`, read as a morphism of `𝒪_Y`-modules
from the unit module of `f_*f⁻¹f_*𝒪_X` to the unit module of `f_*𝒪_X`, their scalars being
restricted along `𝒪_Y ⟶ f_*f⁻¹f_*𝒪_X` and along `f♯` respectively.  The identity that makes
this legitimate is `AlgebraicGeometry.Space.ringUnit_comp_directImageRingCounit`.

It is built through `SheafOfModules.pullbackPullbackUnitRestrictScalarsMap`, whose source is
spelled exactly as the target of `AlgebraicGeometry.Space.directImageKernelIdealUnitIso`, so
that composing the two is syntactic.  This map is named rather than inlined; see the
implementation notes. -/
noncomputable def directImageKernelIdealCounitUnitMap (f : X ⟶ Y) :=
  SheafOfModules.pullbackPullbackUnitRestrictScalarsMap
    (J₁ := SmallEtale.topology B S hS X.1) (J₂ := SmallEtale.topology B S hS Y.1)
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
    (structureRingSheafDirectImage B S hS f)
    (ringUnit (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS Y))
    (pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
      (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
        (structureSharp B S hS f)))
    (αB := structureSharp B S hS f)
    (directImageRingCounit B S hS f)
    (ringUnit_comp_directImageRingCounit B S hS f)

/-- **The direct image of the counit of `f⁻¹ ⊣ f_*` at `𝒪_X`, as a morphism of `𝒪_Y`-modules.**
The morphism `f_*f⁻¹f_*𝒪_X ⟶ f_*𝒪_X` from the third term of
`AlgebraicGeometry.Space.directImageKernelIdealComplex` to the third term of
`AlgebraicGeometry.Space.kernelIdealShortComplex`, for an arbitrary morphism `f` of algebraic
spaces.

See the implementation notes for why there is no module-level counit to push forward instead.
The type is left to be inferred, and is pinned by
`AlgebraicGeometry.Space.directImageKernelIdealProjection` below. -/
noncomputable def directImageKernelIdealModuleCounit (f : X ⟶ Y) :=
  (directImageKernelIdealUnitIso B S hS f).hom ≫ directImageKernelIdealCounitUnitMap B S hS f

/-- The factorisation of `AlgebraicGeometry.Space.directImageKernelIdealModuleCounit` into the
comparison and the counit, as a named equation.  Reading it off the definition by unification
instead — which is what `CategoryTheory.mono_comp'` would do — exhausts the heartbeat budget,
the objects the two factors run between being large; against this equation the rewrite is
syntactic. -/
theorem directImageKernelIdealModuleCounit_eq (f : X ⟶ Y) :
    directImageKernelIdealModuleCounit B S hS f =
      (directImageKernelIdealUnitIso B S hS f).hom ≫
        directImageKernelIdealCounitUnitMap B S hS f := rfl

/-- **The projection `f_*f⁻¹𝒪_Y ⟶ f_*𝒪_X` of `𝒪_Y`-modules**, the third map of
`AlgebraicGeometry.Space.directImageKernelIdealComplex` followed by the direct image of the
counit.  This is the map whose kernel the conormal sequence of a closed immersion is read off
of, and its ascribed type pins both ends of
`AlgebraicGeometry.Space.directImageKernelIdealModuleCounit`: its source is the third term of
`AlgebraicGeometry.Space.directImageKernelIdealComplex` and its target the third term of
`AlgebraicGeometry.Space.kernelIdealShortComplex`.

It is defined for an arbitrary morphism of algebraic spaces. -/
noncomputable def directImageKernelIdealProjection (f : X ⟶ Y) :
    (directImageKernelIdealComplex B S hS f).X₂ ⟶ (kernelIdealShortComplex B S hS f).X₃ :=
  (directImageKernelIdealComplex B S hS f).g ≫ directImageKernelIdealModuleCounit B S hS f

/-! ## Monomorphy at a closed immersion -/

/-- **The counit `f⁻¹f_*𝒪_X ⟶ 𝒪_X` of a closed immersion is invertible as a homomorphism of
sheaves of rings.**  The `CommRingCat`-valued statement is
`AlgebraicGeometry.Space.isIso_commRingCounit_of_isClosedImmersion`, and forgetting
commutativity carries its counit to this one by
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction_counit_forgetCommRing`.

This is the form monomorphy is read in: `AlgebraicGeometry.Space.directImageRingCounit` is
built from the `RingCat`-valued counit, so no `CommRingCat`-valued isomorphism is needed
downstream.  Compare
`Stacks.Sheaves.ToposPushforward.isIso_ringCounit_of_isEmbedding`, which asks instead that the
morphism of topoi be an embedding; no such instance is produced for a closed immersion of
algebraic spaces. -/
theorem isIso_ringCounit_of_isClosedImmersion (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    IsIso (ringCounit (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS X)) := by
  have := isIso_commRingCounit_of_isClosedImmersion B S hS f hf
    (smallEtaleRingedTopos B S hS X).O
  rw [show ringCounit (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS X) = _ from
      (commRingImageAdjunction_counit_forgetCommRing
        (smallToposMorphismTypeU B S hS f) (smallEtaleRingedTopos B S hS X).O).symm]
  exact Functor.map_isIso _ _

/-- **The direct image of the counit of a closed immersion has a retraction**, namely the
direct image of the inverse of the counit.  Both are direct images of homomorphisms of sheaves
of rings, so this is functoriality of
`Stacks.Sheaves.ToposPullback.pullbackRingSheafMap` together with
`AlgebraicGeometry.Space.isIso_ringCounit_of_isClosedImmersion`. -/
theorem directImageRingCounit_comp_pullbackRingSheafMap_inv (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    directImageRingCounit B S hS f ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
          (@inv _ _ _ _ (ringCounit (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS X))
            (isIso_ringCounit_of_isClosedImmersion B S hS f hf)) = 𝟙 _ := by
  have := isIso_ringCounit_of_isClosedImmersion B S hS f hf
  rw [show directImageRingCounit B S hS f =
      pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
        (ringCounit (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS X)) from rfl,
    ← pullbackRingSheafMap_comp, IsIso.hom_inv_id, pullbackRingSheafMap_id]

/-- **The direct image of the counit, read between unit modules, is a monomorphism at a closed
immersion**, by `SheafOfModules.mono_unitRestrictScalarsMapOfComp_of_retraction` applied to the
retraction above. -/
theorem mono_directImageKernelIdealCounitUnitMap (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    Mono (directImageKernelIdealCounitUnitMap B S hS f) :=
  SheafOfModules.mono_pullbackPullbackUnitRestrictScalarsMap_of_retraction
    (J₁ := SmallEtale.topology B S hS X.1) (J₂ := SmallEtale.topology B S hS Y.1)
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
    (structureRingSheafDirectImage B S hS f) _ _ (αB := structureSharp B S hS f)
    (directImageRingCounit B S hS f) (ringUnit_comp_directImageRingCounit B S hS f) _
    (directImageRingCounit_comp_pullbackRingSheafMap_inv B S hS f hf)

/-- **The direct image of the counit is a monomorphism of `𝒪_Y`-modules at an arbitrary closed
immersion.**  Its first factor is an isomorphism and its second is a monomorphism by
`AlgebraicGeometry.Space.mono_directImageKernelIdealCounitUnitMap`; no sectionwise computation
is involved.  See the implementation notes. -/
theorem mono_directImageKernelIdealModuleCounit (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    Mono (directImageKernelIdealModuleCounit B S hS f) := by
  rw [directImageKernelIdealModuleCounit_eq]
  exact mono_comp' (IsIso.mono_of_iso (directImageKernelIdealUnitIso B S hS f).hom)
    (mono_directImageKernelIdealCounitUnitMap B S hS f hf)

/-! ## The kernel of the projection at a closed immersion -/

/-- **`f_*f⁻¹𝓘_f ⟶ f_*f⁻¹𝒪_Y` is a kernel of the projection `f_*f⁻¹𝒪_Y ⟶ f_*𝒪_X`** at an
arbitrary closed immersion.

`AlgebraicGeometry.Space.isLimitKernelFork_directImageKernelIdeal` is the same statement for
`f_*f⁻¹(f♯)`, at an arbitrary morphism, and the projection is that map followed by the direct
image of the counit, which is a monomorphism here; so
`CategoryTheory.Limits.isKernelCompMono` carries the kernel across, with the same inclusion.

The type is left to be inferred; see the implementation notes. -/
noncomputable def isLimitKernelFork_directImageKernelIdealProjection (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :=
  isKernelCompMono (isLimitKernelFork_directImageKernelIdeal B S hS f)
    (directImageKernelIdealModuleCounit B S hS f)
    (hg := mono_directImageKernelIdealModuleCounit B S hS f hf) rfl

/-- **A section of `f_*f⁻¹𝒪_Y` killed by the projection `f_*f⁻¹𝒪_Y ⟶ f_*𝒪_X` comes from
`f_*f⁻¹𝓘_f`**, at an arbitrary closed immersion.  This is the sectionwise form of
`AlgebraicGeometry.Space.isLimitKernelFork_directImageKernelIdealProjection`, and it is what
the derivation of Stacks 02HP consumes. -/
theorem mem_range_directImageKernelIdealProjection_val_app (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    {x : (directImageKernelIdealComplex B S hS f).X₂.val.obj U}
    (hx : (directImageKernelIdealProjection B S hS f).val.app U x = 0) :
    x ∈ LinearMap.range ((directImageKernelIdealComplex B S hS f).f.val.app U).hom :=
  _root_.SheafOfModules.mem_range_val_app_of_isLimit_kernelFork
    (isLimitKernelFork_directImageKernelIdealProjection B S hS f hf) U hx

end AlgebraicGeometry.Space

end
