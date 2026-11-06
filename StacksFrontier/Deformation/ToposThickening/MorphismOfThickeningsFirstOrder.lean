module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SmulAnnihilatesSubobject
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnitEpi
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ClosedImmersion
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickeningsIdealMap

/-!
# The induced map of defining ideals of a first order morphism of thickenings of ringed topoi

Let

```
  (Sh(C), O)  --i-->  (Sh(D), O')
      |                   |
      f                   f'
      v                   v
  (Sh(B), O_B) --t--> (Sh(B'), O_{B'})
```

be a morphism of thickenings of ringed topoi (Stacks 08M7), with defining ideals
`I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`, and let
`(f')^*J ⟶ I` be the induced map of defining ideals of
`StacksFrontier/Deformation/ToposThickening/MorphismOfThickeningsIdealMap.lean`.

This file is the last clause of Stacks 08M7: **when `i` and `t` are first order thickenings the
induced map descends to a map `f^*J ⟶ I`.** Concretely there is a canonical surjection
`(f')^*J ⟶ f^*J`, and since `I` is annihilated by itself the induced map factors uniquely
through it.

## The engine

For a thickening `i` the direct image `i_*` of sheaves of modules is fully faithful with
essential image the `O'`-modules annihilated by `I`: the underlying morphism of topoi is an
equivalence and the structure map is locally surjective, so `i` is a closed immersion of ringed
topoi and Stacks 08M3 applies. Two consequences drive everything below.

* The unit of `i^* ⊣ i_*` is an **epimorphism at every module**: the image of `η_M` is a
  subobject of `i_*i^*M`, hence annihilated by `I`, hence in the essential image, so the unit at
  it is invertible — and that splits the image inclusion
  (`CategoryTheory.Adjunction.epi_unit_app_of_isIso_unit_app_image`).
* When `i` is first order the unit is an **isomorphism at the defining ideal** `I`, because a
  product of two sections of `I` vanishes, so `I` is annihilated by itself and therefore lies in
  the essential image.

The first gives surjectivity of `(f')^*J ⟶ f^*J`, the second the factorization.

## Main definitions

* `Deformation.ToposThickening.IsThickening.closedRingedImmersion`: a thickening of ringed topoi
  read as a closed immersion of ringed topoi, which is what makes Stacks 08M3 available for it.
* `Deformation.ToposThickening.MorphismOfThickenings.reducedPullbackIdeal`: the source's `f^*J`,
  transported to an `O'`-module as `i_*f^*t^*J`.
* `Deformation.ToposThickening.MorphismOfThickenings.firstOrderSurjection`: **Stacks 08M7**, the
  canonical reduction map `(f')^*J ⟶ f^*J`.
* `Deformation.ToposThickening.MorphismOfThickenings.firstOrderIdealMap`: **Stacks 08M7**, the
  induced map of defining ideals read as a map `f^*J ⟶ I`, together with the factorization and
  its uniqueness.

## Main results

* `Deformation.ToposThickening.IsThickening.essImage_pushforwardModules_iff`: an `O'`-module is a
  direct image along a thickening exactly when the defining ideal annihilates it.
* `Deformation.ToposThickening.IsThickening.epi_unit_app`: for a thickening the unit of
  `i^* ⊣ i_*` is an epimorphism at every module.
* `Deformation.ToposThickening.IsFirstOrderThickening.isIso_unit_app_ideal`: for a first order
  thickening the unit is an isomorphism at the defining ideal, so the ideal is a module on the
  source topos.
* `Deformation.ToposThickening.MorphismOfThickenings.firstOrderSurjection_epi`: **Stacks 08M7**,
  the reduction map `(f')^*J ⟶ f^*J` is an epimorphism.

## Implementation notes

Rather than identifying the equivalent topoi of a thickening, modules on the source topos are
moved to the target by the direct image. So the source's `f^*J`, read as an `O'`-module, is
`reducedPullbackIdeal = i_*f^*t^*J`, and `firstOrderSurjection` is the unit of `i^* ⊣ i_*`
followed by the direct image of
`Deformation.ToposThickening.MorphismOfThickenings.pullbackComparison`, the canonical comparison
`i^*(f')^*J ≅ f^*t^*J` of the two iterated pullbacks around the square. The same pattern is used
at ringed-space level in `StacksFrontier/Topology/Sheaves/RingedSpace/Thickening.lean`.

`t^*J` rather than `J` appears because `J` is an `O_{B'}`-module while `f^*` consumes an
`O_B`-module. That this loses nothing is the first-orderness of `t`: it is
`Deformation.ToposThickening.IsFirstOrderThickening.isIso_unit_app_ideal` applied to `t`, which
says `J` is already a module on `Sh(B)`, so `t^*J` is `J` read there. This is why the hypothesis
`ht` is not consumed by the proofs below even though the source states it — the statements have
it built into the shape of `reducedPullbackIdeal`.

`firstOrderSurjection` carries no first-order hypothesis: the map is canonically defined for any
morphism of thickenings, and only its surjectivity needs `i` to be first order. Its body is
reached in the one place it is needed by `unfold` rather than by a hand-written equation lemma:
the composite re-elaborated outside the definition exhausts the elaborator's recursion budget on
these terms, while `unfold` reuses the body the definition already elaborated.

The section universes of the two upper topoi are equal here, as `AlgebraicGeometry.
ClosedRingedImmersion` requires of the closed immersion it carries; the two lower ones stay
independent, nothing below reading `t` as a closed immersion.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom ClosedRingedImmersion)
open AlgebraicGeometry.RingedToposHom (pushforwardModules pullbackAdjPushforwardModules)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u w v' u' w' v'' u'' w'' v''' u''' w'''

namespace Deformation.ToposThickening

section Thickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The underlying morphism of topoi of a thickening is a closed immersion: it is an equivalence,
hence an embedding whose direct image is essentially surjective, and the whole topos is the
closed complement of the empty-sieve sheaf. -/
lemma IsThickening.isClosedImmersion {i : RingedToposHom X Y} (hi : IsThickening i) :
    MorphismOfTopoi.IsClosedImmersion i.toToposHom := by
  have : i.toToposHom.pushforward.IsEquivalence := hi.1
  refine ⟨⟨Functor.IsEquivalence.full, Functor.IsEquivalence.faithful⟩, ?_⟩
  refine ⟨emptySheaf.{u', v', w} Y.J, mono_terminal_from_emptySheaf Y.J, ?_⟩
  ext G
  constructor
  · intro _
    exact Functor.EssSurj.mem_essImage i.toToposHom.pushforward G
  · intro _
    exact isIso_prod_fst_emptySheaf Y.J G

/-- The structure map of a thickening is locally surjective on the underlying sheaves of sets.
Local surjectivity of a morphism of sheaves valued in a concrete category is that of the
underlying morphism of sheaves of sets, which is the form the structure map is carried in. -/
lemma IsThickening.structureMap_surjective {i : RingedToposHom X Y} (hi : IsThickening i) :
    Sheaf.IsLocallySurjective (Y.forgetRing.map i.fSharp) := by
  have : Presheaf.IsLocallySurjective Y.J i.fSharp.hom := hi.2.1
  have h0 : Presheaf.IsLocallySurjective Y.J
      (Functor.whiskerRight i.fSharp.hom (forget CommRingCat.{w})) := inferInstance
  have hsurj : Presheaf.IsLocallySurjective Y.J
      ((sheafToPresheaf Y.J (Type w)).map (Y.forgetRing.map i.fSharp)) := by
    show Presheaf.IsLocallySurjective Y.J
      (Functor.whiskerRight i.fSharp.hom (forget CommRingCat.{w}))
    exact h0
  exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).1 hsurj

/-- A thickening of ringed topoi, read as a closed immersion of ringed topoi. This is what makes
the Stacks 08M3 results about `i_*` on sheaves of modules available for a thickening.

`Deformation.ToposThickening.FirstOrderThickening.closedRingedImmersion` is the same
construction from the stronger datum of Stacks 08MB; only the two conditions above are used
there, so that one is the composite of
`Deformation.ToposThickening.IsThickening.of_firstOrderThickening` with this. -/
noncomputable def IsThickening.closedRingedImmersion {i : RingedToposHom X Y}
    (hi : IsThickening i) : ClosedRingedImmersion.{v, u, v', u', w} where
  source := X
  target := Y
  hom := i
  isClosedImmersion := hi.isClosedImmersion
  structureMap_surjective := hi.structureMap_surjective

/-- **The essential image of the direct image along a thickening.** A sheaf of `O'`-modules is a
direct image along a thickening `i` exactly when the kernel of the structure map annihilates it,
section by section.

This is Stacks 08M3 for a thickening, through
`Deformation.ToposThickening.IsThickening.closedRingedImmersion`; the 08M3 attribute sits on
`AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates`. -/
theorem IsThickening.essImage_pushforwardModules_iff {i : RingedToposHom X Y}
    (hi : IsThickening i)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (pushforwardModules i).essImage G ↔
      ∀ (U : Y.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U),
        a ∈ RingHom.ker (i.fSharp.hom.app U).hom →
          ∀ m : G.val.obj U, a • m = 0 := by
  refine (hi.closedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates G).trans ?_
  exact ⟨fun h U a ha m => h U a ha m, fun h U a ha m => h U a ha m⟩

/-- The direct image of sheaves of modules along a thickening is fully faithful. This is the
other half of Stacks 08M3, read for a thickening. -/
theorem IsThickening.nonempty_pushforwardModules_fullyFaithful {i : RingedToposHom X Y}
    (hi : IsThickening i) : Nonempty (pushforwardModules i).FullyFaithful :=
  hi.closedRingedImmersion.pushforwardModules_fullyFaithful

/-- The unit of `i^* ⊣ i_*` at a module is an isomorphism once the kernel of the structure map
annihilates the module. -/
private theorem IsThickening.isIso_unit_app_of_annihilates
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {i : RingedToposHom X Y} (hi : IsThickening i)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (h : ∀ (U : Y.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U),
      a ∈ RingHom.ker (i.fSharp.hom.app U).hom → ∀ m : M.val.obj U, a • m = 0) :
    IsIso ((pullbackAdjPushforwardModules i).unit.app M) := by
  obtain ⟨ff⟩ := hi.nonempty_pushforwardModules_fullyFaithful
  have : (pushforwardModules i).Full := ff.full
  have : (pushforwardModules i).Faithful := ff.faithful
  exact ((pullbackAdjPushforwardModules i).isIso_unit_app_iff_mem_essImage).2
    ((hi.essImage_pushforwardModules_iff _).2 h)

end Thickening

section Unit

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X Y}

/-- **For a thickening the unit of `i^* ⊣ i_*` is an epimorphism at every module.** The image of
the unit at `M` is a subobject of `i_*i^*M`, hence annihilated by the kernel of the structure
map, hence in the essential image of `i_*`; so the unit at it is an isomorphism, which splits the
image inclusion and makes the unit at `M` a composite of two epimorphisms. -/
theorem IsThickening.epi_unit_app (hi : IsThickening i)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    Epi ((pullbackAdjPushforwardModules i).unit.app M) := by
  obtain ⟨ff⟩ := hi.nonempty_pushforwardModules_fullyFaithful
  have : (pushforwardModules i).Full := ff.full
  have : (pushforwardModules i).Faithful := ff.faithful
  refine Adjunction.epi_unit_app_of_isIso_unit_app_image _ M (hi.isIso_unit_app_of_annihilates _ ?_)
  intro U a ha m
  refine Stacks.SheafOfModules.smul_eq_zero_of_mono
    (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (Abelian.image.ι _) U a ?_ m
  exact (hi.essImage_pushforwardModules_iff _).1
    ⟨(pullbackModules i.toModulesHom).obj M, ⟨Iso.refl _⟩⟩ U a ha

omit [HasSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **For a first order thickening the defining ideal is already a module on the source topos**:
the unit of `i^* ⊣ i_*` at it is an isomorphism.

The ideal is annihilated by itself, a product of two of its sections vanishing, so it lies in the
essential image of `i_*` by Stacks 08M3. This is the instance of the essential-image criterion
that factors the induced map of defining ideals. -/
theorem IsFirstOrderThickening.isIso_unit_app_ideal (hi : IsFirstOrderThickening i)
    (hI : IdealOfThickening i) :
    IsIso ((pullbackAdjPushforwardModules i).unit.app hI.I) := by
  refine hi.isThickening.isIso_unit_app_of_annihilates _ ?_
  intro U a ha m
  refine hI.incl_injective ?_
  rw [_root_.map_smul, _root_.map_zero]
  exact hi.2 U _ _ ha (hI.fSharp_incl_apply U m)

end Unit

namespace MorphismOfThickenings

section FirstOrder

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{v'', u'', w''}} {S' : RingedTopos.{v''', u''', w'''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{w''})] [S'.J.HasSheafCompose (forget RingCat.{w'''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{w'''} RingCat.{w'''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w'''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{w''}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (D : MorphismOfThickenings X X' S S')

/-- The source's `f^*J`, transported to an `O'`-module without identifying the equivalent topoi
of the upper thickening: `i_*f^*t^*J`. The lower ideal `J` is pulled back along `t` because `f^*`
consumes an `O_B`-module; for a first order `t` that pullback is `J` itself, read on `Sh(B)`, by
`Deformation.ToposThickening.IsFirstOrderThickening.isIso_unit_app_ideal`. -/
noncomputable abbrev reducedPullbackIdeal :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O) :=
  (pushforwardModules D.i).obj
    ((pullbackModules D.t.toModulesHom ⋙ pullbackModules D.f.toModulesHom).obj D.idealJ.I)

/-- **Stacks 08M7.** The canonical reduction map `(f')^*J ⟶ f^*J` of a morphism of thickenings of
ringed topoi, with the target read as the `O'`-module `i_*f^*t^*J`: the unit of `i^* ⊣ i_*`,
followed by the direct image of the canonical comparison
`Deformation.ToposThickening.MorphismOfThickenings.pullbackComparison` of the two iterated
pullbacks around the square.

The map needs no hypothesis on the square. When the upper arrow is a first order thickening it
is an epimorphism, by
`Deformation.ToposThickening.MorphismOfThickenings.firstOrderSurjection_epi`.

What is proved here is an epimorphism with a unique factorization, and not the source's
assertion, which is an equality `(f')^*J = f^*J` of the two pullbacks. The equality is not
available under the hypotheses of Situation 91.9.1. By
`Deformation.ToposThickening.IsThickening.essImage_pushforwardModules_iff` this map is an
isomorphism exactly when `I` annihilates `(f')^*J`; and what annihilates `(f')^*J` is the ideal
`J·O'` generated by the image of `J` under `(f')^♯`, since a product of two sections of `J` is
zero. So the source's equality amounts to `J·O' = I`, which is the strictness
`Deformation.ToposThickening.MorphismOfThickenings.IsStrict` of Stacks 08M9 — a further
hypothesis that Situation 91.9.1 does not make. The source also identifies the equivalent topoi
of the two thickenings, which this development does not do. (That reading of the source's
equality is a remark, not a formalized equivalence; nothing below depends on it.)

Nothing of the tag is lost by proving the epimorphism instead. The source uses the equality only
to turn the induced map `(f')^*J ⟶ I` into a map `f^*J ⟶ I`, and an epimorphism does exactly
that: it admits at most one such map, and
`Deformation.ToposThickening.MorphismOfThickenings.firstOrderIdealMap` exhibits one, so the
source's map is obtained and is unique. -/
@[stacks 08M7 "the first order reduction of the pullback of the lower ideal; the two upper \
topoi share their section universe, as the closed immersion carried by \
AlgebraicGeometry.ClosedRingedImmersion requires, the two lower ones staying independent"]
noncomputable def firstOrderSurjection :
    (pullbackModules D.f'.toModulesHom).obj D.idealJ.I ⟶ D.reducedPullbackIdeal :=
  (pullbackAdjPushforwardModules D.i).unit.app
      ((pullbackModules D.f'.toModulesHom).obj D.idealJ.I) ≫
    (pushforwardModules D.i).map (D.pullbackComparison.app D.idealJ.I).hom

set_option maxRecDepth 4000 in
/-- **Stacks 08M7.** When both thickenings are first order the canonical reduction map
`(f')^*J ⟶ f^*J` is surjective: the unit of `i^* ⊣ i_*` is an epimorphism at every module, and
the second factor is the direct image of an isomorphism.

First-orderness of `t` is not consumed: it is what makes `t^*J` the ideal `J` read on `Sh(B)`,
and that identification is built into `reducedPullbackIdeal`. -/
@[stacks 08M7 "surjectivity of the first order reduction; the two upper topoi share their \
section universe, as the closed immersion carried by \
AlgebraicGeometry.ClosedRingedImmersion requires, the two lower ones staying independent"]
theorem firstOrderSurjection_epi (hi : IsFirstOrderThickening D.i)
    (_ht : IsFirstOrderThickening D.t) : Epi D.firstOrderSurjection := by
  have h₁ : Epi ((pullbackAdjPushforwardModules D.i).unit.app
      ((pullbackModules D.f'.toModulesHom).obj D.idealJ.I)) :=
    hi.isThickening.epi_unit_app _
  have h₂ : IsIso ((pushforwardModules D.i).map (D.pullbackComparison.app D.idealJ.I).hom) :=
    ((pushforwardModules D.i).mapIso (D.pullbackComparison.app D.idealJ.I)).isIso_hom
  exact epi_comp' h₁ (@IsIso.epi_of_iso _ _ _ _ _ h₂)

/-- **Stacks 08M7.** When both thickenings are first order the induced map of defining ideals
`(f')^*J ⟶ I` factors uniquely through the canonical reduction `(f')^*J ⟶ f^*J`, giving the
source's map `f^*J ⟶ I`.

The factorization exists because the unit of `i^* ⊣ i_*` at `I` is an isomorphism, `I` being
annihilated by itself; it is unique because the reduction is an epimorphism. -/
@[stacks 08M7 "the first order factorization of the induced map of defining ideals; the two \
upper topoi share their section universe, as the closed immersion carried by \
AlgebraicGeometry.ClosedRingedImmersion requires, the two lower ones staying independent"]
noncomputable def firstOrderIdealMap (hi : IsFirstOrderThickening D.i)
    (ht : IsFirstOrderThickening D.t) :
    { g : D.reducedPullbackIdeal ⟶ D.idealI.I //
      D.firstOrderSurjection ≫ g = D.idealMap ∧
        ∀ g' : D.reducedPullbackIdeal ⟶ D.idealI.I,
          D.firstOrderSurjection ≫ g' = D.idealMap → g' = g } := by
  haveI : IsIso ((pullbackAdjPushforwardModules D.i).unit.app D.idealI.I) :=
    hi.isIso_unit_app_ideal D.idealI
  haveI : Epi D.firstOrderSurjection := D.firstOrderSurjection_epi hi ht
  have hfac : D.firstOrderSurjection ≫
      ((pushforwardModules D.i).map (D.pullbackComparison.app D.idealJ.I).inv ≫
        (pullbackModules D.i.toModulesHom ⋙ pushforwardModules D.i).map D.idealMap ≫
          inv ((pullbackAdjPushforwardModules D.i).unit.app D.idealI.I)) = D.idealMap := by
    have he : (pushforwardModules D.i).map (D.pullbackComparison.app D.idealJ.I).hom ≫
        (pushforwardModules D.i).map (D.pullbackComparison.app D.idealJ.I).inv = 𝟙 _ :=
      ((pushforwardModules D.i).mapIso (D.pullbackComparison.app D.idealJ.I)).hom_inv_id
    unfold firstOrderSurjection
    rw [Category.assoc, ← Category.assoc
        ((pushforwardModules D.i).map (D.pullbackComparison.app D.idealJ.I).hom), he,
      Category.id_comp, ← Category.assoc, IsIso.comp_inv_eq]
    exact ((pullbackAdjPushforwardModules D.i).unit.naturality D.idealMap).symm
  exact ⟨_, hfac, fun g' hg' => (cancel_epi D.firstOrderSurjection).1 (hg'.trans hfac.symm)⟩

end FirstOrder

end MorphismOfThickenings

end Deformation.ToposThickening

end
