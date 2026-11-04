module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingInverseImageKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposSheafSetsFibreSquare
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickenings

/-!
# The inverse image of a first order thickening of the base

Let `t : (Sh(ℬ), O_ℬ) ⟶ (Sh(ℬ'), O_{ℬ'})` be a first order thickening of ringed topoi with
square-zero ideal `𝒥 = Ker(t^♯)`, and let `f' : (Sh(D), O') ⟶ (Sh(ℬ'), O_{ℬ'})` be a morphism of
ringed topoi. Pulling the lower row of the square of Stacks 08M7 back along `f'` presents the
base on the thickened topos: the sheaves of rings

`f⁻¹O_{ℬ'} = (f')⁻¹O_{ℬ'}` and `f⁻¹O_ℬ = (f')⁻¹t_*O_ℬ`

on `Sh(D)` — the identification of `f⁻¹` with `(f')⁻¹` being the one Situation 08M7 makes — the
reduction `(f')⁻¹(t^♯)` between them, and the ideal `f⁻¹𝒥 = (f')⁻¹𝒥`.

This file proves that this is again a square-zero extension of sheaves of rings, in exactly the
form the flatness criterion of Stacks 08M4 consumes: the reduction is locally surjective and the
ideal is, section by section, exactly its kernel.

## Main definitions

* `Deformation.ToposThickening.inverseImageBaseRing` and `.inverseImageReducedBaseRing`:
  `f⁻¹O_{ℬ'}` and `f⁻¹O_ℬ`, read on the thickened topos.
* `Deformation.ToposThickening.inverseImageBaseReduction`: the reduction `f⁻¹O_{ℬ'} ⟶ f⁻¹O_ℬ`.

## Main results

* `Deformation.ToposThickening.isLocallySurjective_inverseImageBaseReduction`: the reduction is
  locally surjective.
* `Deformation.ToposThickening.FirstOrderThickening.isPullback_incl`: the square-zero ideal of a
  first order thickening is, on underlying sheaves of sets, the kernel of the structure map.
* `Deformation.ToposThickening.exists_inverseImageBaseIdeal`: **the ideal datum.** There is a
  sheaf of `f⁻¹O_ℬ`-modules included in `f⁻¹O_{ℬ'}` whose local sections are exactly the local
  sections killed by the reduction.

## Implementation notes

The ideal is the inverse image of `𝒥` **as a module over `t_*O_ℬ`**, which is the form the
square-zero ideal of `Deformation.ToposThickening.FirstOrderThickening` is carried in; its
inverse image is therefore a module over `f⁻¹t_*O_ℬ` with no descent along the reduction needed.
The comparison of the inverse image of a restriction of scalars with the restriction of scalars
of the inverse image is
`Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso`, and the inverse image
of a unit module is the unit module of the inverse-image sheaf of rings on the nose
(`Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso`); both are the identity on underlying
sheaves of sets, which is what makes the sectionwise statements transport by `rfl`.

Nothing is computed on sections of the inverse image — those admit no description. The two
sectionwise statements are readings of one pullback square of sheaves of sets, the square
exhibiting `𝒥` as the kernel of `t^♯`, carried along the inverse image because it is left exact
(`Stacks.Sheaves.ToposPullback.isPullback_map_pullbackRingSheafMap`). The square itself is
produced from the two characterising fields of
`Deformation.ToposThickening.FirstOrderThickening` by
`Stacks.Sheaves.ToposPullback.isPullback_terminal_of_sections`.

The reduction is stated as a morphism of sheaves of *rings* given together with the equation
identifying it with the inverse image of the structure map, rather than as that inverse image
itself. The two spellings of the same morphism — through the full faithfulness of forgetting
commutativity, and through the inverse image of sheaves of rings — are not definitionally
equal, and taking the morphism as a parameter lets the equation be substituted away once
instead of being transported through every statement.

## References

* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPullback (pullbackModuleObj pullbackRingSheaf pullbackRingSheafMap
  pullbackModuleUnitIso isPullback_terminal_of_sections existsUnique_sections_of_isPullback
  sections_comp_eq_zero_of_isPullback isPullback_map_pullbackRingSheafMap)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor inverseImageCommRingFunctor
  inverseImageRingSheaf)
open Stacks.Sheaves.RingedToposModules (inverseImageModules pullbackModuleObjRestrictScalarsIso)

universe v u v' u' w vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

section Kernel

variable {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  {t : RingedToposHom S S'}

/-- **The inclusion of the square-zero ideal of a first order thickening, on underlying sheaves
of sets.** The underlying sheaf of sets of the unit module of a sheaf of rings is the underlying
sheaf of sets of that sheaf of rings, and the declared target here is the second spelling: a
composite written with the first is not type-correct at the `implicit` transparency level, so
the spelling is crossed once, inside this definition. -/
noncomputable def FirstOrderThickening.inclSheafSets (ht : FirstOrderThickening t) :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)
        ((SheafOfModules.restrictScalars ((sheafCompose S'.J
          (forget₂ CommRingCat.{wS'} RingCat.{wS'})).map t.fSharp)).obj ht.I) ⟶
      Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf S'.O) :=
  (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map ht.incl

/-- **The square-zero ideal of a first order thickening is the kernel of its structure map**, as
a pullback square of sheaves of sets: the ideal is the fibre of the structure map over the zero
section.

This is the shape in which the kernel is carried along the inverse image of a morphism of
topoi, where no section of the inverse image can be named. -/
theorem FirstOrderThickening.isPullback_incl (ht : FirstOrderThickening t) :
    IsPullback ht.inclSheafSets (terminal.from _)
      ((sheafCompose S'.J (forget RingCat.{wS'})).map
        ((Stacks.forgetCommRingSheaf S'.J).map t.fSharp))
      (Sheaf.ringZeroHom (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor t.toToposHom).obj S.O))) := by
  refine isPullback_terminal_of_sections _ _ _ ?_ (fun U b b' h ↦ ht.injective U h)
    fun U a ha ↦ ht.exists_ideal_section U a ha
  refine hom_ext_sections fun U b ↦ ?_
  rw [(Sheaf.sectionsFunctor S'.J U).map_comp_apply]
  exact (ht.kernel U _).2 ⟨b, rfl⟩

end Kernel

section InverseImageBase

variable {X' : RingedTopos.{v', u', w}} {S : RingedTopos.{vS, uS, wS}}
  {S' : RingedTopos.{vS', uS', wS'}}
  [X'.J.HasSheafCompose (forget RingCat.{w})] [S.J.HasSheafCompose (forget RingCat.{wS})]
  [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  (t : RingedToposHom S S') (f' : RingedToposHom X' S')

/-- **`f⁻¹O_{ℬ'}`**, the inverse image along `f'` of the structure sheaf of the thickened base.
It is the source of the inverse-image form of the structure map of `f'`. -/
noncomputable abbrev inverseImageBaseRing : Sheaf X'.J CommRingCat.{w} :=
  (inverseImageCommRingFunctor f'.toToposHom).obj S'.O

/-- **`f⁻¹O_ℬ` read on the thickened topos**: the inverse image along `f'` of the direct image
`t_*O_ℬ` of the structure sheaf of the base. This is the presentation of `f⁻¹O_ℬ` that Situation
08M7's identification of `f⁻¹` with `(f')⁻¹` produces. -/
noncomputable abbrev inverseImageReducedBaseRing : Sheaf X'.J CommRingCat.{w} :=
  (inverseImageCommRingFunctor f'.toToposHom).obj
    ((pushforwardCommRingFunctor t.toToposHom).obj S.O)

/-- **The reduction `f⁻¹O_{ℬ'} ⟶ f⁻¹O_ℬ`**, the inverse image along `f'` of the structure map of
the thickening of the base. -/
noncomputable abbrev inverseImageBaseReduction :
    inverseImageBaseRing f' ⟶ inverseImageReducedBaseRing t f' :=
  (inverseImageCommRingFunctor f'.toToposHom).map t.fSharp

omit [S'.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- **The reduction `f⁻¹O_{ℬ'} ⟶ f⁻¹O_ℬ` is locally surjective.** Local surjectivity of a
morphism of sheaves of rings is a property of the underlying morphism of sheaves of sets, and
the inverse image of a morphism of topoi preserves epimorphisms of sheaves of sets.

The two sheafification hypotheses are the ones
`Stacks.Sheaves.ToposPushforward.isLocallySurjective_inverseImageCommRingFunctor_map` reads an
epimorphism of the underlying sheaves of sets back as local surjectivity with: they are on the
*thickened* site, and they are about sheaves of abelian groups rather than of sets. They are
carried by the theorem rather than by the section's variable block so that nothing else in the
file acquires them. -/
theorem isLocallySurjective_inverseImageBaseReduction [HasSheafify X'.J AddCommGrpCat.{w}]
    [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] (ht : FirstOrderThickening t) :
    Presheaf.IsLocallySurjective X'.J (inverseImageBaseReduction t f').hom :=
  Stacks.Sheaves.ToposPushforward.isLocallySurjective_inverseImageCommRingFunctor_map
    f'.toToposHom t.fSharp ht.surjective

/-- Composition of morphisms of sheaves of modules, on sections. -/
theorem comp_val_app {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N P : SheafOfModules.{w} R} (g₁ : M ⟶ N) (g₂ : N ⟶ P)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (g₁ ≫ g₂).val.app U x = g₂.val.app U (g₁.val.app U x) := rfl

/-- **A restriction of scalars along equal ring maps is the identity on sections.** The
underlying presheaf of abelian groups of a restriction of scalars is the one it started from,
so the transport along an equality of the two ring maps does nothing to a section. -/
theorem restrictScalars_eqToHom_val_app {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{w}} {m₁ m₂ : R ⟶ R'} (h : m₁ = m₂)
    (F : SheafOfModules.{w} R') (U : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars m₁).obj F).val.obj U) :
    (eqToHom (congrArg (fun m ↦ (SheafOfModules.restrictScalars m).obj F) h)).val.app U x = x := by
  subst h
  rfl

omit [X'.J.HasSheafCompose (forget AddCommGrpCat)] [S'.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The underlying morphism of sheaves of rings of the reduction, in the spelling the inverse
image of sheaves of rings produces it in. The two spellings — through the full faithfulness of
forgetting commutativity, and through the inverse image of sheaves of rings — are the same
morphism but not definitionally equal. -/
theorem ringMap_inverseImageBaseReduction :
    (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        (inverseImageBaseReduction t f') =
      pullbackRingSheafMap X'.J f'.toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf S'.J).map t.fSharp) :=
  Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap X'.J
    f'.toToposHom.inverseImage t.fSharp

/-- **`f⁻¹𝒥`**, the inverse image of the square-zero ideal of the thickening of the base, as a
module over `f⁻¹O_ℬ`. The ideal of a first order thickening is carried as a module over the
direct image of the reduced structure sheaf, so its inverse image is a module over `f⁻¹O_ℬ`
with no descent along the reduction needed. -/
noncomputable abbrev inverseImageBaseIdeal (ht : FirstOrderThickening t) :
    SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f')) :=
  pullbackModuleObj X'.J f'.toToposHom.inverseImage
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor t.toToposHom).obj S.O))
    ht.I

/-- **The inclusion `f⁻¹𝒥 ⟶ f⁻¹O_{ℬ'}`**: the inverse image of the inclusion of the square-zero
ideal, read through the comparison of the inverse image of a restriction of scalars with the
restriction of scalars of the inverse image, and through the identification of the inverse image
of a unit module with the unit module of the inverse-image sheaf of rings. -/
noncomputable def inverseImageBaseIdealIncl (ht : FirstOrderThickening t) :
    (SheafOfModules.restrictScalars ((sheafCompose X'.J
          (forget₂ CommRingCat.{w} RingCat.{w})).map (inverseImageBaseReduction t f'))).obj
        (inverseImageBaseIdeal t f' ht) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')) :=
  eqToHom (congrArg (fun m ↦ (SheafOfModules.restrictScalars m).obj
      (inverseImageBaseIdeal t f' ht)) (ringMap_inverseImageBaseReduction t f')) ≫
    (pullbackModuleObjRestrictScalarsIso X'.J f'.toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf S'.J).map t.fSharp) ht.I).hom ≫
      (inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
          ht.incl ≫
        (pullbackModuleUnitIso X'.J f'.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv

/-- The inclusion of `f⁻¹𝒥` is, on sections, the inverse image of the inclusion of `𝒥`: the two
comparison isomorphisms it is composed with are the identity on underlying sheaves of sets, and
the transport along the two spellings of the reduction does nothing to a section. -/
theorem inverseImageBaseIdealIncl_val_app (ht : FirstOrderThickening t) (U : X'.Cᵒᵖ)
    (a : (inverseImageBaseIdeal t f' ht).val.obj U) :
    (inverseImageBaseIdealIncl t f' ht).val.app U a =
      (Sheaf.sectionsFunctor X'.J U).map
        (f'.toToposHom.inverseImage.map ht.inclSheafSets) a :=
  congrArg (fun y ↦ (((pullbackModuleObjRestrictScalarsIso X'.J f'.toToposHom.inverseImage
      ((Stacks.forgetCommRingSheaf S'.J).map t.fSharp) ht.I).hom ≫
      (inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
          ht.incl ≫
        (pullbackModuleUnitIso X'.J f'.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv).val.app U) y)
    (restrictScalars_eqToHom_val_app (ringMap_inverseImageBaseReduction t f')
      (inverseImageBaseIdeal t f' ht) U a)

/-- **The inclusion of `f⁻¹𝒥` is killed by the reduction.** -/
theorem inverseImageBaseReduction_inverseImageBaseIdealIncl (ht : FirstOrderThickening t)
    (U : X'.Cᵒᵖ) (a : (inverseImageBaseIdeal t f' ht).val.obj U) :
    (inverseImageBaseReduction t f').hom.app U
        (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
          (inverseImageBaseIdealIncl t f' ht).val.app U a) = 0 := by
  rw [inverseImageBaseIdealIncl_val_app]
  have h := sections_comp_eq_zero_of_isPullback X'.J f'.toToposHom.inverseImage
    ((Stacks.forgetCommRingSheaf S'.J).map t.fSharp) _ ht.isPullback_incl U a
  rwa [← ringMap_inverseImageBaseReduction t f'] at h

/-- **A section of `f⁻¹O_{ℬ'}` killed by the reduction is the image of exactly one section of
`f⁻¹𝒥`.** The ideal is, section by section, precisely the kernel of the reduction. -/
theorem existsUnique_inverseImageBaseIdeal_section (ht : FirstOrderThickening t) (U : X'.Cᵒᵖ)
    (x : (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U)
    (hx : (inverseImageBaseReduction t f').hom.app U x = 0) :
    ∃! a : (inverseImageBaseIdeal t f' ht).val.obj U,
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
        (inverseImageBaseIdealIncl t f' ht).val.app U a) = x := by
  obtain ⟨a, ha, huniq⟩ := existsUnique_sections_of_isPullback X'.J f'.toToposHom.inverseImage
    ((Stacks.forgetCommRingSheaf S'.J).map t.fSharp) _ ht.isPullback_incl U x
    (by rwa [← ringMap_inverseImageBaseReduction t f'])
  exact ⟨a, (inverseImageBaseIdealIncl_val_app t f' ht U a).trans ha,
    fun b hb ↦ huniq b ((inverseImageBaseIdealIncl_val_app t f' ht U b).symm.trans hb)⟩

end InverseImageBase

section StructureMap

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (comm : f'.comp i = t.comp f)

/-- **The comparison `t_*f_*O ≅ (t ∘ f)_*O` of iterated direct images**, for morphisms of ringed
topoi. This is `Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso`, whose target is
written with the composite of the underlying morphisms of topoi; the declared target here is
written with the underlying morphism of topoi of the composite, which is the spelling the
structure map of a composite of morphisms of ringed topoi carries. The two are the same
morphism of topoi, but a composite mixing the two spellings is not type-correct at the
`implicit` transparency level, so the spelling is crossed once, here. -/
noncomputable def ringedPushforwardCompIso (f : RingedToposHom X S) (t : RingedToposHom S S') :
    (pushforwardCommRingFunctor t.toToposHom).obj
        ((pushforwardCommRingFunctor f.toToposHom).obj X.O) ≅
      (pushforwardCommRingFunctor (t.comp f).toToposHom).obj X.O :=
  Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso f.toToposHom t.toToposHom X.O

include comm

/-- **The structure map of `f`, pushed forward to the thickened base**: the map
`t_*O_ℬ ⟶ f'_*i_*O` obtained from `f^♯ : O_ℬ ⟶ f_*O` by applying `t_*` and identifying
`t_*f_*O` with `f'_*i_*O`, the two iterated direct images of the commuting square. -/
noncomputable def pushforwardStructureComparison :
    (pushforwardCommRingFunctor t.toToposHom).obj S.O ⟶
      (pushforwardCommRingFunctor f'.toToposHom).obj
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) :=
  (pushforwardCommRingFunctor t.toToposHom).map f.fSharp ≫
    (ringedPushforwardCompIso f t).hom ≫
      eqToHom (congrArg (fun m : RingedToposHom X S' ↦
        (pushforwardCommRingFunctor m.toToposHom).obj X.O) comm.symm) ≫
      (ringedPushforwardCompIso i f').inv

/-- **The two readings of the structure map of the composite around the square agree.** The
structure map of the thickening of the base followed by the pushed-forward structure map of `f`
is the structure map of `f'` followed by the direct image of the structure map of the
thickening: both are the structure map of the composite `f' ∘ i = t ∘ f`, read through the
comparison of iterated direct images. -/
theorem fSharp_comp_pushforwardStructureComparison :
    t.fSharp ≫ pushforwardStructureComparison i t f f' comm =
      f'.fSharp ≫ (pushforwardCommRingFunctor f'.toToposHom).map i.fSharp := by
  have key : ∀ (k : RingedToposHom X S') (hk : f'.comp i = k),
      k.fSharp ≫ eqToHom (congrArg (fun m : RingedToposHom X S' ↦
          (pushforwardCommRingFunctor m.toToposHom).obj X.O) hk.symm) =
        (f'.comp i).fSharp := by
    intro k hk
    subst hk
    exact Category.comp_id _
  have hleft : (t.fSharp ≫ (pushforwardCommRingFunctor t.toToposHom).map f.fSharp) ≫
      (ringedPushforwardCompIso f t).hom = (t.comp f).fSharp :=
    Category.assoc _ _ _
  have hright : (f'.comp i).fSharp = (f'.fSharp ≫
      (pushforwardCommRingFunctor f'.toToposHom).map i.fSharp) ≫
        (ringedPushforwardCompIso i f').hom :=
    (Category.assoc _ _ _).symm
  rw [pushforwardStructureComparison]
  simp only [← Category.assoc]
  rw [hleft, key (t.comp f) comm, hright, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]

/-- **The structure map `f⁻¹O_ℬ ⟶ i_*O` of `f`, read on the thickened topos.** It is the adjoint
transpose of `Deformation.ToposThickening.pushforwardStructureComparison`, and it is the map
along which flatness of an `i_*O`-module over the base is measured. -/
noncomputable def inverseImageReducedStructureMap :
    inverseImageReducedBaseRing t f' ⟶ (pushforwardCommRingFunctor i.toToposHom).obj X.O :=
  ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction f'.toToposHom).homEquiv _ _).symm
    (pushforwardStructureComparison i t f f' comm)

omit [X'.J.HasSheafCompose (forget AddCommGrpCat)] [S'.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- **The square of structure maps on the thickened topos commutes**: the reduction of the
inverse image of the base followed by the structure map of `f` is the structure map of `f'`
followed by the structure map of the thickening `i`. -/
theorem inverseImageBaseReduction_comp_inverseImageReducedStructureMap :
    inverseImageBaseReduction t f' ≫ inverseImageReducedStructureMap i t f f' comm =
      f'.fSharpInverseImage ≫ i.fSharp := by
  refine ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction f'.toToposHom).homEquiv
    S'.O ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    inverseImageReducedStructureMap, Equiv.apply_symm_apply,
    RingedToposHom.fSharpInverseImage, Equiv.apply_symm_apply,
    fSharp_comp_pushforwardStructureComparison]

end StructureMap

end Deformation.ToposThickening

end
