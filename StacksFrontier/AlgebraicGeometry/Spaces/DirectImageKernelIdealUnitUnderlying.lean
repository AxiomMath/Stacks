module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageKernelIdealModuleCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart

/-!
# The underlying sheaf of sets of the unit comparison of `f_*f⁻¹f_*𝒪_X`

`StacksFrontier/AlgebraicGeometry/Spaces/DirectImageKernelIdealModuleCounit.lean` identifies the
third term of the direct image of the inverse image of the sequence `𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X` with
the unit module of the sheaf of rings `f_*f⁻¹f_*𝒪_X`, by an isomorphism
`AlgebraicGeometry.Space.directImageKernelIdealUnitIso` built from two instances of
`Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso`.  This file proves that
that isomorphism is **the identity on underlying sheaves of sets**, which is what lets a
consumer evaluate the direct image of the counit on a section.

## Main results

* `moduleSheafFunctor_map_directImageModules_map_pullbackModuleObjRestrictScalarsInv`: the
  direct image of the inverse-image comparison is the identity on underlying sheaves of sets.
* `moduleSheafFunctor_map_restrictScalars_map_pullbackModuleObjRestrictScalarsInv`: the same
  for the comparison read after a further restriction of scalars.
* `moduleSheafFunctor_map_directImageInverseImageRestrictScalarsInv`: the composite of the
  two, which is the shape of the comparison above.  Those three, and the equalities of
  underlying sheaves of sets that type them, live in `Stacks.Sheaves.RingedToposModules`.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_directImageKernelIdealUnitIso_hom`: **the
  comparison is the identity on underlying sheaves of sets.**
* `AlgebraicGeometry.Space.heq_directImageKernelIdealUnitIso_hom_val_app`: **the comparison is
  the identity on sections**, which is the form a consumer evaluating the direct image of the
  counit on a section needs.
* `Stacks.Sheaves.RingedToposModules.heq_val_app_of_moduleSheafFunctor_map_eq_eqToHom` and
  `val_app_eq_of_moduleSheafFunctor_map_eq_eqToHom`: the descent from the underlying sheaves of
  sets to sections, once and for all at variables.

## Implementation notes

**Every statement below is proved with the sites, the functors and the sheaves of rings all
variables, and reaches its geometric instance by instantiation alone.**  The equation that says
a morphism of sheaves of modules is the identity asks the kernel to identify the underlying
sheaf of sets of its source with that of its target, and through a `pullbackModuleObj` whose
arguments are geometric that identification exceeds the kernel's budget — it is a
`(kernel) deterministic timeout`, both for the direct-image layer and for the layer under a
further restriction of scalars.  With the arguments variables the same identification is
cheap, and instantiating a proved statement costs nothing.  This is the same discipline as
`Stacks.Sheaves.RingedToposModules.smul_pullbackModuleObj_restrictScalars`, whose
docstring records it for the sections form.

**The right-hand sides are `eqToHom`, not `𝟙`.**  Writing `𝟙` makes the statement's own type
the source-to-source hom type, so type-checking it is exactly the identification above;
`eqToHom` of a named equality of the two underlying sheaves of sets is typed by that equality
and asks for nothing.  The equalities are assembled from
`Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars` and
`Stacks.Sheaves.RingedToposModules.moduleSheaf_pullbackModuleObj_restrictScalars`, each of
which is a `rfl` lemma at variables.

**The sections statement is a `HEq`, and that is not a weakening.**  `Eq` would ask that the
sections of the comparison's source and of its target be *one type*, and deciding that at this
instantiation is the obstruction: the statement
`… .hom.val.app U x = (eqToHom …).hom.app U x` is a `whnf` timeout where the `HEq` beside it
costs a second.  The two types *are* equal -- by
`Stacks.Sheaves.RingedToposModules.moduleSheaf_directImageInverseImageRestrictScalars`
instantiated here, which is what types the `eqToHom` of the statement above -- so wherever a
consumer's own statement already types the two sides alike, `val_app_eq_of_…` turns the `HEq`
into that `Eq`; that is the "descend at the point of use" the `HEq` form exists to allow.

**The descent to sections is one lemma at variables, applied once.**  Writing the chain
(`moduleSheafFunctor_map_hom_app`, then the equation of sheaf morphisms, then the transport)
out at the geometric instance elaborates but is a `(kernel) deterministic timeout`; the same
chain proved at variables and *applied* is instant.  The section argument must be written at
the comparison's own spelling of its source: the complex's third term is definitionally the
same module, and asking for that identification is itself a `whnf` timeout.

**The comparison's factorisation is named.**  The comparison
`AlgebraicGeometry.Space.directImageKernelIdealUnitIso` is a composite of two
`Functor.mapIso`s of `Iso.symm`s; that its `hom` is the composite of the two `inv`s is `rfl`,
but not syntactically so, and
`AlgebraicGeometry.Space.directImageKernelIdealUnitIso_hom_eq` is what makes the rewrite
syntactic.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1), the direct image, and
  [Tag 03D2](https://stacks.math.columbia.edu/tag/03D2), the inverse image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.RingedToposModules

/-! ## One layer: the comparison under a further restriction of scalars -/

section PullbackLayer

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  [J.HasSheafCompose (forget RingCat.{ww})]

variable (J) (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {S S' : Sheaf K RingCat.{ww'}} (α : S' ⟶ S) (G : SheafOfModules.{ww'} S)

omit [J.HasSheafCompose (forget RingCat)] in
/-- The underlying sheaf of sets of a transported sheaf of modules is `Φ` of the underlying
sheaf of sets: the transported module is built so that its sections *are* the sections of `Φ`
of the underlying sheaf of sets. -/
lemma moduleSheaf_pullbackModuleObj (O : Sheaf K RingCat.{ww'}) (N : SheafOfModules.{ww'} O) :
    Sheaf.moduleSheaf (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O N) =
      Φ.obj (Sheaf.moduleSheaf O N) := rfl

omit [J.HasSheafCompose (forget RingCat)] in
/-- The two readings of the inverse image of `G`, each with its scalars further restricted
along `u`, have the same underlying sheaf of sets. -/
lemma moduleSheaf_restrictScalars_pullbackModuleObj_restrictScalars
    {R : Sheaf J RingCat.{ww}} (u : R ⟶ pullbackRingSheaf J Φ S') :
    Sheaf.moduleSheaf R ((SheafOfModules.restrictScalars u).obj
        (pullbackModuleObj J Φ S' ((SheafOfModules.restrictScalars α).obj G))) =
      Sheaf.moduleSheaf R ((SheafOfModules.restrictScalars u).obj
        ((SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α)).obj
          (pullbackModuleObj J Φ S G))) :=
  rfl

/-- **The inverse of the comparison of the inverse image with restriction of scalars, read
after a further restriction of scalars along `u`, is the identity on underlying sheaves of
sets.** -/
lemma moduleSheafFunctor_map_restrictScalars_map_pullbackModuleObjRestrictScalarsInv
    {R : Sheaf J RingCat.{ww}} (u : R ⟶ pullbackRingSheaf J Φ S') :
    (Sheaf.moduleSheafFunctor R).map ((SheafOfModules.restrictScalars u).map
        (pullbackModuleObjRestrictScalarsInv J Φ α G)) =
      eqToHom (moduleSheaf_restrictScalars_pullbackModuleObj_restrictScalars J Φ α G u) :=
  (moduleSheafFunctor_map_restrictScalars_map u _).trans
    ((moduleSheafFunctor_map_pullbackModuleObjRestrictScalarsInv J Φ α G).trans
      (eqToHom_refl _ _).symm)

end PullbackLayer

/-! ## Both layers: the direct image of the inverse-image comparison, then the comparison -/

section DirectImageLayer

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  {S S' : Sheaf K RingCat.{w'}} (α : S' ⟶ S) (G : SheafOfModules.{w'} S)

/-- The direct image of the two readings of the inverse image of `G` have the same underlying
sheaf of sets, the target being spelled at the direct-image layer so that it is the source of
`Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars_pullbackModuleObj_restrictScalars`
there. -/
lemma moduleSheaf_directImageModules_pullbackModuleObj_restrictScalars :
    Sheaf.moduleSheaf S' ((directImageModules f S').obj
        (pullbackModuleObj J f.inverseImage S' ((SheafOfModules.restrictScalars α).obj G))) =
      Sheaf.moduleSheaf S' ((SheafOfModules.restrictScalars (ringUnit f S')).obj
        (pullbackModuleObj K f.pushforward (inverseImageRingSheaf f S')
          ((SheafOfModules.restrictScalars (pullbackRingSheafMap J f.inverseImage α)).obj
            (pullbackModuleObj J f.inverseImage S G)))) :=
  congrArg f.pushforward.obj
    ((moduleSheaf_pullbackModuleObj_restrictScalars J f.inverseImage α G).trans
      (moduleSheaf_restrictScalars (pullbackRingSheafMap J f.inverseImage α) _).symm)

/-- **The direct image of the inverse of the comparison of the inverse image with restriction
of scalars is the identity on underlying sheaves of sets.** -/
lemma moduleSheafFunctor_map_directImageModules_map_pullbackModuleObjRestrictScalarsInv :
    (Sheaf.moduleSheafFunctor S').map ((directImageModules f S').map
        (pullbackModuleObjRestrictScalarsInv J f.inverseImage α G)) =
      eqToHom (moduleSheaf_directImageModules_pullbackModuleObj_restrictScalars f α G) :=
  (moduleSheafFunctor_map_directImageModules_map f S' _).trans
    ((congrArg f.pushforward.map
          (moduleSheafFunctor_map_pullbackModuleObjRestrictScalarsInv J f.inverseImage α G)).trans
      ((f.pushforward.map_id _).trans (eqToHom_refl _ _).symm))

/-- The underlying sheaf of sets of the direct image of the inverse image of `G`, and of the
same with both restrictions of scalars moved outwards, agree. -/
lemma moduleSheaf_directImageInverseImageRestrictScalars :
    Sheaf.moduleSheaf S' ((directImageModules f S').obj
        (pullbackModuleObj J f.inverseImage S' ((SheafOfModules.restrictScalars α).obj G))) =
      Sheaf.moduleSheaf S' ((SheafOfModules.restrictScalars (ringUnit f S')).obj
        ((SheafOfModules.restrictScalars (pullbackRingSheafMap K f.pushforward
            (pullbackRingSheafMap J f.inverseImage α))).obj
          (pullbackModuleObj K f.pushforward (pullbackRingSheaf J f.inverseImage S)
            (pullbackModuleObj J f.inverseImage S G)))) :=
  (moduleSheaf_directImageModules_pullbackModuleObj_restrictScalars f α G).trans
    (moduleSheaf_restrictScalars_pullbackModuleObj_restrictScalars K f.pushforward
      (pullbackRingSheafMap J f.inverseImage α) (pullbackModuleObj J f.inverseImage S G)
      (ringUnit f S'))

/-- **The two comparisons in turn are the identity on underlying sheaves of sets.**  This is
the shape of `AlgebraicGeometry.Space.directImageKernelIdealUnitIso`. -/
lemma moduleSheafFunctor_map_directImageInverseImageRestrictScalarsInv :
    (Sheaf.moduleSheafFunctor S').map
        ((directImageModules f S').map
            (pullbackModuleObjRestrictScalarsInv J f.inverseImage α G) ≫
          (SheafOfModules.restrictScalars (ringUnit f S')).map
            (pullbackModuleObjRestrictScalarsInv K f.pushforward
              (pullbackRingSheafMap J f.inverseImage α)
              (pullbackModuleObj J f.inverseImage S G))) =
      eqToHom (moduleSheaf_directImageInverseImageRestrictScalars f α G) :=
  (Functor.map_comp _ _ _).trans
    ((congrArg₂ (fun p q ↦ p ≫ q)
          (moduleSheafFunctor_map_directImageModules_map_pullbackModuleObjRestrictScalarsInv f α G)
          (moduleSheafFunctor_map_restrictScalars_map_pullbackModuleObjRestrictScalarsInv K
            f.pushforward (pullbackRingSheafMap J f.inverseImage α)
            (pullbackModuleObj J f.inverseImage S G) (ringUnit f S'))).trans
      (eqToHom_trans _ _))

end DirectImageLayer

end Stacks.Sheaves.RingedToposModules

/-! ## The descent from underlying sheaves of sets to sections -/

namespace CategoryTheory.Sheaf

universe ws vs us

variable {C : Type us} [Category.{vs} C] {J : GrothendieckTopology C}

/-- **A transport along an equality of sheaves of sets is the identity on sections**, up to the
equality of the two types of sections that the transport is along.  Proved by `cases` on the
equality, which is what makes it cheap: both sheaves are variables. -/
lemma heq_eqToHom_hom_app {A A' : Sheaf J (Type ws)} (h : A = A') (U : Cᵒᵖ)
    (x : A.obj.obj U) : HEq ((eqToHom h).hom.app U x) x := by
  cases h
  rfl

end CategoryTheory.Sheaf

namespace Stacks.Sheaves.RingedToposModules

universe wd vd ud

variable {C : Type ud} [Category.{vd} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{wd})] [J.HasSheafCompose (forget AddCommGrpCat.{wd})]
  {R : Sheaf J RingCat.{wd}} {M N : SheafOfModules.{wd} R}

omit [J.HasSheafCompose (forget RingCat)] in
/-- **A morphism of sheaves of modules whose underlying morphism of sheaves of sets is a
transport along an equality is the identity on sections**, up to that equality.

This is the whole descent from the underlying sheaves of sets to sections, and it is stated at
variables so that a geometric consumer pays only for the application; see the implementation
notes. -/
lemma heq_val_app_of_moduleSheafFunctor_map_eq_eqToHom (a : M ⟶ N)
    (h : Sheaf.moduleSheaf R M = Sheaf.moduleSheaf R N)
    (ha : (Sheaf.moduleSheafFunctor R).map a = eqToHom h) (U : Cᵒᵖ) (x : M.val.obj U) :
    HEq (a.val.app U x) x :=
  (heq_of_eq ((moduleSheafFunctor_map_hom_app a U x).symm.trans
      (Sheaf.hom_congr_app_apply ha U x))).trans (Sheaf.heq_eqToHom_hom_app h U x)

omit [J.HasSheafCompose (forget RingCat)] in
/-- **The same as an equality**, for a consumer that already has the section in both of the two
types: the two types of sections are equal, so a statement which types `x` and `y` alike and
asserts `HEq x y` identifies them, and the `HEq` above becomes an `Eq`. -/
lemma val_app_eq_of_moduleSheafFunctor_map_eq_eqToHom (a : M ⟶ N)
    (h : Sheaf.moduleSheaf R M = Sheaf.moduleSheaf R N)
    (ha : (Sheaf.moduleSheafFunctor R).map a = eqToHom h) (U : Cᵒᵖ) (x : M.val.obj U)
    (y : N.val.obj U) (hxy : HEq x y) : a.val.app U x = y :=
  eq_of_heq ((heq_val_app_of_moduleSheafFunctor_map_eq_eqToHom a h ha U x).trans hxy)

end Stacks.Sheaves.RingedToposModules

/-! ## The comparison of `f_*f⁻¹f_*𝒪_X` with a unit module -/

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The factorisation of `AlgebraicGeometry.Space.directImageKernelIdealUnitIso` into the two
comparisons, as a named equation; see the implementation notes for why it is named. -/
theorem directImageKernelIdealUnitIso_hom_eq (f : X ⟶ Y) :
    (directImageKernelIdealUnitIso B S hS f).hom =
      (directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)).map
          (pullbackModuleObjRestrictScalarsInv (SmallEtale.topology B S hS X.1)
            (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
            (structureSharp B S hS f)
            (SheafOfModules.unit (structureRingSheafDirectImage B S hS f))) ≫
        (SheafOfModules.restrictScalars
            (ringUnit (smallEtaleRingedToposHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y))).map
          (pullbackModuleObjRestrictScalarsInv (SmallEtale.topology B S hS Y.1)
            (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
            (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
              (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
              (structureSharp B S hS f))
            (pullbackModuleObj (SmallEtale.topology B S hS X.1)
              (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
              (structureRingSheafDirectImage B S hS f)
              (SheafOfModules.unit (structureRingSheafDirectImage B S hS f)))) := rfl

/-- **The comparison identifying `f_*f⁻¹f_*𝒪_X` with a unit module is the identity on
underlying sheaves of sets**, at an arbitrary morphism of algebraic spaces.  Both of its
factors are, by the composite lemma
`moduleSheafFunctor_map_directImageInverseImageRestrictScalarsInv` read at this morphism.

No type is restated: the equality of the two underlying sheaves of sets that types the
`eqToHom` is that lemma's own, instantiated here.  Writing the two objects out instead
exhausts the heartbeat budget. -/
theorem moduleSheafFunctor_map_directImageKernelIdealUnitIso_hom (f : X ⟶ Y) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        (directImageKernelIdealUnitIso B S hS f).hom =
      eqToHom (moduleSheaf_directImageInverseImageRestrictScalars
        (smallEtaleRingedToposHom B S hS f).toToposHom (structureSharp B S hS f)
        (SheafOfModules.unit (structureRingSheafDirectImage B S hS f))) :=
  (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        (directImageKernelIdealUnitIso_hom_eq B S hS f)).trans
    (moduleSheafFunctor_map_directImageInverseImageRestrictScalarsInv
      (smallEtaleRingedToposHom B S hS f).toToposHom (structureSharp B S hS f)
      (SheafOfModules.unit (structureRingSheafDirectImage B S hS f)))

/-- **The comparison identifying `f_*f⁻¹f_*𝒪_X` with a unit module is the identity on
sections**, at an arbitrary morphism of algebraic spaces: a section of the third term of the
direct image of the inverse image of the sequence `𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X` is carried to itself.

This is `AlgebraicGeometry.Space.moduleSheafFunctor_map_directImageKernelIdealUnitIso_hom` read
on a section, by one application of
`Stacks.Sheaves.RingedToposModules.heq_val_app_of_moduleSheafFunctor_map_eq_eqToHom`.  It is a
`HEq`, and `val_app_eq_of_moduleSheafFunctor_map_eq_eqToHom` is the form that gives an `Eq`
where the consumer's own statement types both sides alike; see the implementation notes for why
the `Eq` cannot be stated here. -/
theorem heq_directImageKernelIdealUnitIso_hom_val_app (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : ((directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj
        (pullbackModuleObj (SmallEtale.topology B S hS X.1)
          (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
          (structureRingSheaf B S hS Y)
          ((SheafOfModules.restrictScalars (structureSharp B S hS f)).obj
            (SheafOfModules.unit (structureRingSheafDirectImage B S hS f))))).val.obj U) :
    HEq ((directImageKernelIdealUnitIso B S hS f).hom.val.app U x) x :=
  heq_val_app_of_moduleSheafFunctor_map_eq_eqToHom _ _
    (moduleSheafFunctor_map_directImageKernelIdealUnitIso_hom B S hS f) U x

end AlgebraicGeometry.Space

end
