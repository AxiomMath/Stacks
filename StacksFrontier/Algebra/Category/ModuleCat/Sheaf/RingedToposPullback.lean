module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of sheaves of modules along a morphism of ringed topoi, and its adjunction

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi in the sense of
Stacks 01D3, i.e. an `AlgebraicGeometry.RingedToposHom`: a morphism of the underlying topoi
together with a map `f♯ : O_D ⟶ f_*O_C` of structure sheaves, and nothing else.
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPushforwardComp.lean` supplies the
direct image `f_*` of sheaves of modules for such a morphism. This file supplies the pullback
`f^* G = O_C ⊗_{f⁻¹O_D} f⁻¹G` and the adjunction `f^* ⊣ f_*`.

## The engine: the two forms of the structure map

`Stacks.Sheaves.RingedToposModules` already builds a pullback and an adjunction, but for a
*different* structure, `Stacks.Sheaves.RingedToposModules.RingedToposHom`, which carries four
fields: the morphism of topoi, the structure map in its direct-image form `O_D ⟶ f_*O_C` and
in its inverse-image form `f⁻¹O_D ⟶ O_C`, both at the `RingCat` level, together with the
equation making the two adjunct.

The content of this file is that **those two extra fields are not extra data**: for a two-field
`AlgebraicGeometry.RingedToposHom` the inverse-image form is the adjunct
`fSharpInverseImageRing` of `fSharp` under the ring-level adjunction `f⁻¹ ⊣ f_*` of
Stacks 00YV, and the equation then holds by construction
(`fSharpInverseImageRing_adjunct`). So a two-field morphism of ringed topoi gives rise to a
four-field one, `toModulesHom`, and the pullback and the adjunction can be *transported* rather
than rebuilt. The pullback is therefore not redefined here at all: the pullback along a
two-field morphism of ringed topoi *is*
`Stacks.Sheaves.RingedToposModules.pullbackModules f.toModulesHom`, the one definition of
Stacks 03D6 part (2), and that is the spelling used throughout.

What is not inherited is the direct image: the four-field development defines it as a
restriction of scalars followed by a direct image, whereas
`AlgebraicGeometry.RingedToposHom.pushforwardModules` is a direct image followed by a
restriction of scalars. The two agree, but not definitionally; `toModulesPushforwardIso`
identifies them. Its components are the identity on underlying sheaves of sets, and the only
genuine input is that the two forms of the structure map are adjunct — which is exactly where
`fSharpInverseImageRing_adjunct` is used.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing`: the inverse-image form
  `f⁻¹O_D ⟶ O_C` of the structure map, at the level of sheaves of rings.
* `AlgebraicGeometry.RingedToposHom.toModulesHom`: the four-field morphism of ringed topoi of
  the modules development determined by a two-field one.
* `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`: the identification of the two
  direct images of sheaves of modules. `toModulesSections` and `ofModulesSections` read a
  section of the one as a section of the other, which is what makes the two module structures
  comparable.
* `AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`: the adjunction
  `f^* ⊣ f_*`, i.e. Stacks 03D7 for such a morphism.

## Main results

* `AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing_adjunct`: on underlying sheaves of
  sets, the direct-image form of the structure map is the adjunct of its inverse-image form.
* `AlgebraicGeometry.RingedToposHom.pushforwardModules_smul`: the scalar action on a direct
  image of sheaves of modules is the restriction along `f♯` of the direct-image action of
  Stacks 03D1.
* `AlgebraicGeometry.RingedToposHom.pullbackModules_additive`: the pullback is additive, so it
  can be applied degreewise to complexes.
* `AlgebraicGeometry.RingedToposHom.pushforwardModules_preservesLimitsOfSize` and
  `.pushforwardModules_preservesFiniteLimits`: the direct image commutes with all limits and is
  in particular left exact.
* `AlgebraicGeometry.RingedToposHom.pullbackModules_preservesColimitsOfSize` and
  `.pullbackModules_preservesFiniteColimits`: the pullback commutes with all colimits and is in
  particular right exact.
* `Stacks.Sheaves.ToposPushforward.ringSheafMap_ringImageAdjunction_homEquiv`: the adjunction
  bijection for sheaves of rings is computed by the adjunction bijection for the underlying
  sheaves of sets.

## Implementation notes

The two ringed topoi keep independent universes for their sections, as they do for the direct
image; nothing here forces them together. The sheafification hypotheses
`HasWeakSheafify X.J AddCommGrpCat` and `X.J.WEqualsLocallyBijective AddCommGrpCat` are those
of `Stacks.Sheaves.RingedToposModules.extendScalars`, and they are required of the *source*
topos only, since extension of scalars happens there. `HasWeakSheafify` rather than
`HasSheafify` is what the construction needs, and is what is assumed.

The two underlying sheaves of sets of the two direct images are equal on the nose, but the
identification is expensive for the elaborator to re-derive, and `Sheaf.moduleAddObj` is *not*
definitionally the addition on sections (the product comparison it goes through is sealed). So
the identification is recorded once, as `toModulesSections` and `ofModulesSections`, and the
identity morphism of `toModulesPushforwardIsoApp` is written at the direct image of the
underlying sheaf of sets rather than as `𝟙 _` — with `𝟙 _` the unifier has to compare the two
spellings and exhausts its heartbeats.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03DC](https://stacks.math.columbia.edu/tag/03DC)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPushforward

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))

/-- The adjunction bijection of `f⁻¹ ⊣ f_*` for sheaves of rings is computed by the adjunction
bijection for the underlying sheaves of sets: the underlying map of the adjunct of `φ` is the
adjunct of the underlying map of `φ`. Both sides are the unit followed by the direct image of
`φ`, and on sections the ring-level unit and inverse image are the set-level ones. -/
lemma ringSheafMap_ringImageAdjunction_homEquiv (O : Sheaf K RingCat.{ww'})
    (O' : Sheaf J RingCat.{ww}) (φ : inverseImageRingSheaf f O ⟶ O') :
    (sheafCompose K (forget RingCat.{ww'})).map ((ringImageAdjunction f).homEquiv O O' φ) =
      f.adj.homEquiv (Sheaf.ringSheaf O) (Sheaf.ringSheaf O')
        ((sheafCompose J (forget RingCat.{ww})).map φ) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

end Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- The inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map of a morphism of ringed topoi,
at the level of sheaves of rings: the adjunct of `f♯ : O_D ⟶ f_*O_C` under the adjunction
`f⁻¹ ⊣ f_*` for sheaves of rings.

This is the map along which scalars are extended to form the pullback of a sheaf of modules.
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage` is the corresponding map at the level of
sheaves of *commutative* rings, obtained from the same `f♯` through the adjunction for sheaves
of commutative rings; the identification of the two is not needed here and is not recorded. -/
@[sga "6 0 4.4"]
def fSharpInverseImageRing (f : RingedToposHom X Y) :
    inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf X.O :=
  ((ringImageAdjunction f.toToposHom).homEquiv (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).symm f.fSharpRing

/-- On underlying sheaves of sets, the direct-image form `f♯ : O_D ⟶ f_*O_C` of the structure
map is the adjunct, under `f⁻¹ ⊣ f_*` for sheaves of sets, of the inverse-image form
`f⁻¹O_D ⟶ O_C`. This is the equation that the four-field morphism of ringed topoi of the
modules development carries as a field; here it holds by construction. -/
lemma fSharpInverseImageRing_adjunct (f : RingedToposHom X Y) :
    (sheafCompose Y.J (forget RingCat.{w'})).map f.fSharpRing =
      f.toToposHom.adj.homEquiv (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImageRing) :=
  (congrArg (fun m ↦ (sheafCompose Y.J (forget RingCat.{w'})).map m)
    (((ringImageAdjunction f.toToposHom).homEquiv (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).apply_symm_apply f.fSharpRing).symm).trans
    (ringSheafMap_ringImageAdjunction_homEquiv f.toToposHom _ _ f.fSharpInverseImageRing)

/-- The four-field morphism of ringed topoi of the modules development determined by a
morphism of ringed topoi in the sense of Stacks 01D3. The two extra fields are the
inverse-image form of the structure map and the equation making it adjunct to the direct-image
form, and both are supplied by `fSharpInverseImageRing` and
`fSharpInverseImageRing_adjunct`. -/
def toModulesHom (f : RingedToposHom X Y) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom X Y where
  toToposHom := f.toToposHom
  fSharp := f.fSharpRing
  fSharpInverseImage := f.fSharpInverseImageRing
  fSharp_adjunct := f.fSharpInverseImageRing_adjunct

@[simp]
lemma toModulesHom_toToposHom (f : RingedToposHom X Y) :
    f.toModulesHom.toToposHom = f.toToposHom := rfl

@[simp]
lemma toModulesHom_fSharp (f : RingedToposHom X Y) :
    f.toModulesHom.fSharp = f.fSharpRing := rfl

@[simp]
lemma toModulesHom_fSharpInverseImage (f : RingedToposHom X Y) :
    f.toModulesHom.fSharpInverseImage = f.fSharpInverseImageRing := rfl

section Modules

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]

/-- A section of the direct image of a sheaf of modules taken through the four-field morphism
of ringed topoi, read as a section of the direct image of
`AlgebraicGeometry.RingedToposHom.pushforwardModules`. The two underlying sheaves of sets are
equal on the nose — both are the direct image of the underlying sheaf of sets of the module —
and this records that identification once, so that the two scalar actions and the two
additions can be compared without re-checking it. -/
def toModulesSections (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Z : Y.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj F))) :
    (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj F)) := x

/-- The inverse reading of `AlgebraicGeometry.RingedToposHom.toModulesSections`. -/
def ofModulesSections (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Z : Y.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj F))) :
    (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj F)) := x

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Addition on the sections of a direct image of a sheaf of modules is the direct-image
addition of Stacks 03D1: the restriction of scalars along `f♯` does not change it. -/
lemma pushforwardModules_add (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Z : Y.Cᵒᵖ)
    (x y : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj F))) :
    x + y =
      Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F
        (f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z) x y :=
  (Sheaf.sectionsFunctor_map_moduleAddHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pushforwardModules f).obj F) Z x y).symm.trans
    (moduleAddHom_pullback_apply Y.J f.toToposHom.pushforward
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F Z x y)

/-- Addition on the sections of the direct image taken through the four-field morphism of
ringed topoi is the same direct-image addition: neither of the two restrictions of scalars it
is built from changes it. -/
lemma toModulesHom_pushforwardModules_add (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Z : Y.Cᵒᵖ)
    (x y : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj F))) :
    x + y =
      Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F
        (f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z) x y :=
  f.pushforwardModules_add F Z x y

/-- The two additions on the sections of a direct image of a sheaf of modules agree. -/
lemma toModulesSections_add (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Z : Y.Cᵒᵖ)
    (x y : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj F))) :
    f.toModulesSections F Z (x + y) =
      f.toModulesSections F Z x + f.toModulesSections F Z y :=
  rfl

/-- The two additions on the sections of a direct image of a sheaf of modules agree, read in
the other direction. -/
lemma ofModulesSections_add (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Z : Y.Cᵒᵖ)
    (x y : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj F))) :
    f.ofModulesSections F Z (x + y) =
      f.ofModulesSections F Z x + f.ofModulesSections F Z y :=
  rfl

/-- The scalar action on the sections of a direct image of a sheaf of modules is the
restriction, along the direct-image form `f♯ : O_D ⟶ f_*O_C` of the structure map, of the
direct-image action `f_*O_C × f_*F ⟶ f_*F` of Stacks 03D1. This is the module structure
prescribed by Stacks 03D6 part (1). -/
lemma pushforwardModules_smul (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Z : Y.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (x : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj F))) :
    r • x =
      Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F
        (f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z)
        ((Sheaf.sectionsFunctor Y.J Z).map
          ((sheafCompose Y.J (forget RingCat.{w'})).map f.fSharpRing) r) x :=
  (Sheaf.sectionsFunctor_map_moduleSMulHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pushforwardModules f).obj F) Z r x).symm.trans
    ((moduleSMulObj_restrictScalars f.fSharpRing
          (pullbackModuleObj Y.J f.toToposHom.pushforward
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F)
          (Sheaf.sectionsFunctor Y.J Z) r x).trans
      (moduleSMulHom_pullback_apply Y.J f.toToposHom.pushforward
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F Z _ x))

/-- The two scalar actions on the sections of a direct image of a sheaf of modules agree. The
four-field one carries the scalar first along the unit `O_D ⟶ f_*f⁻¹O_D` and then along the
direct image of the inverse-image form of the structure map, and that composite is `f♯` —
which is exactly `fSharpInverseImageRing_adjunct`, through
`Stacks.Sheaves.RingedToposModules.fSharp_sections`. -/
lemma toModulesSections_smul (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Z : Y.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (x : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj F))) :
    f.toModulesSections F Z (r • x) = r • f.toModulesSections F Z x :=
  (Stacks.Sheaves.RingedToposModules.pushforwardModules_smul f.toModulesHom F Z r x).trans
    (f.pushforwardModules_smul F Z r (f.toModulesSections F Z x)).symm

/-- The two scalar actions on the sections of a direct image of a sheaf of modules agree, read
in the other direction. -/
lemma ofModulesSections_smul (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Z : Y.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (x : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj F))) :
    f.ofModulesSections F Z (r • x) = r • f.ofModulesSections F Z x :=
  (f.toModulesSections_smul F Z r (f.ofModulesSections F Z x)).symm

/-- The direct image of a sheaf of modules computed through the four-field morphism of ringed
topoi of the modules development agrees with the direct image of
`AlgebraicGeometry.RingedToposHom.pushforwardModules`. The underlying sheaves of sets are equal
on the nose and the comparison is the identity on them; that it is additive is because
restriction of scalars does not touch the addition, and that it is linear is the fact that the
two forms of the structure map are adjunct. -/
def toModulesPushforwardIsoApp (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj F ≅
      (pushforwardModules f).obj F where
  hom := ofSheafHom (𝟙 (f.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F)))
    (f.toModulesSections_add F) (f.toModulesSections_smul F)
  inv := ofSheafHom (𝟙 (f.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F)))
    (f.ofModulesSections_add F) (f.ofModulesSections_smul F)
  hom_inv_id := hom_ext_moduleSheafFunctor rfl
  inv_hom_id := hom_ext_moduleSheafFunctor rfl

/-- The identification of the direct image of sheaves of modules built from the four-field
morphism of ringed topoi with `AlgebraicGeometry.RingedToposHom.pushforwardModules`, naturally
in the module. Each component is the identity on underlying sheaves of sets. -/
def toModulesPushforwardIso (f : RingedToposHom X Y) :
    Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom ≅
      pushforwardModules f :=
  NatIso.ofComponents (f.toModulesPushforwardIsoApp) fun _ ↦
    hom_ext_moduleSheafFunctor (Sheaf.hom_ext_sections fun _ _ ↦ rfl)

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03D7** for a morphism of ringed topoi in the sense of Stacks 01D3: pullback of
sheaves of modules is left adjoint to pushforward. The adjunction supplies the canonical
bijection `Hom_{O_C}(f^*G, F) = Hom_{O_D}(G, f_*F)`, naturally in both variables.

It is the adjunction of the modules development for the four-field morphism `toModulesHom`,
with the right adjoint transported along `toModulesPushforwardIso`. -/
@[stacks 03D7 "for the two-field morphism of ringed topoi", sga "4 IV 13.4" "(a) 13.4.1"]
def pullbackAdjPushforwardModules (f : RingedToposHom X Y) :
    f.toModulesHom.pullbackModules ⊣ pushforwardModules f :=
  (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    f.toModulesHom).ofNatIsoRight f.toModulesPushforwardIso

/-- The pullback of sheaves of modules along a morphism of ringed topoi is additive, being a
left adjoint of the additive direct image. This is what lets it be applied degreewise to
complexes, which is how the total pullback `Lf^*` of Stacks 06YY and the derived adjunction of
Stacks 07A6 are formed. -/
theorem pullbackModules_additive (f : RingedToposHom X Y) :
    (f.toModulesHom.pullbackModules).Additive := by
  let : HasBinaryBiproducts
      (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} Y.O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  let : HasBinaryBiproducts
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have := (pullbackAdjPushforwardModules f).isLeftAdjoint
  have : PreservesBinaryBiproducts f.toModulesHom.pullbackModules :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

attribute [instance] pullbackModules_additive

/-! ### Exactness of the direct image and of the pullback

The direct image of sheaves of modules commutes with all limits and the pullback with all
colimits, each being one half of the adjunction `f^* ⊣ f_*` above; left exactness of `f_*` and
right exactness of `f^*` are the finite cases. -/

universe t t'

/-- **Stacks 03DC, part (1).** The direct image of sheaves of modules along a morphism of ringed
topoi commutes with all limits, of every diagram size: it is a right adjoint, the left adjoint
being the pullback `f^*` of Stacks 03D6. -/
@[stacks 03DC "part (1): the direct image commutes with all limits"]
theorem pushforwardModules_preservesLimitsOfSize (f : RingedToposHom X Y) :
    PreservesLimitsOfSize.{t, t'} (pushforwardModules f) :=
  (pullbackAdjPushforwardModules f).rightAdjoint_preservesLimits

/-- **Stacks 03DC, part (1).** The direct image of sheaves of modules along a morphism of ringed
topoi is left exact. This is the finite case of
`AlgebraicGeometry.RingedToposHom.pushforwardModules_preservesLimitsOfSize`. -/
@[stacks 03DC "part (1): the direct image is left exact",
  sga "4 V 5.0" "left exactness of u_*",
  sga "4 IV 13.6" "u_* left exact"]
theorem pushforwardModules_preservesFiniteLimits (f : RingedToposHom X Y) :
    PreservesFiniteLimits (pushforwardModules f) :=
  have := pushforwardModules_preservesLimitsOfSize.{_, _, _, _, _, _, 0, 0} f
  inferInstance

/-- **Stacks 03DC, part (2).** The pullback of sheaves of modules along a morphism of ringed
topoi commutes with all colimits, of every diagram size: it is a left adjoint, the right adjoint
being the direct image `f_*` of Stacks 03D6. -/
@[stacks 03DC "part (2): the pullback commutes with all colimits",
  sga "4 IV 13.6" "u* commutes w/ colimits", sga "4 IV 11.2.2" "j_X^* inductive limits"]
theorem pullbackModules_preservesColimitsOfSize (f : RingedToposHom X Y) :
    PreservesColimitsOfSize.{t, t'} (f.toModulesHom.pullbackModules) :=
  (pullbackAdjPushforwardModules f).leftAdjoint_preservesColimits

/-- **Stacks 03DC, part (2).** The pullback of sheaves of modules along a morphism of ringed
topoi is right exact. This is the finite case of
`AlgebraicGeometry.RingedToposHom.pullbackModules_preservesColimitsOfSize`. -/
@[stacks 03DC "part (2): the pullback is right exact", sga "4 IV 13.6" "u* right exact"]
theorem pullbackModules_preservesFiniteColimits (f : RingedToposHom X Y) :
    PreservesFiniteColimits (f.toModulesHom.pullbackModules) :=
  have := pullbackModules_preservesColimitsOfSize.{_, _, _, _, _, _, 0, 0} f
  inferInstance

end Modules

end AlgebraicGeometry.RingedToposHom

end
