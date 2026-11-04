module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackDescent
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent

/-!
# Effective descent for polarized families: the scheme of the descended family (Stacks 0D40)

Let `{f i : V i ⟶ U}` be a covering family of the big fppf site and `D` a descent datum of
polarized families relative to the sieve it generates, with members `x i` over `V i`. The proof
of Stacks 0D40 descends the underlying family of algebraic spaces first (Stacks 0D1G) and then
shows that the descended algebraic space is a scheme. This file records what the descended
family is once it is a scheme, and what can be said about it without the polarization.

The data are recorded in `AlgebraicGeometry.PolarizedDescentScheme`: a scheme `Z` with a
morphism `π : Z ⟶ U` and morphisms `t i` from the total spaces of the `x i` to `Z`, each
square with the structure morphism of `x i`, `π` and `f i` cartesian, and the `t i` compatible
with the gluing isomorphisms of `D` over every scheme mapping compatibly to two members.

## Main definitions

* `AlgebraicGeometry.PolarizedDescentScheme`: the scheme of the descended family, with its
  cartesian squares and compatibilities.
* `AlgebraicGeometry.PolarizedDescentScheme.ofRepresented`: such data from the descended
  family of algebraic spaces of Stacks 0D1G, once it is represented by a scheme.

## Main results

* `AlgebraicGeometry.PolarizedDescentScheme.isProper_toBase`,
  `AlgebraicGeometry.PolarizedDescentScheme.flat_toBase`,
  `AlgebraicGeometry.PolarizedDescentScheme.finitePresentation_toBase`: the morphism `π` is
  proper, flat and of finite presentation, these properties being fpqc local on the target
  (Stacks 02L1, 02L2, 02L0).

## References

* [Stacks Project, Tag 0D40](https://stacks.math.columbia.edu/tag/0D40)
* [Stacks Project, Tag 02L1](https://stacks.math.columbia.edu/tag/02L1)
* [Stacks Project, Tag 02L2](https://stacks.math.columbia.edu/tag/02L2)
* [Stacks Project, Tag 02L0](https://stacks.math.columbia.edu/tag/02L0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor (Fiber IsPreFibered)

universe w u

namespace AlgebraicGeometry

/-- A property of morphisms local at the target for a precoverage holds for a morphism as soon
as it holds for its base changes along the members of a covering family, each presented by a
cartesian square. -/
theorem MorphismProperty.IsLocalAtTarget.of_forall_isPullback {C : Type*} [Category C]
    {P : MorphismProperty C} {K : Precoverage C} [P.IsLocalAtTarget K] {X Y : C} {f : X ⟶ Y}
    {I : Type*} {Yi : I → C} {g : ∀ i, Yi i ⟶ Y} (hg : Presieve.ofArrows Yi g ∈ K Y)
    {Xi : I → C} {p : ∀ i, Xi i ⟶ X} {fi : ∀ i, Xi i ⟶ Yi i}
    (hsq : ∀ i, IsPullback (p i) (fi i) f (g i)) (h : ∀ i, P (fi i)) : P f := by
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hg fun {U g'} _ hg' => ?_
  obtain ⟨i⟩ := hg'
  refine (MorphismProperty.cancel_left_of_respectsIso P (hsq i).isoPullback.hom _).mp ?_
  rw [(hsq i).isoPullback_hom_snd]
  exact h i

variable {B : BigFppfSite.{u}}

/-! ### Morphisms into a represented family of algebraic spaces -/

namespace PolarizedFamily

/-- The morphism of schemes from the total space of a polarized family `x` to a scheme `Z`
representing, through `e`, the algebraic space of a family `y`, underlying a morphism `φ` from
the family of algebraic spaces of `x` to `y`. -/
def totalMapToRepresented {x : PolarizedFamily B}
    {y : CartesianProperFlatSpaces B integerBase B.contains_integerBase}
    (φ : (forgetPolarization B).obj x ⟶ y) {Z : BigFppfOver B integerBase B.contains_integerBase}
    (e : yoneda.obj Z ≅ y.obj.obj.left.1) :
    x.total ⟶ (BigFppfOver.toScheme B integerBase B.contains_integerBase).obj Z :=
  (BigFppfOver.toScheme B integerBase B.contains_integerBase).map
    (Yoneda.fullyFaithful.preimage (φ.1.hom.left.hom ≫ e.inv))

/-- `AlgebraicGeometry.PolarizedFamily.totalMapToRepresented` of a composite with the image of a
morphism of polarized families is the composite with its morphism of total spaces. -/
theorem totalMapToRepresented_comp {x' x : PolarizedFamily B}
    {y : CartesianProperFlatSpaces B integerBase B.contains_integerBase} (ψ : x' ⟶ x)
    (φ : (forgetPolarization B).obj x ⟶ y) {Z : BigFppfOver B integerBase B.contains_integerBase}
    (e : yoneda.obj Z ≅ y.obj.obj.left.1) :
    totalMapToRepresented ((forgetPolarization B).map ψ ≫ φ) e =
      ψ.totalMap ≫ totalMapToRepresented φ e := by
  have h₁ : Yoneda.fullyFaithful.preimage
      (((forgetPolarization B).map ψ ≫ φ).1.hom.left.hom ≫ e.inv) =
      totalMapOverIntegers ψ ≫ Yoneda.fullyFaithful.preimage (φ.1.hom.left.hom ≫ e.inv) := by
    refine Yoneda.fullyFaithful.map_injective ?_
    refine (Yoneda.fullyFaithful.map_preimage _).trans ?_
    refine Eq.trans ?_ (yoneda.map_comp _ _).symm
    refine Eq.trans ?_ (congrArg (fun k => yoneda.map (totalMapOverIntegers ψ) ≫ k)
      (Yoneda.fullyFaithful.map_preimage _).symm)
    exact Category.assoc (yoneda.map (totalMapOverIntegers ψ)) φ.1.hom.left.hom e.inv
  exact (congrArg (BigFppfOver.toScheme B integerBase B.contains_integerBase).map h₁).trans
    ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map_comp _ _)

/-- The structure morphism of a scheme `Z` representing, through `e`, the algebraic space of a
family `y` lying over `U`, as a morphism of schemes to `U`. -/
def representedToBase {U : B.Schemes} (y : (polarizedFamiliesProperFlatProjection B).Fiber U)
    {Z : BigFppfOver B integerBase B.contains_integerBase}
    (e : yoneda.obj Z ≅ y.1.obj.obj.left.1) :
    (BigFppfOver.toScheme B integerBase B.contains_integerBase).obj Z ⟶ B.inclusion.obj U :=
  (BigFppfOver.toScheme B integerBase B.contains_integerBase).map
      (Yoneda.fullyFaithful.preimage (e.hom ≫ y.1.obj.obj.hom)) ≫
    B.inclusion.map (eqToHom y.2)

/-- **A morphism over `g` into a represented family is a cartesian square over `g`.** Let `x` be
a polarized family over `V`, `y` a finitely presented, flat and proper family of algebraic spaces
over `U` whose algebraic space is represented, through `e`, by a scheme `Z`, and `φ` a morphism
from the family underlying `x` to `y` lying over `g : V ⟶ U`. Then the square formed by the
morphism of total spaces, the structure morphism of `x`, that of `Z` and `g` is cartesian. -/
theorem isPullback_totalMapToRepresented {U V : B.Schemes} {x : PolarizedFamily B}
    (hx : x.base = V) (y : (polarizedFamiliesProperFlatProjection B).Fiber U) (g : V ⟶ U)
    (φ : (forgetPolarization B).obj x ⟶ y.1)
    [hφ : (polarizedFamiliesProperFlatProjection B).IsHomLift g φ]
    {Z : BigFppfOver B integerBase B.contains_integerBase}
    (e : yoneda.obj Z ≅ y.1.obj.obj.left.1) :
    IsPullback (totalMapToRepresented φ e) (x.toBase ≫ B.inclusion.map (eqToHom hx))
      (representedToBase y e) (B.inclusion.map g) := by
  have h := isPullback_of_forgetPolarization_hom B φ e
  have hfac := IsHomLift.fac' (polarizedFamiliesProperFlatProjection B) g φ
  have hbase : (polarizedFamiliesProperFlatProjection B).map φ ≫ eqToHom y.2 =
      eqToHom hx ≫ g := by
    rw [hfac, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rfl
  refine IsPullback.of_iso h (Iso.refl _) (Iso.refl _)
    (B.inclusion.mapIso (eqToIso hx)) (B.inclusion.mapIso (eqToIso y.2)) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact (B.inclusion.map_comp _ _).symm.trans
      ((congrArg B.inclusion.map hbase).trans (B.inclusion.map_comp _ _))

end PolarizedFamily

/-- A covering family of the big fppf site is, after inclusion into all schemes, an fpqc
covering family. -/
theorem BigFppfSite.ofArrows_inclusion_mem_fpqcPrecoverage {U : B.Schemes}
    {E : PreZeroHypercover.{u + 1} U} (hE : B.IsCovering ⟨U, E⟩) :
    Presieve.ofArrows (fun i => B.inclusion.obj (E.X i)) (fun i => B.inclusion.map (E.f i)) ∈
      Scheme.fpqcPrecoverage (B.inclusion.obj U) := by
  have h : E.presieve₀.map B.inclusion ∈ Scheme.fppfPrecoverage (B.inclusion.obj U) := hE.1
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at h
  exact Scheme.fppfPrecoverage_le_fpqcPrecoverage _ h

end AlgebraicGeometry

namespace CategoryTheory.Functor.SieveDescentDatum

variable {𝒞 : Type*} [Category 𝒞] {𝒮 : Type*} [Category 𝒮] {𝒯 : Type*} [Category 𝒯]
  {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} {F : 𝒮 ⥤ 𝒯} [p.IsFibered] [q.IsFibered]

/-- **The compatibility of a descent of the image of a descent datum, read before the image.**
Let `F` be a 1-morphism of fibred categories and `D` a descent datum for `p`. Morphisms `ζf`,
`ζg` from the images under `F` of two objects of `D` to an object `y`, compatible with the
gluing isomorphism of the image datum `D.mapF hF1`, are compatible with the image under `F` of
the gluing isomorphism of `D` itself: the comparisons `mapPbIso` cancel. -/
theorem map_comp_eq_of_mapF (hF1 : IsFibredOneMorphism p q F) {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum p R) {V W Z : 𝒞} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) {y : 𝒯}
    (ζf : F.obj (D.obj f hf).1 ⟶ y) (ζg : F.obj (D.obj g hg).1 ⟶ y)
    (h : Fiber.fiberInclusion.map ((D.mapF hF1).iso hf hg ε ε' heq).hom ≫
        IsPreFibered.pullbackMap ((D.mapF hF1).obj g hg).2 ε' ≫ ζg =
      IsPreFibered.pullbackMap ((D.mapF hF1).obj f hf).2 ε ≫ ζf) :
    F.map (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 ε') ≫ ζg =
      F.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε) ≫ ζf := by
  have hiso : ((D.mapF hF1).iso hf hg ε ε' heq).hom =
      (mapPbIso hF1 (D.obj f hf) ε).hom ≫
        ((Fiber.mapOfComp p q F hF1.comp_eq Z).map (D.iso hf hg ε ε' heq).hom ≫
          (mapPbIso hF1 (D.obj g hg) ε').inv) := rfl
  have hmap : Fiber.fiberInclusion.map
      ((Fiber.mapOfComp p q F hF1.comp_eq Z).map (D.iso hf hg ε ε' heq).hom) =
      F.map (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) :=
    Fiber.fiberInclusion_map_mapOfComp_map p q F hF1.comp_eq Z _
  have e1 : F.map (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 ε') ≫ ζg =
      F.map (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
        F.map (IsPreFibered.pullbackMap (D.obj g hg).2 ε') ≫ ζg :=
    (F.map_comp _ _ =≫ ζg).trans (Category.assoc _ _ _)
  have e2 := (mapPbIso_inv_fac_assoc hF1 (D.obj g hg) ε' ζg).symm
  have e3 : Fiber.fiberInclusion.map ((D.mapF hF1).iso hf hg ε ε' heq).hom =
      Fiber.fiberInclusion.map (mapPbIso hF1 (D.obj f hf) ε).hom ≫
        Fiber.fiberInclusion.map
          ((Fiber.mapOfComp p q F hF1.comp_eq Z).map (D.iso hf hg ε ε' heq).hom) ≫
        Fiber.fiberInclusion.map (mapPbIso hF1 (D.obj g hg) ε').inv := by
    rw [hiso]
    rfl
  have key : Fiber.fiberInclusion.map (mapPbIso hF1 (D.obj f hf) ε).hom ≫
      (F.map (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 ε') ≫ ζg) =
      Fiber.fiberInclusion.map (mapPbIso hF1 (D.obj f hf) ε).hom ≫
        (F.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε) ≫ ζf) := by
    refine Eq.trans ?_ (h.trans (mapPbIso_hom_fac_assoc hF1 (D.obj f hf) ε ζf).symm)
    refine (congrArg (fun m => Fiber.fiberInclusion.map (mapPbIso hF1 (D.obj f hf) ε).hom ≫ m)
      (e1.trans (congrArg
        (fun m => F.map (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫ m) e2))).trans ?_
    refine Eq.trans ?_ (congrArg (fun m => m ≫
      IsPreFibered.pullbackMap ((D.mapF hF1).obj g hg).2 ε' ≫ ζg) e3).symm
    refine Eq.trans ?_ (congrArg (fun m => (Fiber.fiberInclusion.map
        (mapPbIso hF1 (D.obj f hf) ε).hom ≫ m ≫
          Fiber.fiberInclusion.map (mapPbIso hF1 (D.obj g hg) ε').inv) ≫
        IsPreFibered.pullbackMap ((D.mapF hF1).obj g hg).2 ε' ≫ ζg) hmap).symm
    exact ((Category.assoc _ _ _).trans (congrArg
      (fun m => Fiber.fiberInclusion.map (mapPbIso hF1 (D.obj f hf) ε).hom ≫ m)
      (Category.assoc _ _ _))).symm
  exact (cancel_epi (Fiber.fiberInclusion.mapIso (mapPbIso hF1 (D.obj f hf) ε)).hom).1 key

end CategoryTheory.Functor.SieveDescentDatum

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}}

/-! ### The scheme of a descended family -/

/-- A property of morphisms of schemes respecting isomorphisms holds for the structure morphism
of a polarized family followed by an identification of its base. -/
theorem PolarizedFamily.prop_toBase_comp_eqToHom {P : MorphismProperty Scheme.{u}}
    {V : B.Schemes} {x : PolarizedFamily B} (h : x.base = V) (hx : P x.toBase) :
    P (x.toBase ≫ B.inclusion.map (eqToHom h)) := by
  subst h
  rw [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
  exact hx

variable {U : B.Schemes} {I : Type w} {V : I → B.Schemes} {f : ∀ i, V i ⟶ U}

/-- **The scheme of the family descended from a descent datum of polarized families.** For a
descent datum `D` of polarized families relative to the sieve generated by `{f i : V i ⟶ U}`,
with members `x i` over `V i`: a scheme `total` with a morphism `toBase` to `U` and morphisms
`totalMap i` from the total space of `x i`, such that the square formed by `totalMap i`, the
structure morphism of `x i`, `toBase` and `f i` is cartesian, and such that the `totalMap i` are
compatible with the gluing isomorphisms of `D`. -/
structure PolarizedDescentScheme
    (D : (polarizedProjection B).SieveDescentDatum (Sieve.ofArrows V f)) where
  /-- The total space of the descended family. -/
  total : Scheme.{u}
  /-- Its structure morphism. -/
  toBase : total ⟶ B.inclusion.obj U
  /-- The morphism from the total space of each member of the datum. -/
  totalMap : ∀ i, (D.obj (f i) (Sieve.ofArrows_mk V f i)).1.total ⟶ total
  /-- Each member of the datum is the base change of the descended family. -/
  isPullback : ∀ i, IsPullback (totalMap i)
    ((D.obj (f i) (Sieve.ofArrows_mk V f i)).1.toBase ≫
      B.inclusion.map (eqToHom (D.obj (f i) (Sieve.ofArrows_mk V f i)).2))
    toBase (B.inclusion.map (f i))
  /-- The morphisms from the members are compatible with the gluing isomorphisms of the datum
  over every scheme mapping compatibly to two members of the covering family. -/
  totalMap_glue : ∀ (i j : I) ⦃W : B.Schemes⦄ (b : W ⟶ V i) (b' : W ⟶ V j)
      (h : b ≫ f i = b' ≫ f j),
    (Fiber.fiberInclusion.map
          (D.iso (Sieve.ofArrows_mk V f i) (Sieve.ofArrows_mk V f j) b b' h).hom ≫
        IsPreFibered.pullbackMap (D.obj (f j) (Sieve.ofArrows_mk V f j)).2 b').totalMap ≫
        totalMap j =
      (IsPreFibered.pullbackMap (D.obj (f i) (Sieve.ofArrows_mk V f i)).2 b).totalMap ≫ totalMap i

namespace PolarizedDescentScheme

variable {D : (polarizedProjection B).SieveDescentDatum (Sieve.ofArrows V f)}

section Local

variable (hf : Presieve.ofArrows (fun i => B.inclusion.obj (V i)) (fun i => B.inclusion.map (f i))
    ∈ Scheme.fpqcPrecoverage (B.inclusion.obj U)) (S : PolarizedDescentScheme D)
include hf

/-- The structure morphism of the descended family has a property fpqc local on the target as soon
as the structure morphisms of the members of the datum have it. -/
private theorem prop_toBase_of_forall {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtTarget (Scheme.fpqcPrecoverage)]
    (h : ∀ i, P (D.obj (f i) (Sieve.ofArrows_mk V f i)).1.toBase) : P S.toBase :=
  MorphismProperty.IsLocalAtTarget.of_forall_isPullback hf S.isPullback
    fun i => PolarizedFamily.prop_toBase_comp_eqToHom _ (h i)

/-- **The descended family is proper** (Stacks 02L1): its base changes along the covering family
are the members of the datum, which are proper. -/
theorem isProper_toBase : IsProper S.toBase :=
  prop_toBase_of_forall hf S fun i => (D.obj (f i) (Sieve.ofArrows_mk V f i)).1.proper

/-- **The descended family is flat** (Stacks 02L2). -/
theorem flat_toBase : Flat S.toBase :=
  prop_toBase_of_forall hf S fun i => (D.obj (f i) (Sieve.ofArrows_mk V f i)).1.flat

/-- **The descended family is of finite presentation** (Stacks 02L0). -/
theorem finitePresentation_toBase : FinitePresentation S.toBase :=
  prop_toBase_of_forall hf S fun i =>
    (D.obj (f i) (Sieve.ofArrows_mk V f i)).1.finitePresentation

end Local

/-- **The scheme of the descended family, from a representation of the descended algebraic
space.** Let `y` be a finitely presented, flat and proper family of algebraic spaces over `U`,
with morphisms `ζ i` over `f i` from the families underlying the members of `D`, compatible with
the images of the gluing isomorphisms of `D`, and let `e` represent the algebraic space of `y` by
a scheme `Z`. Then `Z`, with its structure morphism to `U` and the morphisms of schemes
underlying the `ζ i`, is the scheme of the descended family: the squares are cartesian by
`AlgebraicGeometry.PolarizedFamily.isPullback_totalMapToRepresented`, and the compatibility is
the compatibility of the `ζ i` read on total spaces. -/
def ofRepresented (y : (polarizedFamiliesProperFlatProjection B).Fiber U)
    (ζ : ∀ i, (forgetPolarization B).obj (D.obj (f i) (Sieve.ofArrows_mk V f i)).1 ⟶ y.1)
    (hζ : ∀ i, (polarizedFamiliesProperFlatProjection B).IsHomLift (f i) (ζ i))
    (hglue : ∀ (i j : I) ⦃W : B.Schemes⦄ (b : W ⟶ V i) (b' : W ⟶ V j)
        (h : b ≫ f i = b' ≫ f j), (forgetPolarization B).map
          (Fiber.fiberInclusion.map
            (D.iso (Sieve.ofArrows_mk V f i) (Sieve.ofArrows_mk V f j) b b' h).hom ≫
          IsPreFibered.pullbackMap (D.obj (f j) (Sieve.ofArrows_mk V f j)).2 b') ≫ ζ j =
        (forgetPolarization B).map
          (IsPreFibered.pullbackMap (D.obj (f i) (Sieve.ofArrows_mk V f i)).2 b) ≫ ζ i)
    {Z : BigFppfOver B integerBase B.contains_integerBase}
    (e : yoneda.obj Z ≅ y.1.obj.obj.left.1) : PolarizedDescentScheme D where
  total := (BigFppfOver.toScheme B integerBase B.contains_integerBase).obj Z
  toBase := PolarizedFamily.representedToBase y e
  totalMap i := PolarizedFamily.totalMapToRepresented (ζ i) e
  isPullback i :=
    haveI := hζ i
    PolarizedFamily.isPullback_totalMapToRepresented (D.obj (f i) (Sieve.ofArrows_mk V f i)).2
      y (f i) (ζ i) e
  totalMap_glue i j _ b b' h :=
    (PolarizedFamily.totalMapToRepresented_comp _ (ζ j) e).symm.trans
      ((congrArg (fun k => PolarizedFamily.totalMapToRepresented k e) (hglue i j b b' h)).trans
        (PolarizedFamily.totalMapToRepresented_comp _ (ζ i) e))

end PolarizedDescentScheme

end AlgebraicGeometry

end
