module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFiberedUnconditional
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Base change of the stack of coherent sheaves, unconditionally

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over a scheme `S` of a big
fppf site, the standing data of Stacks 08KB, and let `g : Y' ⟶ Y` be a morphism of algebraic
spaces.  Writing `X' = X ×_Y Y'`, Stacks 08LP asserts that the square

`Coh_{X'/Y'} ⟶ Coh_{X/Y}`, `𝒮_{Y'} ⟶ 𝒮_Y`

is 2-cartesian.  This file builds the square and proves its universal property from the
base-change stability `AlgebraicGeometry.Space.ModulePullbackStabilityOfFinitePresentation`,
which asks flatness to be inherited only by the inverse image of a module of finite
presentation; the module of an object of `Coh_{X/Y}` is of finite presentation.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.baseChangeObject'` and
  `AlgebraicGeometry.Space.CoherentSituation.baseChangeHom'`: the object and the morphism of
  `Coh_{X/Y}` attached to an object and a morphism of `Coh_{X'/Y'}` by reading the module through
  the comparison `X'_T ≅ X_T` of the two base changes.
* `AlgebraicGeometry.Space.CoherentSituation.baseChangeFunctor'`: the functor
  `Coh_{X'/Y'} ⥤ Coh_{X/Y}` those two assignments define, and
  `AlgebraicGeometry.Space.CoherentSituation.coherentBaseChangeMap'` it as a 1-morphism of
  categories over the site.
* `AlgebraicGeometry.Space.CoherentSituation.baseChangeSquare'`: the square of Stacks 08LP.
* `AlgebraicGeometry.Space.CoherentSituation.BaseChangeLift'`: the datum lifting an object of
  `Coh_{X/Y}` whose test scheme factors through `Y'`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.baseChangeSquare_hlift'` and
  `AlgebraicGeometry.Space.CoherentSituation.baseChangeSquareLiftedObject'`: arrow lifting and
  object lifting for the square.
* `AlgebraicGeometry.Space.CoherentSituation.baseChangeSquare_isTwoFibreProduct'`: the square
  is 2-cartesian, for a given category structure on the objects of the two sides.

## Implementation notes

The primed names are the counterparts of the correspondingly named declarations of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackBaseChange.lean`, with
`AlgebraicGeometry.Space.ModulePullbackStabilityOfFinitePresentation` in place of
`AlgebraicGeometry.Space.ModulePullbackStability`.  Everything in that module which does not
mention the base-change stability is used from there unchanged.  Quasi-coherence and finite type
of the transported module are read off its finite presentation.

## References

* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS) {Y' : AlgebraicSpaces B S hS}

/-! ### Transport of an object along the comparison -/

/-- The object of `Coh_{X/Y}` attached to an object of `Coh_{X'/Y'}`: its test scheme is the
given one read over `Y`, and its module is the inverse image of the given one along the
comparison `X_T ⟶ X'_T`. -/
def baseChangeObject' (hst : ModulePullbackStabilityOfFinitePresentation B S hS) (g : Y' ⟶ D.Y)
    (A : CoherentObject (D.baseChange g)) : CoherentObject D where
  T := (D.overBase g).obj A.T
  F := (modulePullback B S hS (D.baseChangeSpaceIso g A.T).inv).obj A.F
  finitePresentation :=
    hst.finitePresentation (D.baseChangeSpaceIso g A.T).inv A.F A.finitePresentation
  quasicoherent :=
    have := hst.finitePresentation (D.baseChangeSpaceIso g A.T).inv A.F A.finitePresentation
    inferInstance
  flat :=
    hst.flat (D.isPullback_baseChangeSpaceIso_inv g A.T) A.F A.finitePresentation A.flat
  properSupport := by
    obtain ⟨hp, hU, hproper⟩ := A.properSupport
    have := A.finitePresentation
    obtain ⟨hU', hproper'⟩ := hst.properSupport (D.isPullback_baseChangeSpaceIso_inv g A.T) hp
      A.F A.quasicoherent inferInstance hU hproper
    exact ⟨(isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (D.isPullback_baseChangeSpaceIso_inv g A.T) hp, hU', hproper'⟩

/-- The transported object has the given test scheme, read over `Y`. -/
@[simp]
theorem baseChangeObject_T' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) (A : CoherentObject (D.baseChange g)) :
    (D.baseChangeObject' hst g A).T = (D.overBase g).obj A.T :=
  rfl

/-- The module of the transported object is the inverse image of the given one. -/
@[simp]
theorem baseChangeObject_F' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) (A : CoherentObject (D.baseChange g)) :
    (D.baseChangeObject' hst g A).F =
      (modulePullback B S hS (D.baseChangeSpaceIso g A.T).inv).obj A.F :=
  rfl

/-! ### Transport of a morphism along the comparison -/

variable (hc : ModulePushforwardCoherence B S hS)

/-- The morphism of `Coh_{X/Y}` attached to a morphism of `Coh_{X'/Y'}`: its base map is the
given one read over `Y`, and its comparison of modules is the given one conjugated by the
comparison of the two base changes. -/
def baseChangeHom' (hst : ModulePullbackStabilityOfFinitePresentation B S hS) (g : Y' ⟶ D.Y)
    {A A' : CoherentObject (D.baseChange g)} (m : CoherentHom A A') :
    CoherentHom (D.baseChangeObject' hst g A) (D.baseChangeObject' hst g A') where
  base := (D.overBase g).map m.base
  fibre := Functor.conjFibre (D.baseChangeModuleSquare g m.base) m.fibre
  isIso_fibre := Functor.isIso_conjFibre (D.baseChangeModuleSquare g m.base) m.fibre

/-- The base map of the transported morphism is the given one read over `Y`. -/
@[simp]
theorem baseChangeHom_base' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) {A A' : CoherentObject (D.baseChange g)} (m : CoherentHom A A') :
    (D.baseChangeHom' hst g m).base = (D.overBase g).map m.base :=
  rfl

/-- The comparison of modules of a transported morphism. -/
theorem baseChangeHom_fibre' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) {A A' : CoherentObject (D.baseChange g)} (m : CoherentHom A A') :
    (D.baseChangeHom' hst g m).fibre =
      Functor.conjFibre (D.baseChangeModuleSquare g m.base) m.fibre :=
  rfl

/-- The underlying morphism of schemes of the base map of a transported morphism. -/
@[simp]
theorem baseChangeHom_base_left' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) {A A' : CoherentObject (D.baseChange g)} (m : CoherentHom A A') :
    (D.baseChangeHom' hst g m).base.left = m.base.left :=
  rfl

/-- The unit law of Stacks 03LU at the test scheme of a transported object. -/
theorem idComparison_baseChangeObject' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) (A : CoherentObject (D.baseChange g)) :
    D.idComparison hc (D.baseChangeObject' hst g A).T =
      D.idComparison hc ((D.overBase g).obj A.T) :=
  rfl

/-- The base map of the transport of an identity. -/
theorem baseChangeHom_id_base' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) (A : CoherentObject (D.baseChange g)) :
    (D.baseChangeHom' hst g (CoherentHom.id hc A)).base =
      (CoherentHom.id hc (D.baseChangeObject' hst g A)).base :=
  rfl

/-- Transport along the comparison of base changes preserves identities. -/
theorem baseChangeHom_id' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) (A : CoherentObject (D.baseChange g)) :
    D.baseChangeHom' hst g (CoherentHom.id hc A) =
      CoherentHom.id hc (D.baseChangeObject' hst g A) := by
  have hcomp : HEq ((D.idComparison hc ((D.overBase g).obj A.T)).hom.app
        ((modulePullback B S hS (D.baseChangeSpaceIso g A.T).inv).obj A.F))
      ((D.idComparison hc (D.baseChangeObject' hst g A).T).hom.app
        (D.baseChangeObject' hst g A).F) := by
    rw [D.baseChangeObject_F' hst g A, D.idComparison_baseChangeObject' hc hst g A]
    rfl
  refine coherentHom_eq_of_heq (D.baseChangeHom_id_base' hc hst g A) ?_
  refine HEq.trans (heq_of_eq ((D.baseChangeHom_fibre' hst g (CoherentHom.id hc A)).trans
    ((congrArg (fun σ => Functor.conjFibre σ (CoherentHom.id hc A).fibre)
        (D.baseChangeModuleSquare_idBase hc g A)).trans
      ((congrArg (Functor.conjFibre (D.baseChangeModuleSquare g (𝟙 A.T)))
          (CoherentHom.id_fibre hc A)).trans
        (Functor.conjFibre_id (D.baseChangeModuleSquare g (𝟙 A.T))
          ((D.baseChange g).idComparison hc A.T)
          (D.idComparison hc ((D.overBase g).obj A.T))
          (D.baseChangeModuleSquare_id hc g A.T) A.F)))))
    (HEq.trans hcomp (heq_of_eq (CoherentHom.id_fibre hc (D.baseChangeObject' hst g A)).symm))

/-- The comparison of Stacks 03LU for the composite of two transported base maps. -/
theorem compComparison_baseChangeHom' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) {A A' A'' : CoherentObject (D.baseChange g)} (m : CoherentHom A A')
    (n : CoherentHom A' A'') :
    D.compComparison (D.baseChangeHom' hst g m).base (D.baseChangeHom' hst g n).base =
      D.compComparison ((D.overBase g).map m.base) ((D.overBase g).map n.base) :=
  rfl

/-- The base map of the transport of a composite. -/
theorem baseChangeHom_comp_base' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) {A A' A'' : CoherentObject (D.baseChange g)} (m : CoherentHom A A')
    (n : CoherentHom A' A'') :
    (D.baseChangeHom' hst g (m.comp n)).base =
      ((D.baseChangeHom' hst g m).comp (D.baseChangeHom' hst g n)).base :=
  rfl

include hc in
/-- Transport along the comparison of base changes preserves composition. -/
theorem baseChangeHom_comp' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) {A A' A'' : CoherentObject (D.baseChange g)} (m : CoherentHom A A')
    (n : CoherentHom A' A'') :
    D.baseChangeHom' hst g (m.comp n) =
      (D.baseChangeHom' hst g m).comp (D.baseChangeHom' hst g n) := by
  refine coherentHom_eq_of_heq (D.baseChangeHom_comp_base' hst g m n) (heq_of_eq ?_)
  refine (D.baseChangeHom_fibre' hst g (m.comp n)).trans ?_
  refine (congrArg (fun σ => Functor.conjFibre σ (m.comp n).fibre)
    (D.baseChangeModuleSquare_compBase g m n)).trans ?_
  refine (congrArg (Functor.conjFibre (D.baseChangeModuleSquare g (m.base ≫ n.base)))
    (CoherentHom.comp_fibre m n)).trans ?_
  refine (congrArg (fun σ => Functor.conjFibre σ
      (Functor.fibreComp ((D.baseChange g).compComparison m.base n.base) m.fibre n.fibre))
    (D.baseChangeModuleSquare_comp_eq g m.base n.base)).trans ?_
  refine (Functor.conjFibre_fibreComp ((D.baseChange g).compComparison m.base n.base)
    (D.compComparison ((D.overBase g).map m.base) ((D.overBase g).map n.base))
    (D.baseChangeModuleSquare g m.base) (D.baseChangeModuleSquare g n.base) _
    (modulePullbackSquare_comp hc
      (baseChangeMap_comp D.f ((D.overBase g).map m.base) ((D.overBase g).map n.base)).symm
      (baseChangeMap_comp (D.baseChange g).f m.base n.base).symm rfl
      (D.baseChangeSpaceIso_inv_naturality g m.base) rfl
      (D.baseChangeSpaceIso_inv_naturality g n.base) rfl
      (D.baseChangeSpaceIso_inv_naturality g (m.base ≫ n.base)))
    m.fibre n.fibre).trans ?_
  rw [← D.baseChangeHom_fibre' hst g m, ← D.baseChangeHom_fibre' hst g n,
    ← D.compComparison_baseChangeHom' hst g m n]
  exact (CoherentHom.comp_fibre (D.baseChangeHom' hst g m) (D.baseChangeHom' hst g n)).symm

/-! ### The base-change functor -/

/-- The base-change functor `Coh_{X'/Y'} ⥤ Coh_{X/Y}`, given on objects by
`AlgebraicGeometry.Space.CoherentSituation.baseChangeObject'` and on morphisms by
`AlgebraicGeometry.Space.CoherentSituation.baseChangeHom'`. -/
def baseChangeFunctor' (hst : ModulePullbackStabilityOfFinitePresentation B S hS) (g : Y' ⟶ D.Y)
    (cd : CoherentCategoryData hc D) (cd' : CoherentCategoryData hc (D.baseChange g)) :
    @Functor (CoherentObject (D.baseChange g)) cd'.category (CoherentObject D) cd.category :=
  letI : Category.{u + 1} (CoherentObject (D.baseChange g)) := cd'.category
  letI : Category.{u + 1} (CoherentObject D) := cd.category
  { obj := D.baseChangeObject' hst g
    map := fun {A A'} m => (Equiv.cast (cd.hom_type _ _)).symm
      (D.baseChangeHom' hst g ((Equiv.cast (cd'.hom_type A A')) m))
    map_id := fun A => by
      refine (Equiv.cast (cd.hom_type _ _)).injective ?_
      rw [Equiv.apply_symm_apply, cd'.identity, cd.identity]
      exact D.baseChangeHom_id' hc hst g A
    map_comp := fun {A A' A''} m n => by
      refine (Equiv.cast (cd.hom_type _ _)).injective ?_
      rw [Equiv.apply_symm_apply, cd.composition, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, cd'.composition]
      exact D.baseChangeHom_comp' hc hst g _ _ }

/-- The morphism of `Coh_{X/Y}` underlying the value of the base-change functor. -/
theorem baseChangeFunctor_cast' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (D.baseChange g))
    {A A' : CoherentObject (D.baseChange g)} :
    letI : Category.{u + 1} (CoherentObject (D.baseChange g)) := cd'.category
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    ∀ m : A ⟶ A',
      (Equiv.cast (cd.hom_type _ _)) ((D.baseChangeFunctor' hc hst g cd cd').map m) =
        D.baseChangeHom' hst g ((Equiv.cast (cd'.hom_type A A')) m) :=
  fun _ => Equiv.apply_symm_apply _ _

/-- The top row of the square of Stacks 08LP: the base-change functor as a 1-morphism
`Coh_{X'/Y'} ⟶ Coh_{X/Y}` of categories over the big fppf site of `S`. -/
def coherentBaseChangeMap' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (D.baseChange g)) :
    coherentBasedCategory cd' ⥤ᵇ coherentBasedCategory cd where
  toFunctor := D.baseChangeFunctor' hc hst g cd cd'
  w := by
    let _ : Category.{u + 1} (CoherentObject (D.baseChange g)) := cd'.category
    let _ : Category.{u + 1} (CoherentObject D) := cd.category
    refine CategoryTheory.Functor.ext (fun A => rfl) (fun A A' m => ?_)
    change ((Equiv.cast (cd.hom_type _ _))
        ((D.baseChangeFunctor' hc hst g cd cd').map m)).base.left =
      𝟙 _ ≫ ((Equiv.cast (cd'.hom_type A A')) m).base.left ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, D.baseChangeFunctor_cast' hc hst g cd cd' m]
    exact D.baseChangeHom_base_left' hst g _

/-- The square of Stacks 08LP commutes on the nose. -/
theorem coherentBaseChangeMap_comp_toBase' (hst : ModulePullbackStabilityOfFinitePresentation
    B S hS) (g : Y' ⟶ D.Y) (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (D.baseChange g)) :
    BasedFunctor.comp (D.coherentBaseChangeMap' hc hst g cd cd') (coherentToBase cd) =
      BasedFunctor.comp (coherentToBase cd') (baseBasedMap g) := by
  let _ : Category.{u + 1} (CoherentObject (D.baseChange g)) := cd'.category
  let _ : Category.{u + 1} (CoherentObject D) := cd.category
  have hobj : ∀ A : (coherentBasedCategory cd').obj,
      (BasedFunctor.comp (D.coherentBaseChangeMap' hc hst g cd cd')
          (coherentToBase cd)).obj A =
        (BasedFunctor.comp (coherentToBase cd') (baseBasedMap g)).obj A := fun _ => rfl
  refine BasedCategory.BasedFunctor.ext'
    (CategoryTheory.Functor.hext hobj (fun A A' m => heq_of_eq ?_))
  show ULift.up ((Equiv.cast (cd.hom_type _ _))
      ((D.baseChangeFunctor' hc hst g cd cd').map m)).base =
    ULift.up ((D.overBase g).map ((Equiv.cast (cd'.hom_type A A')) m).base)
  rw [D.baseChangeFunctor_cast' hc hst g cd cd' m]
  exact congrArg ULift.up (D.baseChangeHom_base' hst g _)

/-! ### Faithfulness of the top row -/

include hc in
/-- Transport of morphisms along base change is injective. -/
theorem baseChangeHom_injective' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) {A A' : CoherentObject (D.baseChange g)} :
    Function.Injective (D.baseChangeHom' hst g (A := A) (A' := A')) := by
  intro m n h
  have hb : m.base = n.base :=
    CostructuredArrow.hom_ext _ _ (by simpa using congrArg (fun k => k.base.left) h)
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  refine coherentHom_eq_of_heq rfl (heq_of_eq ?_)
  refine Functor.conjFibre_injective (D.baseChangeModuleSquare g mb)
    (D.fullyFaithful_modulePullback_baseChangeSpaceIso hc g A.T) ?_
  have hmid : (D.baseChangeHom' hst g (⟨mb, mf, mi⟩ : CoherentHom A A')).fibre =
      (D.baseChangeHom' hst g (⟨mb, nf, ni⟩ : CoherentHom A A')).fibre :=
    eq_of_heq (heq_fibre_of_eq h)
  exact ((D.baseChangeHom_fibre' hst g (⟨mb, mf, mi⟩ : CoherentHom A A')).symm.trans
    hmid).trans (D.baseChangeHom_fibre' hst g (⟨mb, nf, ni⟩ : CoherentHom A A'))

/-- The top row of the square of Stacks 08LP is faithful. -/
theorem baseChangeFunctor_faithful' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (D.baseChange g)) :
    letI : Category.{u + 1} (CoherentObject (D.baseChange g)) := cd'.category
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    (D.baseChangeFunctor' hc hst g cd cd').Faithful := by
  let _ : Category.{u + 1} (CoherentObject (D.baseChange g)) := cd'.category
  let _ : Category.{u + 1} (CoherentObject D) := cd.category
  constructor
  intro A A' m n h
  refine (Equiv.cast (cd'.hom_type A A')).injective ?_
  refine D.baseChangeHom_injective' hc hst g ?_
  rw [← D.baseChangeFunctor_cast' hc hst g cd cd' m,
    ← D.baseChangeFunctor_cast' hc hst g cd cd' n]
  exact congrArg (Equiv.cast (cd.hom_type _ _)) h

include hc in
/-- A morphism of `Coh_{X/Y}` between two transports whose base map comes from `Y'` is itself a
transport. -/
theorem exists_baseChangeHom' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) {A A' : CoherentObject (D.baseChange g)} (β : A.T ⟶ A'.T)
    (m : CoherentHom (D.baseChangeObject' hst g A) (D.baseChangeObject' hst g A'))
    (hβ : (D.overBase g).map β = m.base) :
    ∃ k : CoherentHom A A', k.base = β ∧ D.baseChangeHom' hst g k = m := by
  obtain ⟨mb, mf, mi⟩ := m
  change (D.overBase g).map β = mb at hβ
  subst hβ
  have hE := D.fullyFaithful_modulePullback_baseChangeSpaceIso hc g A.T
  refine ⟨⟨β, Functor.conjFibreInv (D.baseChangeModuleSquare g β) hE mf,
    Functor.isIso_conjFibreInv (D.baseChangeModuleSquare g β) hE mf mi⟩, rfl, ?_⟩
  refine coherentHom_eq_of_heq rfl (heq_of_eq ?_)
  refine (D.baseChangeHom_fibre' hst g _).trans ?_
  exact Functor.conjFibre_conjFibreInv (D.baseChangeModuleSquare g β) hE mf

/-! ### Lifting an object of `Coh_{X/Y}` whose test scheme factors through `Y'` -/

/-- The datum lifting an object of `Coh_{X/Y}` whose test scheme factors through `Y'`. -/
structure BaseChangeLift' (hc : ModulePushforwardCoherence B S hS)
    (hst : ModulePullbackStabilityOfFinitePresentation B S hS) (g : Y' ⟶ D.Y)
    (A : CoherentObject D) (T₀ : SchemesOver (D.baseChange g).Y) where
  /-- the lifted object -/
  obj : CoherentObject (D.baseChange g)
  /-- its test scheme is the given one -/
  objT : obj.T = T₀
  /-- its transport has the test scheme of the given object -/
  baseEq : (D.baseChangeObject' hst g obj).T = A.T
  /-- the comparison with the given object -/
  hom : CoherentHom (D.baseChangeObject' hst g obj) A
  /-- the comparison is vertical -/
  hom_base_left : hom.base.left =
    eqToHom (congrArg (fun T : SchemesOver D.Y => T.left) baseEq)

/-- An object of `Coh_{X/Y}` whose test scheme factors through `Y'` is the transport of an
object of `Coh_{X'/Y'}`. -/
def baseChangeLift' (hc : ModulePushforwardCoherence B S hS)
    (hst : ModulePullbackStabilityOfFinitePresentation B S hS) (g : Y' ⟶ D.Y)
    (A : CoherentObject D) (T₀ : SchemesOver (D.baseChange g).Y)
    (hT : A.T = (D.overBase g).obj T₀) :
    D.BaseChangeLift' hc hst g A T₀ := by
  obtain ⟨AT, AF, hqc, hfp, hfl, hps⟩ := A
  change AT = (D.overBase g).obj T₀ at hT
  subst hT
  have hsq := D.isPullback_baseChangeSpaceIso_hom g T₀
  exact
    { obj :=
        { T := T₀
          F := (modulePullback B S hS (D.baseChangeSpaceIso g T₀).hom).obj AF
          finitePresentation :=
            hst.finitePresentation (D.baseChangeSpaceIso g T₀).hom AF hfp
          quasicoherent :=
            have := hst.finitePresentation (D.baseChangeSpaceIso g T₀).hom AF hfp
            inferInstance
          flat := hst.flat hsq AF hfp hfl
          properSupport := by
            obtain ⟨hp, hU, hproper⟩ := hps
            obtain ⟨hU', hproper'⟩ :=
              hst.properSupport hsq hp AF hqc inferInstance hU hproper
            exact ⟨(isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback hsq hp,
              hU', hproper'⟩ }
      objT := rfl
      baseEq := rfl
      hom :=
        { base := 𝟙 _
          fibre := ((D.idComparison hc ((D.overBase g).obj T₀)).app AF ≪≫
            (hc.modulePullbackEquivalence (D.baseChangeSpaceIso g T₀)).unitIso.app AF).hom
          isIso_fibre := Iso.isIso_hom _ }
      hom_base_left := rfl }

/-! ### The square of Stacks 08LP and its universal property -/

/-- The square of Stacks 08LP: the 2-commutative square

`Coh_{X'/Y'} ⟶ Coh_{X/Y}`, `𝒮_{Y'} ⟶ 𝒮_Y`

whose top row is the base-change functor, whose two vertical arrows are the projections which
forget the module, and whose bottom row is the morphism induced by `g : Y' ⟶ Y`. -/
def baseChangeSquare' (hst : ModulePullbackStabilityOfFinitePresentation B S hS) (g : Y' ⟶ D.Y)
    (cd : CoherentCategoryData hc D) (cd' : CoherentCategoryData hc (D.baseChange g)) :
    @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
      (coherentBasedCategory cd) (baseBasedCategory (D.baseChange g).Y)
      (baseBasedCategory D.Y) (coherentToBase cd) (baseBasedMap g) where
  pt := coherentBasedCategory cd'
  fst := D.coherentBaseChangeMap' hc hst g cd cd'
  snd := coherentToBase cd'
  iso := eqToIso (D.coherentBaseChangeMap_comp_toBase' hc hst g cd cd')

/-- Arrow lifting for the square of Stacks 08LP: a morphism of `Coh_{X/Y}` between two
transports and a morphism of test schemes over `Y'` which lie over the same morphism of the site
come from a morphism of `Coh_{X'/Y'}`. -/
theorem baseChangeSquare_hlift' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (D.baseChange g)) :
    ∀ {A A' : (D.baseChangeSquare' hc hst g cd cd').pt.obj}
      (s : (D.baseChangeSquare' hc hst g cd cd').fst.obj A ⟶
        (D.baseChangeSquare' hc hst g cd cd').fst.obj A')
      (t : (D.baseChangeSquare' hc hst g cd cd').snd.obj A ⟶
        (D.baseChangeSquare' hc hst g cd cd').snd.obj A')
      {U V : BigFppfOver B S hS} (j : U ⟶ V),
      (coherentBasedCategory cd).p.IsHomLift j s →
      (baseBasedCategory (D.baseChange g).Y).p.IsHomLift j t →
      ∃ k : A ⟶ A', (D.baseChangeSquare' hc hst g cd cd').fst.map k = s ∧
        (D.baseChangeSquare' hc hst g cd cd').snd.map k = t := by
  let _ : Category.{u + 1} (CoherentObject (D.baseChange g)) := cd'.category
  let _ : Category.{u + 1} (CoherentObject D) := cd.category
  intro A A' s t U V j hs ht
  let ce := Equiv.cast (cd.hom_type (D.baseChangeObject' hst g A) (D.baseChangeObject' hst g A'))
  have e : (ce s).base.left = t.down.left := by
    show (coherentBasedCategory cd).p.map s =
      (baseBasedCategory (D.baseChange g).Y).p.map t
    rw [IsHomLift.fac' (coherentBasedCategory cd).p j s,
      IsHomLift.fac' (baseBasedCategory (D.baseChange g).Y).p j t]
    rfl
  have hβ : (D.overBase g).map t.down = (ce s).base := CostructuredArrow.hom_ext _ _ e.symm
  obtain ⟨k, hkb, hks⟩ := D.exists_baseChangeHom' hc hst g t.down _ hβ
  refine ⟨(Equiv.cast (cd'.hom_type A A')).symm k, ?_, ?_⟩
  · refine ce.injective ?_
    show ce ((D.baseChangeFunctor' hc hst g cd cd').map ((Equiv.cast (cd'.hom_type A A')).symm k)) =
      ce s
    refine (D.baseChangeFunctor_cast' hc hst g cd cd' _).trans ?_
    exact (congrArg (D.baseChangeHom' hst g (A := A) (A' := A'))
      (Equiv.apply_symm_apply (Equiv.cast (cd'.hom_type A A')) k)).trans hks
  · show ULift.up ((Equiv.cast (cd'.hom_type A A'))
      ((Equiv.cast (cd'.hom_type A A')).symm k)).base = t
    rw [Equiv.apply_symm_apply, hkb]
    rfl

/-- Object lifting for the square of Stacks 08LP: an object of any 2-commutative square over the
same cospan, naming an object `(T, ℱ)` of `Coh_{X/Y}` and a test scheme `T₀` over `Y'`, lifts to
an object of `Coh_{X'/Y'}` whose transport is vertically isomorphic to `(T, ℱ)`. -/
def baseChangeSquareLiftedObject' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (D.baseChange g))
    (T : @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
      (coherentBasedCategory cd) (baseBasedCategory (D.baseChange g).Y)
      (baseBasedCategory D.Y) (coherentToBase cd) (baseBasedMap g))
    (x : T.pt.obj) :
    Bicategory.SquareLiftedObject (D.baseChangeSquare' hc hst g cd cd') T x := by
  let _ : Category.{u + 1} (CoherentObject D) := cd.category
  let _ : Category.{u + 1} (CoherentObject (D.baseChange g)) := cd'.category
  have hobj : (ULiftHom.objUp.{u + 1, u + 1} ((T.fst.obj x : CoherentObject D)).T :
        BaseObjects D.Y) =
      ULiftHom.objUp.{u + 1, u + 1}
        ((D.overBase g).obj (ULiftHom.objDown.{u + 1, u + 1} (T.snd.obj x))) :=
    baseObjects_eq_of_vertical (T.iso.hom.toNatTrans.app x) (T.iso.hom.isHomLift' x)
  have hT : ((T.fst.obj x : CoherentObject D)).T =
      (D.overBase g).obj (ULiftHom.objDown.{u + 1, u + 1} (T.snd.obj x)) :=
    congrArg ULiftHom.objDown.{u + 1, u + 1} hobj
  have hfib : Functor.IsFiberedInGroupoids (coherentSiteProjection cd) := by
    rw [← coherentSiteProjection_eq cd]
    exact coherentProjection_isFiberedInGroupoids' hc cd
  set L := D.baseChangeLift' hc hst g (T.fst.obj x)
    (ULiftHom.objDown.{u + 1, u + 1} (T.snd.obj x)) hT
  have hb : (coherentSiteProjection cd).obj (T.fst.obj x) = T.pt.p.obj x := T.fst.w_obj x
  have ha : (coherentSiteProjection cd).obj (D.baseChangeObject' hst g L.obj) = T.pt.p.obj x :=
    (congrArg (fun W : SchemesOver D.Y => W.left) L.baseEq).trans hb
  have hmap : (coherentSiteProjection cd).map ((Equiv.cast (cd.hom_type
        (D.baseChangeObject' hst g L.obj) (T.fst.obj x))).symm L.hom) =
      eqToHom (congrArg (fun W : SchemesOver D.Y => W.left) L.baseEq) := by
    change ((Equiv.cast (cd.hom_type (D.baseChangeObject' hst g L.obj) (T.fst.obj x)))
      ((Equiv.cast (cd.hom_type (D.baseChangeObject' hst g L.obj)
        (T.fst.obj x))).symm L.hom)).base.left = _
    rw [Equiv.apply_symm_apply]
    exact L.hom_base_left
  have hvert : (coherentSiteProjection cd).IsHomLift (𝟙 (T.pt.p.obj x))
      ((Equiv.cast (cd.hom_type (D.baseChangeObject' hst g L.obj)
        (T.fst.obj x))).symm L.hom) := by
    refine IsHomLift.of_fac' _ _ _ ha hb ?_
    rw [hmap]
    simp only [Category.id_comp, eqToHom_trans]
    rfl
  have hiso : IsIso ((Equiv.cast (cd.hom_type (D.baseChangeObject' hst g L.obj)
      (T.fst.obj x))).symm L.hom) :=
    Functor.isIso_of_isHomLift_id' (coherentSiteProjection cd) hfib _ hvert
  have hb' : (baseBasedCategory (D.baseChange g).Y).p.obj (T.snd.obj x) = T.pt.p.obj x :=
    T.snd.w_obj x
  have ha' : (baseBasedCategory (D.baseChange g).Y).p.obj
      (ULiftHom.objUp.{u + 1, u + 1} L.obj.T) = T.pt.p.obj x :=
    (congrArg (baseBasedCategory (D.baseChange g).Y).p.obj
      (congrArg ULiftHom.objUp.{u + 1, u + 1} L.objT)).trans hb'
  exact
    { obj := L.obj
      fstIso := @asIso _ _ _ _ ((Equiv.cast (cd.hom_type (D.baseChangeObject' hst g L.obj)
        (T.fst.obj x))).symm L.hom) hiso
      sndIso := eqToIso (congrArg ULiftHom.objUp.{u + 1, u + 1} L.objT)
      fst_vertical := hvert
      snd_vertical :=
        Functor.isHomLift_id_eqToHom_of_obj_eq (baseBasedCategory (D.baseChange g).Y).p
          (congrArg ULiftHom.objUp.{u + 1, u + 1} L.objT) ha' }

/-- The square `Coh_{X'/Y'} ⟶ Coh_{X/Y}`, `𝒮_{Y'} ⟶ 𝒮_Y` of Stacks 08LP is 2-cartesian:
`Coh_{X'/Y'}`, with the base-change functor and the projection forgetting the module, is a
2-fibre product of the projection `Coh_{X/Y} ⟶ 𝒮_Y` with the morphism `𝒮_{Y'} ⟶ 𝒮_Y`. -/
def baseChangeSquare_isTwoFibreProduct' (hst : ModulePullbackStabilityOfFinitePresentation B S hS)
    (g : Y' ⟶ D.Y) (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (D.baseChange g)) :
    Bicategory.IsTwoFibreProduct (D.baseChangeSquare' hc hst g cd cd') :=
  have _h1 : (baseBasedCategory D.Y).p.Faithful := baseBasedCategory_faithful D.Y
  have _h2 : (D.baseChangeSquare' hc hst g cd cd').fst.toFunctor.Faithful :=
    D.baseChangeFunctor_faithful' hc hst g cd cd'
  Bicategory.squareIsTerminal (D.baseChangeSquare' hc hst g cd cd')
    (D.baseChangeSquare_hlift' hc hst g cd cd')
    (fun T x => D.baseChangeSquareLiftedObject' hc hst g cd cd' T x)

end CoherentSituation

end AlgebraicGeometry.Space

end
