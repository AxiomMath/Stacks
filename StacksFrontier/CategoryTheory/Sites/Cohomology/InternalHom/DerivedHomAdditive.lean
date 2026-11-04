module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Center.Linear
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom is additive and linear over the structure sheaf

Let `(𝒞, 𝒪)` be a ringed site and `K ∈ D(𝒪)`. This file proves two properties of the functor
`R𝑆heafHom_𝒪(K, -) : D(𝒪) ⥤ D(𝒪)`
(`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` evaluated at `K`): it is additive, and
it carries multiplication by a compatible family of local sections of `𝒪` to multiplication by
that same family. Both are needed to transport the derived-completeness condition
`T(-, f) = 0` through derived internal Hom, which is [Stacks, Tag 099A].

## Main results

* `AlgebraicGeometry.RingedSite.homMap_add_right` — the induced map of internal Hom complexes is
  additive in the morphism of targets.
* `AlgebraicGeometry.RingedSite.homMap_add_left` — and in the morphism of sources.
* `AlgebraicGeometry.RingedSite.additive_derivedSheafHom_flip_obj` — `R𝑆heafHom_𝒪(-, E)` is
  additive.  This is the contravariant counterpart of `additive_derivedSheafHom_obj`, needed
  wherever the difference map of a system has to pass through `R𝑆heafHom_𝒪(-, E)`.
* `AlgebraicGeometry.RingedSite.homMap_globalSectionToEnd` — at the level of internal Hom
  complexes, the map induced by multiplication by a global section is multiplication by that
  section.
* `AlgebraicGeometry.RingedSite.additive_derivedSheafHom_obj` — `R𝑆heafHom_𝒪(K, -)` is additive.
* `AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd` — `R𝑆heafHom_𝒪(K, -)`
  carries multiplication by a global section to multiplication by that section.

## Implementation notes

**Why the functorial K-injective resolution is not used.** The obvious route to additivity would
be to transport it along the localization from the model bifunctor
`AlgebraicGeometry.RingedSite.derivedSheafHomModel`, which is the internal Hom complex into the
functorial K-injective resolution of [Stacks, Tag 079P]. That route is closed: the resolution
functor `Stacks.Injectives.kInjectiveResolutionFunctor` is **not** additive. It is a chosen
witness of `Stacks.Injectives.FunctorialKInjectiveResolution`, a structure with no additivity
field, produced by transfinite iteration of two steps — a small-object construction whose
coproducts are indexed by the sets of lifting problems, and a functorial injective enlargement —
and a functor whose value on a morphism reindexes a coproduct indexed by a Hom-set does not
respect addition of morphisms. There is nothing to prove there.

Both results are instead proved by reduction to K-injective **representatives**, using only the
comparison `AlgebraicGeometry.RingedSite.derivedSheafHomComparison` and its naturality:
on the class of a K-injective complex the derived internal Hom is the class of the ordinary
internal Hom complex, every object of `D(𝒪)` is the class of a K-injective complex
(`AlgebraicGeometry.RingedSite.kInjectiveModel`), and every morphism into the class of a
K-injective complex is the class of a morphism of complexes
(`AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective`). The resolution functor is used
only to produce those representatives, never as a functor.

**Why the algebra is factored through abstract lemmas.** The terms involved — the descent of a
bifunctor through two localizations, composed with the lifting isomorphism — are large enough
that `rw` with a generic `Preadditive` or `Linear` distributivity lemma exhausts the heartbeat
budget while trying to whnf them. Every such step is therefore isolated in a lemma
(`AlgebraicGeometry.RingedSite.eq_add_of_mono`,
`AlgebraicGeometry.RingedSite.eq_smul_id_of_mono`,
`AlgebraicGeometry.RingedSite.additive_of_representatives`,
`AlgebraicGeometry.RingedSite.map_smul_id_of_iso`,
`AlgebraicGeometry.RingedSite.map_smul_id_of_natIso`) stated for arbitrary morphisms of an
arbitrary preadditive category, so that the distributivity is proved once on small terms and the
large terms only ever appear as the arguments of an `exact`.

The scalars are the central endomorphisms `Stacks.SheafOfModules.globalSectionToEnd` given by a
compatible family of local sections of `𝒪`, which is the form in which the derived-completeness
predicate of [Stacks, Tag 0999] supplies them. The linear structure is the one that predicate
uses: `CategoryTheory.Linear.ofRingMorphism` along the identity of the centre.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.RingedSite

/-- **A functor is additive as soon as it is additive on the morphisms between a chosen family of
representatives.** Given a choice `R M ≅ M` of representative for every object, every morphism is
the conjugate of a morphism between representatives, and conjugation is additive. -/
theorem additive_of_representatives {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) (R : C → C) (e : ∀ M, R M ≅ M)
    (h : ∀ (M N : C) (f g : R M ⟶ R N), F.map (f + g) = F.map f + F.map g) : F.Additive := by
  constructor
  intro M N f g
  have key : ∀ t : M ⟶ N, F.map t =
      F.map (e M).inv ≫ F.map ((e M).hom ≫ t ≫ (e N).inv) ≫ F.map (e N).hom := by
    intro t
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    simp
  have hsum : (e M).hom ≫ (f + g) ≫ (e N).inv =
      ((e M).hom ≫ f ≫ (e N).inv) + ((e M).hom ≫ g ≫ (e N).inv) := by
    rw [Preadditive.add_comp, Preadditive.comp_add]
  rw [key (f + g), key f, key g, hsum, h M N, Preadditive.add_comp, Preadditive.comp_add]

/-- **A monomorphism detects a sum.** If three morphisms `u`, `v`, `w` with common source and
target become, after composition with a monomorphism, the composites of one morphism with `α`,
with `β` and with `α + β`, then `w = u + v`. -/
theorem eq_add_of_mono {C : Type*} [Category C] [Preadditive C] {Y Z S T : C}
    {u v w : Y ⟶ Z} {c' : Z ⟶ T} [Mono c'] {c : Y ⟶ S} {α β : S ⟶ T}
    (hu : u ≫ c' = c ≫ α) (hv : v ≫ c' = c ≫ β)
    (hw : w ≫ c' = c ≫ (α + β)) : w = u + v := by
  refine (cancel_mono c').mp ?_
  rw [hw, Preadditive.comp_add, ← hu, ← hv, Preadditive.add_comp]

/-- **A monomorphism detects multiplication by a scalar.** If an endomorphism `u` of `Y` becomes,
after composition with a monomorphism `c`, the composite of `c` with multiplication by `r`, then
`u` is multiplication by `r`. -/
theorem eq_smul_id_of_mono {R : Type*} [Semiring R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] {Y T : C} {u : Y ⟶ Y} {c : Y ⟶ T} [Mono c] {r : R}
    (hu : u ≫ c = c ≫ (r • 𝟙 T)) : u = r • 𝟙 Y := by
  refine (cancel_mono c).mp ?_
  rw [hu, Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

/-- A functor carries multiplication by a scalar to multiplication by that scalar at an object as
soon as it does so at an isomorphic object. -/
theorem map_smul_id_of_iso {R : Type*} [Semiring R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D] (F : C ⥤ D) (r : R) {M N : C}
    (e : M ≅ N) (h : F.map (r • 𝟙 M) = r • 𝟙 (F.obj M)) :
    F.map (r • 𝟙 N) = r • 𝟙 (F.obj N) := by
  have he : r • 𝟙 N = e.inv ≫ (r • 𝟙 M) ≫ e.hom := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.inv_hom_id]
  rw [he, F.map_comp, F.map_comp, h, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    ← F.map_comp, e.inv_hom_id, F.map_id]

/-- Carrying multiplication by a scalar to multiplication by that scalar is invariant under
isomorphism of functors. -/
theorem map_smul_id_of_natIso {R : Type*} [Semiring R] {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D] {F G : C ⥤ D}
    (e : F ≅ G) (r : R) (M : C) (h : F.map (r • 𝟙 M) = r • 𝟙 (F.obj M)) :
    G.map (r • 𝟙 M) = r • 𝟙 (G.obj M) := by
  refine (cancel_epi (e.hom.app M)).mp ?_
  rw [← e.hom.naturality, h, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    Category.comp_id]

variable (X : RingedSite.{u, u, u})

/-- Sheaves of modules are linear over the centre of their own category. This is the linear
structure the derived-completeness predicate of [Stacks, Tag 0999] uses. -/
abbrev linearCatCenterRingSheaf :
    Linear (CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Linear.ofRingMorphism (RingHom.id _)

attribute [local instance] linearCatCenterRingSheaf

section Chain

variable
  {K K' M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Two morphisms of sheaves of modules on the slice site over `U` agree as soon as they agree on
the sections over every object presented as `Over.mk f`. -/
theorem sliceHom_ext {U : X.C}
    {A B : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)} {φ ψ : A ⟶ B}
    (h : ∀ (W : X.C) (f : W ⟶ U) (x : A.val.obj (op (Over.mk f))),
      (φ.val.app (op (Over.mk f))) x = (ψ.val.app (op (Over.mk f))) x) : φ = ψ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨V⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact h V.left V.hom x

/-- Two morphisms of complexes into an internal Hom complex agree as soon as they agree on
sections, after passing to the description of sections as cochains. -/
private theorem hom_ext_of_sectionsEquiv
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {f g : P ⟶ (sheafHomComplex X K' M').obj}
    (h : ∀ (n : ℤ) (U : X.C) (s : (P.X n).val.obj (op U)),
      (sheafHomComplex X K' M').sectionsEquiv U n ((f.f n).val.app (op U) s) =
        (sheafHomComplex X K' M').sectionsEquiv U n ((g.f n).val.app (op U) s)) : f = g := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨U⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact ((sheafHomComplex X K' M').sectionsEquiv U n).injective (h n U s)

/-- Pre- and postcomposition of cochains is additive in the postcomposed morphism. -/
lemma cochainConj_add_right (U : X.C) (k : K' ⟶ K) (m m' : M ⟶ M') {n : ℤ}
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainConj X U k (m + m') c = cochainConj X U k m c + cochainConj X U k m' c := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [cochainConj_v, Cochain.add_v, cochainConj_v, cochainConj_v]
  have h : ((m + m').f q).over U = (m.f q).over U + (m'.f q).over U :=
    (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_add
  rw [h, Preadditive.comp_add, Preadditive.comp_add]

/-- The induced map of internal Hom complexes is additive in the morphism of targets. -/
lemma homMap_add_right (k : K' ⟶ K) (m m' : M ⟶ M') :
    homMap X k (m + m') = homMap X k m + homMap X k m' := by
  refine hom_ext_of_sectionsEquiv X fun n U s => ?_
  have hsum : ((homMap X k m + homMap X k m').f n).val.app (op U) s =
      ((homMap X k m).f n).val.app (op U) s + ((homMap X k m').f n).val.app (op U) s := rfl
  rw [homMap_f, sectionsEquiv_homMapHom, cochainConj_add_right, hsum, map_add, homMap_f,
    homMap_f, sectionsEquiv_homMapHom, sectionsEquiv_homMapHom]

/-- Pre- and postcomposition of cochains is additive in the precomposed morphism. -/
lemma cochainConj_add_left (U : X.C) (k k' : K' ⟶ K) (m : M ⟶ M') {n : ℤ}
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainConj X U (k + k') m c = cochainConj X U k m c + cochainConj X U k' m c := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [cochainConj_v, Cochain.add_v, cochainConj_v, cochainConj_v]
  have h : ((k + k').f p).over U = (k.f p).over U + (k'.f p).over U :=
    (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_add
  rw [h, Preadditive.add_comp]

/-- The induced map of internal Hom complexes is additive in the morphism of sources. -/
lemma homMap_add_left (k k' : K' ⟶ K) (m : M ⟶ M') :
    homMap X (k + k') m = homMap X k m + homMap X k' m := by
  refine hom_ext_of_sectionsEquiv X fun n U s => ?_
  have hsum : ((homMap X k m + homMap X k' m).f n).val.app (op U) s =
      ((homMap X k m).f n).val.app (op U) s + ((homMap X k' m).f n).val.app (op U) s := rfl
  rw [homMap_f, sectionsEquiv_homMapHom, cochainConj_add_left, hsum, map_add, homMap_f,
    homMap_f, sectionsEquiv_homMapHom, sectionsEquiv_homMapHom]

/-- **Multiplication by a global section passes through the internal Hom complex.** The map of
internal Hom complexes induced by multiplication by a compatible family of local sections of `𝒪`
in the target is multiplication by that same family. -/
lemma homMap_globalSectionToEnd
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙ forget RingCat).sections) :
    homMap X (𝟙 A)
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 B) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 (sheafHomComplex X A B).obj := by
  refine hom_ext_of_sectionsEquiv X fun n U s => ?_
  rw [homMap_f, sectionsEquiv_homMapHom]
  refine Cochain.ext _ _ fun p q hpq => ?_
  refine sliceHom_ext X fun W g x => ?_
  have hid : SheafOfModules.Hom.over (𝟙 (A.X p)) U = 𝟙 ((A.X p).over U) := rfl
  have hcomp :
      ∀ {P Q R : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)}
        (φ : P ⟶ Q) (ψ : Q ⟶ R) (V : (Over U)ᵒᵖ) (y : P.val.obj V),
      ((φ ≫ ψ).val.app V) y = (ψ.val.app V) ((φ.val.app V) y) := fun _ _ _ _ => rfl
  have hR0 : (ModuleCat.Hom.hom
      (((Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 (sheafHomComplex X A B).obj).f n).val.app (op U))) s =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) from
        a.val (op U)) • s := rfl
  have hsec :
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj (op (Over.mk g)) from
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op
          (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) from
            a.val (op U))) =
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj (op (Over.mk g)) from
        a.val (op W)) := a.property g.op
  rw [cochainConj_v, HomologicalComplex.id_f, hid, Category.id_comp, hcomp, hR0,
    (sheafHomComplex X A B).sectionsEquiv_smul U
      (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) from a.val (op U))
      n p q hpq s g x, hsec]
  rfl

end Chain

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The K-injective model comparison, natural in a K-injective target at an identity source.
This is `AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality` with the source
morphism taken to be an identity. -/
theorem derivedSheafHomComparison_naturality_id_source
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [B.IsKInjective] [B'.IsKInjective] (φ : B ⟶ B') :
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
          (DerivedCategory.Q.map φ) ≫ (derivedSheafHomComparison X A B').hom =
      (derivedSheafHomComparison X A B).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 A) φ) := by
  have h := derivedSheafHomComparison_naturality X (𝟙 A) φ
  rwa [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h

/-- Derived internal Hom out of the class of `A` is additive on morphisms between classes of
K-injective complexes: such a morphism is the class of a morphism of complexes, the induced map
of internal Hom complexes is additive, and the model comparison is a monomorphism. -/
private lemma derivedSheafHom_map_add_of_isKInjective
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [B.IsKInjective] [B'.IsKInjective]
    (f g : DerivedCategory.Q.obj B ⟶ DerivedCategory.Q.obj B') :
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map (f + g) =
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map f +
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map g := by
  obtain ⟨φ, rfl⟩ := exists_Q_map_eq_of_isKInjective X f
  obtain ⟨ψ, rfl⟩ := exists_Q_map_eq_of_isKInjective X g
  have hadd : DerivedCategory.Q.map (φ + ψ) =
      DerivedCategory.Q.map φ + DerivedCategory.Q.map ψ := DerivedCategory.Q.map_add
  have hQH : DerivedCategory.Q.map (homMap X (𝟙 A) (φ + ψ)) =
      DerivedCategory.Q.map (homMap X (𝟙 A) φ) +
        DerivedCategory.Q.map (homMap X (𝟙 A) ψ) := by
    rw [homMap_add_right]
    exact DerivedCategory.Q.map_add
  refine eq_add_of_mono (c' := (derivedSheafHomComparison X A B').hom)
    (derivedSheafHomComparison_naturality_id_source X A φ)
    (derivedSheafHomComparison_naturality_id_source X A ψ) ?_
  rw [← hadd, derivedSheafHomComparison_naturality_id_source, hQH]

/-- **Derived internal Hom out of a fixed object is an additive functor.** Every object of
`D(𝒪)` is the class of a K-injective complex, which reduces additivity to the K-injective
models, where the functor is the class of the induced map of internal Hom complexes. -/
instance additive_derivedSheafHom_obj
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).obj (op A)).Additive := by
  have hQ :
      ∀ A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A₀))).Additive := fun A₀ =>
    additive_of_representatives _ (fun M => DerivedCategory.Q.obj (kInjectiveModel X M))
      (fun M => kInjectiveModelIso X M)
      (fun _ _ f g => derivedSheafHom_map_add_of_isKInjective X A₀ f g)
  have := hQ (kInjectiveModel X A)
  exact Functor.additive_of_iso
    ((derivedSheafHomBifunctor X).mapIso (kInjectiveModelIso X A).symm.op)

/-- The K-injective model comparison, natural in the source at an identity target.  This is
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality` with the target morphism
taken to be an identity, in the `AlgebraicGeometry.RingedSite.homMap` spelling. -/
theorem derivedSheafHomComparison_naturality_id_target
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [E.IsKInjective]
    {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : A' ⟶ A) :
    ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map φ).op).app
          (DerivedCategory.Q.obj E) ≫ (derivedSheafHomComparison X A' E).hom =
      (derivedSheafHomComparison X A E).hom ≫
        DerivedCategory.Q.map (homMap X φ (𝟙 E)) := by
  have h := derivedSheafHomComparison_naturality X φ (𝟙 E)
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h

/-- Derived internal Hom into the class of a K-injective complex is additive on morphisms whose
target is the class of a K-injective complex: such a morphism is the class of a morphism of
complexes, the induced map of internal Hom complexes is additive in the source, and the model
comparison is a monomorphism. -/
private lemma derivedSheafHom_flip_map_add_of_isKInjective
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [E.IsKInjective]
    {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [A.IsKInjective]
    (f g : DerivedCategory.Q.obj A' ⟶ DerivedCategory.Q.obj A) :
    ((derivedSheafHomBifunctor X).map (f + g).op).app (DerivedCategory.Q.obj E) =
      ((derivedSheafHomBifunctor X).map f.op).app (DerivedCategory.Q.obj E) +
        ((derivedSheafHomBifunctor X).map g.op).app (DerivedCategory.Q.obj E) := by
  obtain ⟨φ, rfl⟩ := exists_Q_map_eq_of_isKInjective X f
  obtain ⟨ψ, rfl⟩ := exists_Q_map_eq_of_isKInjective X g
  have hadd : DerivedCategory.Q.map (φ + ψ) =
      DerivedCategory.Q.map φ + DerivedCategory.Q.map ψ := DerivedCategory.Q.map_add
  have hQH : DerivedCategory.Q.map (homMap X (φ + ψ) (𝟙 E)) =
      DerivedCategory.Q.map (homMap X φ (𝟙 E)) +
        DerivedCategory.Q.map (homMap X ψ (𝟙 E)) := by
    rw [homMap_add_left]
    exact DerivedCategory.Q.map_add
  refine eq_add_of_mono (c' := (derivedSheafHomComparison X A' E).hom)
    (derivedSheafHomComparison_naturality_id_target X E φ)
    (derivedSheafHomComparison_naturality_id_target X E ψ) ?_
  rw [← hadd, derivedSheafHomComparison_naturality_id_target, hQH]

/-- **Derived internal Hom into a fixed object is an additive functor of its contravariant
variable.** Every object of `D(𝒪)` is the class of a K-injective complex, which reduces
additivity to morphisms between K-injective models; there the functor is the class of the induced
map of internal Hom complexes, which is additive in the source. -/
instance additive_derivedSheafHom_flip_obj
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).flip.obj E).Additive := by
  have hQ :
      ∀ (E₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        [E₀.IsKInjective],
        ((derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj E₀)).Additive := fun E₀ _ =>
    additive_of_representatives _
      (fun M => op (DerivedCategory.Q.obj (kInjectiveModel X M.unop)))
      (fun M => (kInjectiveModelIso X M.unop).op.symm)
      (fun _ _ f g => derivedSheafHom_flip_map_add_of_isKInjective X E₀ f.unop g.unop)
  have := hQ (kInjectiveModel X E)
  exact Functor.additive_of_iso
    ((derivedSheafHomBifunctor X).flip.mapIso (kInjectiveModelIso X E))

/-- Derived internal Hom out of the class of `A` carries multiplication by a global section to
multiplication by that section, on the class of a K-injective complex. -/
private lemma derivedSheafHom_map_globalSectionToEnd_model
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙ forget RingCat).sections)
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 (DerivedCategory.Q.obj B)) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj B)) := by
  have hQ : DerivedCategory.Q.map
      (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 B) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 (DerivedCategory.Q.obj B) := by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  have hQ2 : DerivedCategory.Q.map
      (homMap X (𝟙 A)
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 B)) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 (DerivedCategory.Q.obj (sheafHomComplex X A B).obj) := by
    rw [homMap_globalSectionToEnd, Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  refine eq_smul_id_of_mono (c := (derivedSheafHomComparison X A B).hom) ?_
  rw [← hQ, derivedSheafHomComparison_naturality_id_source, hQ2]

/-- **Derived internal Hom out of a fixed object carries multiplication by a global section to
multiplication by that section.** This is the `𝒪`-linearity of `R𝑆heafHom_𝒪(K, -)` in its second
variable, at the central endomorphisms given by compatible families of local sections of `𝒪`. -/
theorem derivedSheafHom_map_globalSectionToEnd
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙ forget RingCat).sections)
    (A M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).obj (op A)).map
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 M) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 (((derivedSheafHomBifunctor X).obj (op A)).obj M) := by
  have hQ :
      ∀ (A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        (N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A₀))).map
          (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
            𝟙 N) =
          Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
            𝟙 (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A₀))).obj N) :=
    fun A₀ N =>
    map_smul_id_of_iso _ _ (kInjectiveModelIso X N)
      (derivedSheafHom_map_globalSectionToEnd_model X a A₀ (kInjectiveModel X N))
  exact map_smul_id_of_natIso
    ((derivedSheafHomBifunctor X).mapIso (kInjectiveModelIso X A).symm.op) _ M
    (hQ (kInjectiveModel X A) M)

end Derived

end AlgebraicGeometry.RingedSite

end
