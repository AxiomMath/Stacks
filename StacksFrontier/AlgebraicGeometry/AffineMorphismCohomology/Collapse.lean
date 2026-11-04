module

public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.AcyclicQuasiIso
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.ResolutionDesc

/-!
# Collapse of the derived functor of a composite at an acyclic object, without preserved injectives

Let `G : 𝒞 ⥤ 𝒟` be additive and left exact, let `T : 𝒟 ⥤ ℰ` be additive and left exact, with
`𝒟` having enough injectives, and assume

* `G` carries injective objects to objects that are **right acyclic for `T`**, and
* the object `A` of `𝒞` is `G`-acyclic, i.e. `R ⁿ G (A) = 0` for `n > 0`.

Then the right derived functors of the composite collapse: `R ⁿ (G ⋙ T) (A) ≅ R ⁿ T (G A)`, the
isomorphism is computed by any augmentation-preserving comparison of `G` applied to an injective
resolution of `A` with an injective resolution of `G A`, in degree zero it intertwines the two
canonical maps to the zeroth right derived functors, and it is natural in `A` over any class of
`G`-acyclic objects.

`Stacks.RightDerivedComp` already proves all of this under the **stronger** hypothesis that `G`
preserves injective objects; there, `G` applied to an injective resolution *is* an injective
resolution, so Mathlib's `CategoryTheory.InjectiveResolution.isoRightDerivedObj` applies to it
directly. That hypothesis is false for the pushforward of sheaves of modules, which is why
[Stacks, Tag 089W] is not a corollary of that file. What survives is that `G` applied to an
injective resolution is an *exact* resolution whose terms are `T`-acyclic
(`Stacks.RightDerivedComp.quasiIso_mapι` needs only left exactness of `G` and acyclicity of `A`),
and that is enough:

* `Stacks.AcyclicQuasiIso.isIso_homologyMap_map` makes the comparison with an injective
  resolution of `G A` invertible on homology, which replaces `isoRightDerivedObj` on that side;
* `Stacks.ResolutionDesc.desc` constructs such a comparison and
  `Stacks.ResolutionDesc.homologyMap_map_eq` says that any two of them agree on homology, which
  replaces `CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality` on that side.

## Main definitions

* `Stacks.AcyclicCollapse.canonicalDesc`: the comparison of `G` applied to the chosen injective
  resolution of `A` with the chosen injective resolution of `G A`.
* `Stacks.AcyclicCollapse.objIso`: the collapse isomorphism `R ⁿ (G ⋙ T) (A) ≅ R ⁿ T (G A)`.
* `Stacks.AcyclicCollapse.natIso`: it as a natural isomorphism, over a class of `G`-acyclic
  objects.

## Main results

* `Stacks.AcyclicCollapse.objIso_hom_eq`: the collapse isomorphism is computed by **any**
  injective resolution `I` of `A`, **any** injective resolution `J` of `G A` and **any**
  comparison `φ` between them preserving the augmentation.
* `Stacks.AcyclicCollapse.toRightDerivedZero_comp_objIso_hom`: in degree zero it intertwines
  `G ⋙ T ⟶ R ⁰(G ⋙ T)` with `T ⟶ R ⁰T`.
* `Stacks.AcyclicCollapse.objIso_hom_naturality`: naturality in the `G`-acyclic object.

## Implementation notes

The `T`-acyclicity of the terms of `G` applied to an injective resolution is
`rightAcyclic_mapCocomplex_X`, which is the hypothesis `hacyc` read at `I.cocomplex.X n`; the
terms of an injective resolution of `G A` are `T`-acyclic because injective objects are acyclic
for every additive functor (`Stacks.Cohomology.Leray.rightAcyclic_of_injective`).

`objIso_hom_eq` is proved by comparing `(I, J, φ)` with the chosen data through two descents of
identity morphisms: `CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality` moves
the `𝒞`-side resolution and `isoRightDerivedObj_inv_naturality` the `𝒟`-side one, after which
the two remaining comparisons `G I ⟶ J₀` have the same degree-zero augmentation and
`Stacks.ResolutionDesc.homologyMap_map_eq` identifies them. The same two moves prove naturality.

## References

* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open Stacks.RightDerivedComp

namespace Stacks.AcyclicCollapse

universe v v' v'' u u' u''

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{max u' v'} D] [HasDerivedCategory.{max u'' v''} E]
  [EnoughInjectives C] [EnoughInjectives D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]
  (T : D ⥤ E) [T.Additive] [PreservesFiniteLimits T]
  (hacyc : ∀ I : C, Injective I → T.rightAcyclic (G.obj I))

/-! ### The two families of right acyclic terms -/

omit [EnoughInjectives C] [PreservesFiniteLimits G] [PreservesFiniteLimits T] in
include hacyc in
/-- `G` applied to an injective resolution has `T`-acyclic terms: that is the hypothesis
`hacyc`, read at each term. -/
theorem rightAcyclic_mapCocomplex_X {A : C} (I : InjectiveResolution A) (n : ℕ) :
    T.rightAcyclic ((mapCocomplex G I).X n) :=
  hacyc _ (I.injective n)

omit [EnoughInjectives C] [PreservesFiniteLimits G] [PreservesFiniteLimits T] in
/-- An injective resolution has `T`-acyclic terms, because injective objects are right acyclic
for every additive functor. -/
theorem rightAcyclic_cocomplex_X {B : D} (J : InjectiveResolution B) (n : ℕ) :
    T.rightAcyclic (J.cocomplex.X n) :=
  Stacks.Cohomology.Leray.rightAcyclic_of_injective T _ (J.injective n)

/-! ### The comparison is a quasi-isomorphism, and invertible on homology after `T` -/

variable {A : C} (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))

omit [HasDerivedCategory D] [EnoughInjectives C] [EnoughInjectives D] [PreservesFiniteLimits G]
  [PreservesFiniteLimits T] in
/-- The augmentation condition, rewritten with the augmentation
`Stacks.RightDerivedComp.mapι` of `G` applied to the resolution. -/
theorem mapι_f_zero_comp (I : InjectiveResolution A) (J : InjectiveResolution (G.obj A))
    (φ : mapCocomplex G I ⟶ J.cocomplex)
    (hφ : G.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (mapι G I).f 0 ≫ φ.f 0 = J.ι.f 0 :=
  (congrArg (· ≫ φ.f 0) (mapι_f_zero G I)).trans hφ

omit [HasDerivedCategory D] [EnoughInjectives D] in
include hA in
/-- An augmentation-preserving comparison of `G` applied to an injective resolution of a
`G`-acyclic object with an injective resolution of its image is a quasi-isomorphism: both
augmentations are, by `Stacks.RightDerivedComp.quasiIso_mapι`. -/
theorem quasiIso_comparison (I : InjectiveResolution A) (J : InjectiveResolution (G.obj A))
    (φ : mapCocomplex G I ⟶ J.cocomplex)
    (hφ : G.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) : QuasiIso φ := by
  have hι : QuasiIso (mapι G I) := quasiIso_mapι G I hA
  have key : mapι G I ≫ φ = J.ι := by
    refine HomologicalComplex.hom_ext _ _ fun i => ?_
    match i with
    | 0 =>
      exact (HomologicalComplex.comp_f _ _ 0).trans (mapι_f_zero_comp G I J φ hφ)
    | (i + 1) =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (G.obj A) (i + 1)
        (by simp)).eq_of_src _ _
  have : QuasiIso (mapι G I ≫ φ) := by
    rw [key]
    infer_instance
  exact quasiIso_of_comp_left (mapι G I) φ

include hacyc hA in
/-- **`T` applied termwise to such a comparison is invertible on homology in every degree.**
This is what replaces the fact that `G` applied to an injective resolution is itself an
injective resolution. -/
theorem isIso_homologyMap_map (I : InjectiveResolution A) (J : InjectiveResolution (G.obj A))
    (φ : mapCocomplex G I ⟶ J.cocomplex)
    (hφ : G.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n) :=
  have := quasiIso_comparison G hA I J φ hφ
  Stacks.AcyclicQuasiIso.isIso_homologyMap_map T φ
    (rightAcyclic_mapCocomplex_X G T hacyc I) (rightAcyclic_cocomplex_X T J) n

/-! ### The collapse isomorphism -/

include hA in
/-- The chosen comparison: `G` applied to the chosen injective resolution of `A` is an exact
resolution of `G A`, so `Stacks.ResolutionDesc.desc` compares it with the chosen injective
resolution of `G A`. -/
noncomputable def canonicalDesc :
    mapCocomplex G (injectiveResolution A) ⟶ (injectiveResolution (G.obj A)).cocomplex :=
  have := quasiIso_mapι G (injectiveResolution A) hA
  Stacks.ResolutionDesc.desc (mapι G (injectiveResolution A)) (injectiveResolution (G.obj A))

omit [HasDerivedCategory D] in
include hA in
/-- The degree-zero component of `canonicalDesc` is compatible with the augmentations: composing
it with the degree-zero component of `mapι` gives the augmentation of the chosen injective
resolution of `G A`. -/
theorem mapι_f_zero_comp_canonicalDesc :
    (mapι G (injectiveResolution A)).f 0 ≫ (canonicalDesc G hA).f 0 =
      (injectiveResolution (G.obj A)).ι.f 0 :=
  have := quasiIso_mapι G (injectiveResolution A) hA
  Stacks.ResolutionDesc.f_zero_comp_desc_f_zero (mapι G (injectiveResolution A))
    (injectiveResolution (G.obj A))

omit [HasDerivedCategory D] in
include hA in
/-- `canonicalDesc` preserves augmentations: `G` applied to the augmentation of the chosen
injective resolution of `A`, followed by the degree-zero component of `canonicalDesc`, is the
augmentation of the chosen injective resolution of `G A`. -/
theorem canonicalDesc_comm :
    G.map ((injectiveResolution A).ι.f 0) ≫ (canonicalDesc G hA).f 0 =
      (injectiveResolution (G.obj A)).ι.f 0 :=
  (congrArg (· ≫ (canonicalDesc G hA).f 0) (mapι_f_zero G (injectiveResolution A)).symm).trans
    (mapι_f_zero_comp_canonicalDesc G hA)

include hacyc hA in
/-- **The collapse isomorphism `R ⁿ (G ⋙ T) (A) ≅ R ⁿ T (G A)`.** -/
noncomputable def objIso (n : ℕ) :
    ((G ⋙ T).rightDerived n).obj A ≅ (T.rightDerived n).obj (G.obj A) :=
  (injectiveResolution A).isoRightDerivedObj (G ⋙ T) n ≪≫
    @asIso _ _ _ _ _ (isIso_homologyMap_map G T hacyc hA (injectiveResolution A)
      (injectiveResolution (G.obj A)) (canonicalDesc G hA) (canonicalDesc_comm G hA) n) ≪≫
    ((injectiveResolution (G.obj A)).isoRightDerivedObj T n).symm

include hacyc hA in
/-- The forward map of `objIso` is the map induced on homology by `T` applied to `canonicalDesc`,
conjugated by the identifications of both derived functors with homology of the chosen injective
resolutions. -/
theorem objIso_hom_chosen (n : ℕ) :
    (objIso G T hacyc hA n).hom =
      ((injectiveResolution A).isoRightDerivedObj (G ⋙ T) n).hom ≫
        HomologicalComplex.homologyMap
          ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map (canonicalDesc G hA)) n ≫
        ((injectiveResolution (G.obj A)).isoRightDerivedObj T n).inv :=
  rfl

/-! ### Independence of every choice -/

/-- Two augmentation-preserving comparisons `φ`, `φ'` of `G` applied to injective resolutions of
`A` and `B` with injective resolutions of `G A` and `G B` are compatible with the maps induced by
`g : A ⟶ B` on the derived functors, when `G` applied to `I` is a quasi-isomorphic resolution. -/
private theorem rightDerived_map_comp_comparison
    {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
    (G : C ⥤ D) [G.Additive] (T : D ⥤ E) [T.Additive] {A B : C} (g : A ⟶ B)
    (I : InjectiveResolution A) (hι : QuasiIso (mapι G I)) (I' : InjectiveResolution B)
    (J : InjectiveResolution (G.obj A)) (J' : InjectiveResolution (G.obj B))
    (φ : mapCocomplex G I ⟶ J.cocomplex) (φ' : mapCocomplex G I' ⟶ J'.cocomplex)
    (hφ : G.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) (hφ' : G.map (I'.ι.f 0) ≫ φ'.f 0 = J'.ι.f 0)
    (n : ℕ) :
    ((G ⋙ T).rightDerived n).map g ≫ (I'.isoRightDerivedObj (G ⋙ T) n).hom ≫
        HomologicalComplex.homologyMap
          ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ') n ≫
        (J'.isoRightDerivedObj T n).inv =
      (I.isoRightDerivedObj (G ⋙ T) n).hom ≫
        HomologicalComplex.homologyMap
          ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
        (J.isoRightDerivedObj T n).inv ≫ (T.rightDerived n).map (G.map g) := by
  set ψ := InjectiveResolution.desc g I' I
  set χ := InjectiveResolution.desc (G.map g) J' J
  set Gψ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ
  have hψ₀ : I.ι.f 0 ≫ ψ.f 0 = g ≫ I'.ι.f 0 := InjectiveResolution.desc_commutes_zero g I' I
  have hχ₀ : J.ι.f 0 ≫ χ.f 0 = G.map g ≫ J'.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero (G.map g) J' J
  -- the augmentation identities, all in term mode: a `rw` with `mapι_f_zero` leaves a target
  -- that is not type-correct at `implicit` transparency and blocks every later rewrite.
  have h1 : G.map (I.ι.f 0) ≫ Gψ.f 0 = G.map g ≫ G.map (I'.ι.f 0) :=
    (G.map_comp _ _).symm.trans ((congrArg G.map hψ₀).trans (G.map_comp _ _))
  have h2 : (mapι G I).f 0 ≫ Gψ.f 0 = G.map g ≫ (mapι G I').f 0 :=
    (congrArg (· ≫ Gψ.f 0) (mapι_f_zero G I)).trans
      (h1.trans (congrArg (G.map g ≫ ·) (mapι_f_zero G I').symm))
  have hL : (mapι G I).f 0 ≫ (φ ≫ χ).f 0 = G.map g ≫ J'.ι.f 0 :=
    (congrArg ((mapι G I).f 0 ≫ ·) (HomologicalComplex.comp_f φ χ 0)).trans
      ((assoc _ _ _).symm.trans
        ((congrArg (· ≫ χ.f 0) (mapι_f_zero_comp G I J φ hφ)).trans hχ₀))
  have hR : (mapι G I).f 0 ≫ (Gψ ≫ φ').f 0 = G.map g ≫ J'.ι.f 0 :=
    (congrArg ((mapι G I).f 0 ≫ ·) (HomologicalComplex.comp_f Gψ φ' 0)).trans
      ((assoc _ _ _).symm.trans ((congrArg (· ≫ φ'.f 0) h2).trans
        ((assoc _ _ _).trans
          (congrArg (G.map g ≫ ·) (mapι_f_zero_comp G I' J' φ' hφ')))))
  have hhom := Stacks.ResolutionDesc.homologyMap_map_eq (mapι G I) J' T
    (φ ≫ χ) (Gψ ≫ φ') (hL.trans hR.symm) n
  have hmid : HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
      HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map χ) n =
      HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map Gψ) n ≫
      HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ') n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp, hhom]
  have nat₁ := InjectiveResolution.isoRightDerivedObj_hom_naturality g I I' ψ hψ₀ (G ⋙ T) n
  have nat₂ := InjectiveResolution.isoRightDerivedObj_inv_naturality (G.map g) J J' χ hχ₀ T n
  set a := (I.isoRightDerivedObj (G ⋙ T) n).hom
  set b := HomologicalComplex.homologyMap
    ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map Gψ) n
  set p := HomologicalComplex.homologyMap
    ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n
  set p' := HomologicalComplex.homologyMap
    ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ') n
  set q := HomologicalComplex.homologyMap
    ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map χ) n
  set a' := (I'.isoRightDerivedObj (G ⋙ T) n).hom
  set d := (J.isoRightDerivedObj T n).inv
  set d' := (J'.isoRightDerivedObj T n).inv
  calc ((G ⋙ T).rightDerived n).map g ≫ a' ≫ p' ≫ d'
      = (((G ⋙ T).rightDerived n).map g ≫ a') ≫ p' ≫ d' := (assoc _ _ _).symm
    _ = (a ≫ b) ≫ p' ≫ d' := congrArg (· ≫ p' ≫ d') nat₁
    _ = a ≫ b ≫ p' ≫ d' := assoc _ _ _
    _ = a ≫ (b ≫ p') ≫ d' := congrArg (a ≫ ·) (assoc b p' d').symm
    _ = a ≫ (p ≫ q) ≫ d' := congrArg (fun x => a ≫ x ≫ d') hmid.symm
    _ = a ≫ p ≫ q ≫ d' := congrArg (a ≫ ·) (assoc p q d')
    _ = a ≫ p ≫ d ≫ (T.rightDerived n).map (G.map g) :=
        congrArg (fun x => a ≫ p ≫ x) nat₂.symm

include hacyc hA in
/-- **The collapse isomorphism is computed by any augmentation-preserving comparison of any
injective resolution of `A` with any injective resolution of `G A`.** -/
theorem objIso_hom_eq (n : ℕ) (I : InjectiveResolution A) (J : InjectiveResolution (G.obj A))
    (φ : mapCocomplex G I ⟶ J.cocomplex)
    (hφ : G.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (objIso G T hacyc hA n).hom =
      (I.isoRightDerivedObj (G ⋙ T) n).hom ≫
        HomologicalComplex.homologyMap
          ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
        (J.isoRightDerivedObj T n).inv := by
  have h := rightDerived_map_comp_comparison G T (𝟙 A) I (quasiIso_mapι G I hA)
    (injectiveResolution A) J (injectiveResolution (G.obj A)) φ (canonicalDesc G hA) hφ
    (canonicalDesc_comm G hA) n
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
  erw [Category.comp_id] at h
  exact (objIso_hom_chosen G T hacyc hA n).trans h

/-! ### The degree-zero normalization -/

include hacyc hA in
/-- **In degree zero the collapse isomorphism intertwines the canonical map from `G ⋙ T` to its
zeroth right derived functor with the canonical map from `T` to its own.** -/
theorem toRightDerivedZero_comp_objIso_hom :
    (G ⋙ T).toRightDerivedZero.app A ≫ (objIso G T hacyc hA 0).hom =
      T.toRightDerivedZero.app (G.obj A) := by
  set I₀ := injectiveResolution A with hI₀def
  set J₀ := injectiveResolution (G.obj A) with hJ₀def
  set φ₀ := canonicalDesc G hA with hφ₀def
  set Tφ₀ := (T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ₀ with hTφ₀def
  set z₁ := I₀.toRightDerivedZero' (G ⋙ T) with hz₁def
  set z₂ := J₀.toRightDerivedZero' T with hz₂def
  set π₁ := (CochainComplex.isoHomologyπ₀ ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (mapCocomplex G I₀))).hom with hπ₁def
  set π₂ := (CochainComplex.isoHomologyπ₀ ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    J₀.cocomplex)).hom with hπ₂def
  set c := HomologicalComplex.homologyMap Tφ₀ 0 with hcdef
  set d := (J₀.isoRightDerivedObj T 0).inv with hddef
  have e1 : z₁ ≫ ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (mapCocomplex G I₀)).iCycles 0 = T.map (G.map (I₀.ι.f 0)) :=
    I₀.toRightDerivedZero'_comp_iCycles (G ⋙ T)
  have e2 : z₂ ≫ ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      J₀.cocomplex).iCycles 0 = T.map (J₀.ι.f 0) :=
    J₀.toRightDerivedZero'_comp_iCycles T
  have e3 : Tφ₀.f 0 = T.map (φ₀.f 0) := rfl
  have hcyc : z₁ ≫ HomologicalComplex.cyclesMap Tφ₀ 0 = z₂ := by
    refine (cancel_mono (((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      J₀.cocomplex).iCycles 0)).1 ?_
    exact ((assoc _ _ _).trans ((congrArg (z₁ ≫ ·)
        (HomologicalComplex.cyclesMap_i Tφ₀ 0)).trans
      ((assoc _ _ _).symm.trans ((congrArg (· ≫ Tφ₀.f 0) e1).trans
        ((congrArg (T.map (G.map (I₀.ι.f 0)) ≫ ·) e3).trans
          ((T.map_comp _ _).symm.trans
            (congrArg T.map (canonicalDesc_comm G hA)))))))).trans e2.symm
  have hπ : z₁ ≫ π₁ ≫ c = z₂ ≫ π₂ := by
    rw [← hcyc, assoc, hπ₁def, hπ₂def, HomologicalComplex.isoHomologyπ_hom,
      HomologicalComplex.isoHomologyπ_hom, hcdef, HomologicalComplex.homologyπ_naturality]
  have eqU : (G ⋙ T).toRightDerivedZero.app A = z₁ ≫ π₁ ≫
      (I₀.isoRightDerivedObj (G ⋙ T) 0).inv := I₀.toRightDerivedZero_eq (G ⋙ T)
  have eqV : T.toRightDerivedZero.app (G.obj A) = z₂ ≫ π₂ ≫ d :=
    J₀.toRightDerivedZero_eq T
  calc (G ⋙ T).toRightDerivedZero.app A ≫ (objIso G T hacyc hA 0).hom
      = (z₁ ≫ π₁ ≫ (I₀.isoRightDerivedObj (G ⋙ T) 0).inv) ≫
          (objIso G T hacyc hA 0).hom := congrArg (· ≫ (objIso G T hacyc hA 0).hom) eqU
    _ = (z₁ ≫ π₁ ≫ (I₀.isoRightDerivedObj (G ⋙ T) 0).inv) ≫
          ((I₀.isoRightDerivedObj (G ⋙ T) 0).hom ≫ c ≫ d) :=
        congrArg ((z₁ ≫ π₁ ≫ (I₀.isoRightDerivedObj (G ⋙ T) 0).inv) ≫ ·)
          (objIso_hom_chosen G T hacyc hA 0)
    _ = z₁ ≫ (π₁ ≫ (I₀.isoRightDerivedObj (G ⋙ T) 0).inv) ≫
          ((I₀.isoRightDerivedObj (G ⋙ T) 0).hom ≫ c ≫ d) := assoc _ _ _
    _ = z₁ ≫ π₁ ≫ ((I₀.isoRightDerivedObj (G ⋙ T) 0).inv ≫
          ((I₀.isoRightDerivedObj (G ⋙ T) 0).hom ≫ c ≫ d)) :=
        congrArg (z₁ ≫ ·) (assoc _ _ _)
    _ = z₁ ≫ π₁ ≫ c ≫ d :=
        congrArg (fun x => z₁ ≫ π₁ ≫ x) (Iso.inv_hom_id_assoc _ _)
    _ = (z₁ ≫ π₁ ≫ c) ≫ d :=
        ((assoc z₁ (π₁ ≫ c) d).trans (congrArg (z₁ ≫ ·) (assoc π₁ c d))).symm
    _ = (z₂ ≫ π₂) ≫ d := congrArg (· ≫ d) hπ
    _ = z₂ ≫ π₂ ≫ d := assoc _ _ _
    _ = T.toRightDerivedZero.app (G.obj A) := eqV.symm

/-! ### Naturality -/

include hacyc in
/-- **The collapse isomorphism is natural in the `G`-acyclic object.** -/
theorem objIso_hom_naturality {A B : C}
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hB : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj B)) (g : A ⟶ B) (n : ℕ) :
    ((G ⋙ T).rightDerived n).map g ≫ (objIso G T hacyc hB n).hom =
      (objIso G T hacyc hA n).hom ≫ (T.rightDerived n).map (G.map g) := by
  rw [objIso_hom_chosen G T hacyc hB n, objIso_hom_chosen G T hacyc hA n, assoc,
    rightDerived_map_comp_comparison G T g _ (quasiIso_mapι G _ hA) _ _ _ _ _
      (canonicalDesc_comm G hA) (canonicalDesc_comm G hB) n]
  exact congrArg (_ ≫ ·) (assoc _ _ _).symm

/-! ### The natural isomorphism over a class of acyclic objects -/

include hacyc in
/-- **The collapse isomorphism as a natural isomorphism**, on the full subcategory cut out by
any class `P` of `G`-acyclic objects. -/
noncomputable def natIso (P : ObjectProperty C)
    (hP : ∀ X : C, P X → ∀ n, 0 < n → IsZero ((G.rightDerived n).obj X)) (n : ℕ) :
    P.ι ⋙ (G ⋙ T).rightDerived n ≅ P.ι ⋙ G ⋙ T.rightDerived n :=
  NatIso.ofComponents (fun X => objIso G T hacyc (hP X.obj X.property) n)
    fun {X Y} g => objIso_hom_naturality G T hacyc (hP X.obj X.property)
      (hP Y.obj Y.property) g.hom n

include hacyc in
/-- The component of `natIso` at `X` is the collapse isomorphism `objIso` at `X`. -/
@[simp]
theorem natIso_hom_app (P : ObjectProperty C)
    (hP : ∀ X : C, P X → ∀ n, 0 < n → IsZero ((G.rightDerived n).obj X)) (n : ℕ)
    (X : P.FullSubcategory) :
    (natIso G T hacyc P hP n).hom.app X = (objIso G T hacyc (hP X.obj X.property) n).hom :=
  rfl

end Stacks.AcyclicCollapse

end
