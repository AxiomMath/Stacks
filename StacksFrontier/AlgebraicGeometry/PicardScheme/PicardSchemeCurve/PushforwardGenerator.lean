module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Generating sections of a module whose derived pushforward is the structure sheaf

Let `p : Y ⟶ S` be a morphism of schemes and `ℒ` an `𝒪_Y`-module. A morphism `s : 𝒪_Y ⟶ ℒ`
has a *derived adjoint* `𝒪_S[0] ⟶ Rp_*(ℒ[0])`, its transpose under `Lp^* ⊣ Rp_*` after the
identification `Lp^*(𝒪_S[0]) ≅ 𝒪_Y[0]`. We call `s` a *generator* when its derived adjoint is
an isomorphism. This is the section `s` of the proof of [Stacks, Tag 0B9X] in the case where the
invertible module `𝒩` with `Rf_{T,*}ℒ ≅ 𝒩[0]` is trivial: the adjunction map `f_T^*𝒩 ⟶ ℒ`.

## Main definitions

* `AlgebraicGeometry.PushforwardGenerator.derivedAdjoint`: the derived adjoint of `s : 𝒪_Y ⟶ ℒ`.
* `AlgebraicGeometry.PushforwardGenerator.IsGenerator`: the derived adjoint is invertible.
* `AlgebraicGeometry.PushforwardGenerator.pullbackEnd`: an endomorphism of `𝒪_S` pulled back to
  an endomorphism of `𝒪_Y`.

## Main results

* `AlgebraicGeometry.PushforwardGenerator.exists_isGenerator`: when `Rp_*(ℒ[0]) ≅ 𝒪_S[0]` there
  is a generator.
* `AlgebraicGeometry.PushforwardGenerator.exists_eq_pullbackEnd_comp`: every `t : 𝒪_Y ⟶ ℒ` is
  `p^*a ≫ s` for an endomorphism `a` of `𝒪_S`, an automorphism when `t` is a generator too.
* `AlgebraicGeometry.PushforwardGenerator.map_ne_zero_of_isGenerator`: if the derived base change
  map of a cartesian square at `ℒ[0]` is invertible ([Stacks, Tag 0B91]) and the new base is
  nonempty, the pullback of a generator is nonzero. This is the input "the section is nonzero on
  every fibre" of the proof of [Stacks, Tag 0B9X].

## Implementation notes

Everything is read in the derived category through the fully faithful functor `(-)[0]`: no
comparison of `f_*` with `R⁰f_*` is needed, and the base change argument is the defining mate
identity of the derived base change map (`derivedBaseChangeMap_adjoint`) together with the
naturality of the comparison `Lf^*(ℱ[0]) ≅ (f^*ℱ)[0]` for flat `ℱ`
(`Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso_hom_naturality`).

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Cohomology.FlatSingleDerivedPullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The comparison morphism `Lf^*(ℱ[0]) ⟶ (f^*ℱ)[0]`, the forward map of
`derivedPullbackSingleIso`. -/
def derivedPullbackSingleHom (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F) ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
        ((modulePullback f).obj F) :=
  (derivedPullback f).map ((DerivedCategory.singleFunctorIsoCompQh
      (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app F) ≫
    (derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F) ≫
    DerivedCategory.Qh.map (((modulePullback f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom.app ((HomologicalComplex.single
        (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ) 0).obj F)) ≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom.app _ ≫
    DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback f) (ComplexShape.up ℤ) 0).hom.app F) ≫
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X)) 0).inv.app
      ((modulePullback f).obj F)

/-- For flat `ℱ`, the forward map of `derivedPullbackSingleIso` is `derivedPullbackSingleHom`. -/
theorem derivedPullbackSingleIso_hom (F : SheafOfModules.{u} (structureSheafRing Y))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F) :
    (derivedPullbackSingleIso f F hF).hom = derivedPullbackSingleHom f F :=
  rfl

/-- The natural transformation `(-)[0] ⋙ Lf^* ⟶ f^* ⋙ (-)[0]` whose components are the
morphisms `derivedPullbackSingleHom`. -/
def derivedPullbackSingleNatTrans :
    DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0 ⋙
        derivedPullback f ⟶
      modulePullback f ⋙
        DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0 :=
  Functor.whiskerRight (DerivedCategory.singleFunctorIsoCompQh
      (SheafOfModules.{u} (structureSheafRing Y)) 0).hom (derivedPullback f) ≫
    (Functor.whiskerLeft (HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing Y)) 0) (derivedPullbackComparison f) :
        HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0 ⋙
          DerivedCategory.Qh ⋙ derivedPullback f ⟶ _) ≫
    (Functor.whiskerLeft (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ) 0)
      (Functor.whiskerRight ((modulePullback f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom DerivedCategory.Qh) :
      HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ) 0 ⋙
        (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ) ⋙
          (modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙ DerivedCategory.Qh ⟶ _) ≫
    (Functor.whiskerLeft (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ) 0 ⋙ (modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom :
      (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ) 0 ⋙
        (modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
              (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh) ⟶ _) ≫
    Functor.whiskerRight (HomologicalComplex.singleMapHomologicalComplex (modulePullback f)
      (ComplexShape.up ℤ) 0).hom DerivedCategory.Q ≫
    (Functor.whiskerLeft (modulePullback f) (DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (structureSheafRing X)) 0).inv :
      (modulePullback f ⋙ HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ) 0) ⋙ DerivedCategory.Q ⟶ _)

/-- The component of `derivedPullbackSingleNatTrans` at `ℱ` is `derivedPullbackSingleHom f ℱ`. -/
theorem derivedPullbackSingleNatTrans_app (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (derivedPullbackSingleNatTrans f).app F = derivedPullbackSingleHom f F :=
  rfl

/-- The morphisms `Lf^*(ℱ[0]) ⟶ (f^*ℱ)[0]` are natural in the module `ℱ`. -/
theorem derivedPullbackSingleHom_naturality
    {F G : SheafOfModules.{u} (structureSheafRing Y)} (φ : F ⟶ G) :
    (derivedPullback f).map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map φ) ≫
        derivedPullbackSingleHom f G =
      derivedPullbackSingleHom f F ≫
        (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map
          ((modulePullback f).map φ) :=
  (derivedPullbackSingleNatTrans f).naturality φ

/-- **The comparison `Lf^*(ℱ[0]) ≅ (f^*ℱ)[0]` is natural** in the flat module `ℱ`. -/
theorem derivedPullbackSingleIso_hom_naturality
    {F G : SheafOfModules.{u} (structureSheafRing Y)}
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F)
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) G) (φ : F ⟶ G) :
    (derivedPullback f).map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map φ) ≫
        (derivedPullbackSingleIso f G hG).hom =
      (derivedPullbackSingleIso f F hF).hom ≫
        (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map
          ((modulePullback f).map φ) := by
  rw [derivedPullbackSingleIso_hom, derivedPullbackSingleIso_hom,
    derivedPullbackSingleHom_naturality]

end Stacks.Cohomology.FlatSingleDerivedPullback

namespace AlgebraicGeometry.PushforwardGenerator

open Stacks.Cohomology.FlatSingleDerivedPullback Stacks.Cohomology.DerivedPullbackUnit
open Stacks.Cohomology.DerivedBaseChange Stacks.DerivedPullback.Composition

variable {Y S : RingedSpace.{u, u}} (p : Y ⟶ S) (L : SheafOfModules.{u} (structureSheafRing Y))

/-- A module whose image under `(-)[0]` is zero is zero. -/
theorem isZero_of_isZero_singleFunctor_obj {X : RingedSpace.{u, u}}
    {M : SheafOfModules.{u} (structureSheafRing X)}
    (h : IsZero
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) :
    IsZero M := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  apply (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map_injective
  exact ((DerivedCategory.singleFunctor _ 0).map_id _).trans ((h.eq_of_src _ _).trans
    ((DerivedCategory.singleFunctor _ 0).map_zero _ _).symm)

/-- **The derived adjoint `𝒪_S[0] ⟶ Rp_*(ℒ[0])` of a morphism `s : 𝒪_Y ⟶ ℒ`**: the transpose
under `Lp^* ⊣ Rp_*` of `s[0]`, precomposed with `Lp^*(𝒪_S[0]) ≅ 𝒪_Y[0]`. -/
def derivedAdjoint (s : (SheafOfModules.unit (structureSheafRing Y)) ⟶ L) :
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).obj
        (SheafOfModules.unit (structureSheafRing S)) ⟶
      (derivedPushforward p).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L) :=
  (derivedAdjunction p).homEquiv _ _ ((derivedPullbackUnitIso p).hom ≫
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map s)

/-- **A generator** of `ℒ` relative to `p`: a morphism `𝒪_Y ⟶ ℒ` whose derived adjoint
`𝒪_S[0] ⟶ Rp_*(ℒ[0])` is an isomorphism. -/
def IsGenerator (s : (SheafOfModules.unit (structureSheafRing Y)) ⟶ L) : Prop :=
  IsIso (derivedAdjoint p L s)

/-- The derived adjoint `derivedAdjoint p L` is injective on morphisms `𝒪_Y ⟶ ℒ`. -/
theorem derivedAdjoint_injective : Function.Injective (derivedAdjoint p L) := fun _ _ h =>
  (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map_injective
    ((Iso.cancel_iso_hom_left _ _ _).1 (((derivedAdjunction p).homEquiv _ _).injective h))

/-- **A generator exists when `Rp_*(ℒ[0]) ≅ 𝒪_S[0]`.** -/
theorem exists_isGenerator
    (h : Nonempty
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).obj
          (SheafOfModules.unit (structureSheafRing S)) ≅
        (derivedPushforward p).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L))) :
    ∃ s, IsGenerator p L s := by
  obtain ⟨φ⟩ := h
  let ψ : (derivedPullback p).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).obj
        (SheafOfModules.unit (structureSheafRing S))) ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L :=
    ((derivedAdjunction p).homEquiv _ _).symm φ.hom
  refine ⟨(DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).preimage
    ((derivedPullbackUnitIso p).inv ≫ ψ), ?_⟩
  unfold IsGenerator
  rw [derivedAdjoint, Functor.map_preimage, Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  infer_instance

/-- **The pullback `p^*a` of an endomorphism `a` of `𝒪_S`**, read as an endomorphism of `𝒪_Y`
through `p^*𝒪_S ≅ 𝒪_Y`. -/
def pullbackEnd (a : (SheafOfModules.unit (structureSheafRing S)) ⟶
      (SheafOfModules.unit (structureSheafRing S))) :
    (SheafOfModules.unit (structureSheafRing Y)) ⟶ (SheafOfModules.unit (structureSheafRing Y)) :=
  (modulePullbackObjUnitIso p).inv ≫ (modulePullback p).map a ≫ (modulePullbackObjUnitIso p).hom

/-- The pullback `p^*a` of an automorphism `a` of `𝒪_S` is an automorphism of `𝒪_Y`. -/
instance (a : (SheafOfModules.unit (structureSheafRing S)) ⟶
    (SheafOfModules.unit (structureSheafRing S))) [IsIso a] : IsIso (pullbackEnd p a) := by
  unfold pullbackEnd
  infer_instance

/-- The unit comparison `Lp^*(𝒪_S[0]) ≅ 𝒪_Y[0]` intertwines `Lp^*(a[0])` with `(p^*a)[0]`. -/
theorem derivedPullback_map_single_comp_unitIso
    (a : (SheafOfModules.unit (structureSheafRing S)) ⟶
      (SheafOfModules.unit (structureSheafRing S))) :
    (derivedPullback p).map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).map a) ≫
        (derivedPullbackUnitIso p).hom =
      (derivedPullbackUnitIso p).hom ≫
        (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
          (pullbackEnd p a) := by
  rw [derivedPullbackUnitIso_hom, reassoc_of% (derivedPullbackSingleIso_hom_naturality
    p (isFlat_unit S) (isFlat_unit S) a)]
  simp only [pullbackEnd, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_assoc]

/-- The derived adjoint of `p^*a ≫ s` is `a[0]` followed by the derived adjoint of `s`. -/
theorem derivedAdjoint_pullbackEnd_comp
    (a : (SheafOfModules.unit (structureSheafRing S)) ⟶
      (SheafOfModules.unit (structureSheafRing S)))
    (s : (SheafOfModules.unit (structureSheafRing Y)) ⟶ L) :
    derivedAdjoint p L (pullbackEnd p a ≫ s) =
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).map a ≫
        derivedAdjoint p L s := by
  rw [derivedAdjoint, derivedAdjoint, ← Adjunction.homEquiv_naturality_left, Functor.map_comp,
    reassoc_of% derivedPullback_map_single_comp_unitIso]

/-- **Every morphism `t : 𝒪_Y ⟶ ℒ` factors through a generator `s`** as `p^*a ≫ s`; when `t` is a
generator too, `a` is an automorphism of `𝒪_S`. -/
theorem exists_eq_pullbackEnd_comp (s t : (SheafOfModules.unit (structureSheafRing Y)) ⟶ L)
    (hs : IsGenerator p L s) :
    ∃ a : (SheafOfModules.unit (structureSheafRing S)) ⟶
        (SheafOfModules.unit (structureSheafRing S)),
      t = pullbackEnd p a ≫ s ∧ (IsGenerator p L t → IsIso a) := by
  have : IsIso (derivedAdjoint p L s) := hs
  refine ⟨(DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).preimage
    (derivedAdjoint p L t ≫ inv (derivedAdjoint p L s)), ?_, fun ht => ?_⟩
  · refine derivedAdjoint_injective p L ?_
    rw [derivedAdjoint_pullbackEnd_comp, Functor.map_preimage, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  · have : IsIso (derivedAdjoint p L t) := ht
    have : IsIso ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).preimage
          (derivedAdjoint p L t ≫ inv (derivedAdjoint p L s)))) := by
      rw [Functor.map_preimage]
      infer_instance
    exact isIso_of_fully_faithful
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0) _

/-- **The transpose of a derived adjoint after base change.** For a commutative square
`g' ≫ p = p' ≫ g` and any `s : 𝒪_Y ⟶ ℒ`, the transpose under `Lp'^* ⊣ Rp'_*` of the derived
pullback along `g` of the derived adjoint of `s`, followed by the derived base change map at
`ℒ[0]`, is `Lg'^*(s[0])` up to the comparison of the two iterated derived pullbacks and
`Lp^*(𝒪_S[0]) ≅ 𝒪_Y[0]`. -/
theorem homEquiv_symm_derivedPullback_map_derivedAdjoint_comp {Y' S' : RingedSpace.{u, u}}
    (g' : Y' ⟶ Y) (p' : Y' ⟶ S') (g : S' ⟶ S) (sq : g' ≫ p = p' ≫ g)
    (s : SheafOfModules.unit (structureSheafRing Y) ⟶ L) :
    ((derivedAdjunction p').homEquiv _ _).symm
        ((derivedPullback g).map (derivedAdjoint p L s) ≫ derivedBaseChangeMap g' p' p g sq
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L)) =
      ((derivedPullbackCompIsoLeft g' p' p g sq).hom ≫
          (derivedPullbackCompIsoCanonical g' p).inv).app
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).obj
          (SheafOfModules.unit (structureSheafRing S))) ≫
        (derivedPullback g').map ((derivedPullbackUnitIso p).hom ≫
          (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map s) := by
  have hcounit : (derivedPullback p).map (derivedAdjoint p L s) ≫
      (derivedAdjunction p).counit.app
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L) =
      (derivedPullbackUnitIso p).hom ≫
        (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map s :=
    ((derivedAdjunction p).homEquiv_counit _ _ (derivedAdjoint p L s)).symm.trans
      (Equiv.symm_apply_apply _ _)
  rw [Adjunction.homEquiv_naturality_left_symm, derivedBaseChangeMap_adjoint]
  have nat := ((derivedPullbackCompIsoLeft g' p' p g sq).hom ≫
    (derivedPullbackCompIsoCanonical g' p).inv).naturality (derivedAdjoint p L s)
  calc _ = ((derivedPullback g ⋙ derivedPullback p').map (derivedAdjoint p L s) ≫
        ((derivedPullbackCompIsoLeft g' p' p g sq).hom ≫
          (derivedPullbackCompIsoCanonical g' p).inv).app _) ≫
        (derivedPullback g').map ((derivedAdjunction p).counit.app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj
            L)) := by
        simp only [NatTrans.comp_app, Category.assoc]
        rfl
    _ = (((derivedPullbackCompIsoLeft g' p' p g sq).hom ≫
          (derivedPullbackCompIsoCanonical g' p).inv).app _ ≫
        (derivedPullback p ⋙ derivedPullback g').map (derivedAdjoint p L s)) ≫
        (derivedPullback g').map ((derivedAdjunction p).counit.app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L)) :=
        congrArg (fun x => x ≫ (derivedPullback g').map ((derivedAdjunction p).counit.app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L)))
          nat
    _ = _ := (Category.assoc _ _ _).trans (congrArg (fun x => _ ≫ x)
        (((derivedPullback g').map_comp _ _).symm.trans
          (congrArg (derivedPullback g').map hcounit)))

/-- A morphism vanishes iff its transpose under `Lp'^* ⊣ Rp'_*` does. -/
private theorem derivedAdjunction_homEquiv_symm_eq_zero_iff {Y' S' : RingedSpace.{u, u}}
    (p' : Y' ⟶ S') {A : DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
    {B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'))}
    (f : A ⟶ (derivedPushforward p').obj B) :
    ((derivedAdjunction p').homEquiv _ _).symm f = 0 ↔ f = 0 := by
  have : (derivedPullback p').IsLeftAdjoint := ⟨_, ⟨derivedAdjunction p'⟩⟩
  have h0 : ((derivedAdjunction p').homEquiv A B).symm 0 = 0 :=
    ((derivedAdjunction p').homEquiv_counit _ _ 0).trans
      ((congrArg (fun x => x ≫ _) (Functor.map_zero _ _ _)).trans zero_comp)
  exact ⟨fun h => ((derivedAdjunction p').homEquiv _ _).symm.injective (h.trans h0.symm),
    fun h => by rw [h]; exact h0⟩

/-- **A morphism whose pullback vanishes has vanishing derived adjoint after base change**, when
the derived base change map of the square at `ℒ[0]` is invertible and `ℒ` is flat: if
`g'^*s = 0` then `Lg^*` of the derived adjoint of `s` is zero. -/
theorem derivedPullback_map_derivedAdjoint_eq_zero {Y' S' : RingedSpace.{u, u}} (g' : Y' ⟶ Y)
    (p' : Y' ⟶ S') (g : S' ⟶ S) (sq : g' ≫ p = p' ≫ g)
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) L)
    (hbc : IsIso (derivedBaseChangeMap g' p' p g sq
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L)))
    (s : SheafOfModules.unit (structureSheafRing Y) ⟶ L) (h0 : (modulePullback g').map s = 0) :
    (derivedPullback g).map (derivedAdjoint p L s) = 0 := by
  have hz : (derivedPullback g').map
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map s) =
        0 := by
    have hn := derivedPullbackSingleIso_hom_naturality g' (isFlat_unit Y) hL s
    rw [h0, Functor.map_zero, comp_zero] at hn
    exact (cancel_mono (derivedPullbackSingleIso g' L hL).hom).1 (hn.trans zero_comp.symm)
  have hkey : ((derivedAdjunction p').homEquiv _ _).symm
      ((derivedPullback g).map (derivedAdjoint p L s) ≫ derivedBaseChangeMap g' p' p g sq
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L)) =
        0 := by
    refine (homEquiv_symm_derivedPullback_map_derivedAdjoint_comp p L g' p' g sq s).trans ?_
    exact (congrArg (fun x => _ ≫ x) (((derivedPullback g').map_comp _ _).trans
      ((congrArg (fun x => _ ≫ x) hz).trans comp_zero))).trans comp_zero
  have h2 : (derivedPullback g).map (derivedAdjoint p L s) ≫ derivedBaseChangeMap g' p' p g sq
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L) =
        0 := by
    exact (derivedAdjunction_homEquiv_symm_eq_zero_iff p' _).1 hkey
  exact (cancel_mono (derivedBaseChangeMap g' p' p g sq _)).1 (h2.trans zero_comp.symm)

/-- **The derived adjoint of an isomorphism stays nonzero after any base change** whose top
corner `Y'` has a nonzero structure sheaf: for an isomorphism `s : 𝒪_Y ⟶ ℒ`, `Lg^*` of the
derived adjoint of `s` is nonzero. -/
theorem derivedPullback_map_derivedAdjoint_ne_zero {Y' S' : RingedSpace.{u, u}} (g' : Y' ⟶ Y)
    (p' : Y' ⟶ S') (g : S' ⟶ S) (sq : g' ≫ p = p' ≫ g)
    (s : SheafOfModules.unit (structureSheafRing Y) ⟶ L) [IsIso s]
    (hne : ¬ IsZero (SheafOfModules.unit (structureSheafRing Y'))) :
    (derivedPullback g).map (derivedAdjoint p L s) ≠ 0 := by
  intro h0
  have hkey := homEquiv_symm_derivedPullback_map_derivedAdjoint_comp p L g' p' g sq s
  have hzero := (derivedAdjunction_homEquiv_symm_eq_zero_iff p'
    ((derivedPullback g).map (derivedAdjoint p L s) ≫ derivedBaseChangeMap g' p' p g sq
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L))).2
    (by rw [h0, zero_comp])
  let e := (((derivedPullbackCompIsoLeft g' p' p g sq) ≪≫
      (derivedPullbackCompIsoCanonical g' p).symm).app
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).obj
          (SheafOfModules.unit (structureSheafRing S)))) ≪≫
      (derivedPullback g').mapIso ((derivedPullbackUnitIso p) ≪≫
        (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).mapIso
          (asIso s))
  have he : e.hom = 0 := by
    refine Eq.trans ?_ (hkey.symm.trans hzero)
    simp only [e, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom,
      NatTrans.comp_app]
  have hz1 : IsZero ((derivedPullback p').obj ((derivedPullback g).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).obj
        (SheafOfModules.unit (structureSheafRing S))))) :=
    IsZero.of_mono_eq_zero e.hom he
  exact hne (isZero_of_isZero_singleFunctor_obj (hz1.of_iso
    (((derivedPullback p').mapIso (derivedPullbackUnitIso g)) ≪≫ derivedPullbackUnitIso p').symm))

/-- **The pullback of a generator along the top edge of a square is nonzero**, as soon as the
derived base change map of the square at `ℒ[0]` is invertible ([Stacks, Tag 0B91] (1)) and the
new base `S'` has a nonzero structure sheaf: for flat `ℒ` and a generator `s`, the pullback
`g'^*s` is nonzero. -/
theorem map_ne_zero_of_isGenerator {Y' S' : RingedSpace.{u, u}} (g' : Y' ⟶ Y) (p' : Y' ⟶ S')
    (g : S' ⟶ S) (sq : g' ≫ p = p' ≫ g)
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) L)
    (hbc : IsIso (derivedBaseChangeMap g' p' p g sq
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L)))
    (hne : ¬ IsZero (SheafOfModules.unit (structureSheafRing S')))
    (s : SheafOfModules.unit (structureSheafRing Y) ⟶ L) (hs : IsGenerator p L s) :
    (modulePullback g').map s ≠ 0 := by
  intro h0
  have hA : IsIso (derivedAdjoint p L s) := hs
  have h2 : (derivedPullback g).map (derivedAdjoint p L s) ≫ derivedBaseChangeMap g' p' p g sq
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L) =
        0 := by
    rw [derivedPullback_map_derivedAdjoint_eq_zero p L g' p' g sq hL hbc s h0, zero_comp]
  have : IsIso ((derivedPullback g).map (derivedAdjoint p L s)) := Functor.map_isIso _ _
  have hz1 : IsZero ((derivedPullback g).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S)) 0).obj
        (SheafOfModules.unit (structureSheafRing S)))) := by
    exact IsZero.of_mono_eq_zero _ h2
  exact hne (isZero_of_isZero_singleFunctor_obj (hz1.of_iso (derivedPullbackUnitIso g).symm))

/-- **After base change, the derived pushforward of `ℒ` is still the structure sheaf**: if `ℒ`
has a generator relative to `p` and the derived base change map of a square at `ℒ[0]` is
invertible ([Stacks, Tag 0B91] (1)), then `Rp'_*((g'^*ℒ)[0]) ≅ 𝒪_{S'}[0]`. -/
theorem nonempty_derivedPushforward_pullback_iso {Y' S' : RingedSpace.{u, u}} (g' : Y' ⟶ Y)
    (p' : Y' ⟶ S') (g : S' ⟶ S) (sq : g' ≫ p = p' ≫ g)
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) L)
    (hbc : IsIso (derivedBaseChangeMap g' p' p g sq
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj L)))
    (s : SheafOfModules.unit (structureSheafRing Y) ⟶ L) (hs : IsGenerator p L s) :
    Nonempty ((derivedPushforward p').obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y')) 0).obj
          ((modulePullback g').obj L)) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S')) 0).obj
        (SheafOfModules.unit (structureSheafRing S'))) := by
  have hA : IsIso (derivedAdjoint p L s) := hs
  exact ⟨(derivedPushforward p').mapIso (derivedPullbackSingleIso g' L hL).symm ≪≫
    (@asIso _ _ _ _ _ hbc).symm ≪≫
    (derivedPullback g).mapIso (@asIso _ _ _ _ (derivedAdjoint p L s) hA).symm ≪≫
    derivedPullbackUnitIso g⟩

end AlgebraicGeometry.PushforwardGenerator

end
