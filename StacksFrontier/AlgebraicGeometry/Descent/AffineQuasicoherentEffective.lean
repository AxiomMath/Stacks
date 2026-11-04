module

public import StacksFrontier.AlgebraicGeometry.Descent.QcohCoalgebraTransfer
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonCoalgebraObj
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effectivity of descent data along one faithfully flat morphism of affine schemes

The effectivity half of [Stacks, Tag 023T] asserts, for an fpqc covering family, that every
descent datum on quasi-coherent sheaves is effective, i.e. isomorphic to the canonical descent
datum of a quasi-coherent sheaf on the base. This file proves it for a one-element family given by
a faithfully flat morphism `Spec φ` of affine schemes, using that pullback of quasi-coherent
modules along `Spec φ` is comonadic (`Stacks.Descent.comonadicPullbackQcoh`).

## Main definitions

* `Stacks.Descent.coalgebraPullbackQcoh`: a coalgebra over the comonad of
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` whose underlying module is
  quasi-coherent, as a coalgebra over the comonad of `Stacks.Descent.pullbackQcohAdjunction`, on
  the same structure morphism.
* `Stacks.Descent.affineTransition`: the transition morphism of a descent datum over the chosen
  pullback of `Spec φ` with itself that a pushout square of rings provides.
* `Stacks.Descent.IsTransposedCocycleAt` and `Stacks.Descent.IsTransposedCocycle`: the cocycle
  condition of a descent datum, transposed onto a chosen pullback, at variable data and at the
  chosen pullback of `Spec φ` provided by a pushout square of rings.

## Main results

* `Stacks.Descent.counit_pullbackQcohAdjunction_app_hom`: after forgetting quasi-coherence, the
  counit of the adjunction on quasi-coherent modules is the counit of the adjunction on all
  sheaves of modules.
* `Stacks.Descent.exists_iso_pullback_of_coalgebra`: for a faithfully flat `φ`, every
  quasi-coherent coalgebra for the comonad of `(Spec φ)^* ⊣ (Spec φ)_*` is isomorphic to the
  canonical one on `(Spec φ)^* M` for a quasi-coherent module `M` on `Spec R`.
* `Stacks.Descent.isTransposedCocycle_scheme` and `Stacks.Descent.isTransposedCocycle`: the
  transposed cocycle condition holds for a descent datum.
* `Stacks.Descent.exists_isTransposeOf_scheme` and `Stacks.Descent.exists_isTransposeOf_affine`:
  the component of a descent datum carries a structure morphism.
* `Stacks.Descent.counit_affine` and `Stacks.Descent.coassoc_affine`: the two Eilenberg–Moore
  axioms of that structure morphism.
* `Stacks.Descent.isEffective_of_isTransposedCocycle` and
  `Stacks.Descent.isEffective_of_isTransposeOf`: a one-element quasi-coherent descent datum along
  `Spec φ` with a structure morphism is effective.
* `Stacks.Descent.isEffective_of_faithfullyFlat_affine`: for `φ` faithfully flat with a pushout
  presentation of `φ` with itself, every one-element quasi-coherent descent datum along `Spec φ`
  is effective.

## Implementation notes

The two spellings of the inverse image, `AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)`
and `(AlgebraicGeometry.modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor`, are
definitionally equal, but at a concrete morphism the kernel does not finish converting between
them (inside an `IsIso`, or in identifying `AlgebraicGeometry.canonicalDescentFunctor` with
`CategoryTheory.Pseudofunctor.toDescentData`) within the heartbeat budget, while at a variable
morphism the conversion is free. Hence `Stacks.Descent.isEffective_of_descentDataIso`,
`Stacks.Descent.coassoc_of_descentDataCoassoc_scheme`, `Stacks.Descent.isTransposedCocycle_scheme`
and `Stacks.Descent.exists_isTransposeOf_scheme` are stated at variable data, with invertibility
hypotheses written with `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` rather
than `CategoryTheory.Pseudofunctor.descentBaseChange`, and `Stacks.Descent.IsTransposedCocycle`
is defined as a substitution instance of `Stacks.Descent.IsTransposedCocycleAt`; respelling any
of these makes the affine applications fail kernel checking.
`Stacks.Descent.exists_iso_pullback_of_coalgebra'` is the one declaration that crosses between
the two spellings.

In the coalgebra conditions the goal mixes two `Category` instances on the same sheaves of
modules, so `rw` and `simp` do not reduce it; a `change` into the underlying equation is used.

The name `Stacks.Descent.isEffective_of_faithfullyFlat` is taken by the effective descent of
modules along a faithfully flat ring map, hence the `_affine` suffix.

## References

* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe t u

namespace Stacks.Descent

open Stacks.AlgebraicGeometry.ModuleDescentBaseChange

/-- A quasi-coherent descent datum isomorphic to the canonical descent datum of a quasi-coherent
module on the base is effective. -/
theorem isEffective_of_descentDataIso {ι : Type t} {T : Scheme.{u}} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ T} (D : QuasicoherentDescentData f)
    (M : (SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory)
    (e : (modulePullbackPseudofunctor.toDescentData f).obj M.obj ≅ D.obj) : D.IsEffective :=
  ⟨M, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- `CategoryTheory.Pseudofunctor.coassoc_of_descentDataCoassoc` for the pullback pseudofunctor
of schemes, with the morphism and its chosen self-pullback as variables. -/
theorem coassoc_of_descentDataCoassoc_scheme {T Y : Scheme.{u}} {g : Y ⟶ T}
    (sq : ChosenPullback g g) {A : Y.Modules}
    {θ : (Scheme.Modules.pullback sq.p₁).obj A ⟶ (Scheme.Modules.pullback sq.p₂).obj A}
    {a : A ⟶ (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward g).obj A)}
    (ha : Pseudofunctor.IsTransposeOf (F := modulePullbackPseudofunctor) sq
      (Scheme.Modules.pullbackPushforwardAdjunction g) a θ)
    (hiso : IsIso ((Pseudofunctor.descentBaseChange (F := modulePullbackPseudofunctor) sq
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.pullbackPushforwardAdjunction sq.p₁)).app
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward g).obj A))))
    (hco : (Scheme.Modules.pullback sq.p₁).map a ≫
        Pseudofunctor.descentSquareApp (F := modulePullbackPseudofunctor) sq
          ((Scheme.Modules.pushforward g).obj A) =
      θ ≫ (Scheme.Modules.pullback sq.p₂).map a) :
    a ≫ (Scheme.Modules.pullback g).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pushforward g).obj A)) =
      a ≫ (Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward g).map a) :=
  Pseudofunctor.coassoc_of_descentDataCoassoc (F := modulePullbackPseudofunctor) sq
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction sq.p₁) ha rfl hiso hco

/-- For a morphism `g` of schemes with a chosen pullback `sq` of `g` with itself, a module `A` on
the source, a transition morphism `θ` of `A` over `sq` and a morphism `a : A ⟶ g^* g_* A`: the
inverse image of `a` along the first projection, followed by the canonical comparison of the two
pullbacks of `g_* A`, is `θ` followed by the inverse image of `a` along the second projection. -/
def IsTransposedCocycleAt {T Y : Scheme.{u}} {g : Y ⟶ T} (sq : ChosenPullback g g)
    {A : Y.Modules}
    (θ : (Scheme.Modules.pullback sq.p₁).obj A ⟶ (Scheme.Modules.pullback sq.p₂).obj A)
    (a : A ⟶ (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward g).obj A)) : Prop :=
  (Scheme.Modules.pullback sq.p₁).map a ≫
      Pseudofunctor.descentSquareApp (F := modulePullbackPseudofunctor) sq
        ((Scheme.Modules.pushforward g).obj A) =
    θ ≫ (Scheme.Modules.pullback sq.p₂).map a

/-- `Stacks.Descent.IsTransposedCocycleAt` holds for the transition morphism of a descent datum
for a one-element family `g`, given that `a` transposes to it and that the base-change morphisms
of the chosen pullback `sq` of `g` with itself and of the chosen pullback `sq'` of its first
projection with itself are invertible. -/
theorem isTransposedCocycle_scheme {T Y : Scheme.{u}} {g : Y ⟶ T} (sq : ChosenPullback g g)
    {k : sq.pullback ⟶ Y} (hk : k = sq.p₁) (sq' : ChosenPullback k k)
    {ι : Type t} [Unique ι] (D : modulePullbackPseudofunctor.DescentData (fun _ : ι ↦ g))
    {A : Y.Modules} (hA : A = D.obj default)
    {θ : (Scheme.Modules.pullback sq.p₁).obj A ⟶ (Scheme.Modules.pullback sq.p₂).obj A}
    {a : A ⟶ (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward g).obj A)}
    (ha : Pseudofunctor.IsTransposeOf (F := modulePullbackPseudofunctor) sq
      (Scheme.Modules.pullbackPushforwardAdjunction g) a θ)
    (hθ : HEq θ (D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂))
    (h₁ : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (sq.hp₂.trans sq.hp₁.symm)).app A))
    (h₂ : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (sq'.hp₂.trans sq'.hp₁.symm)).app ((Scheme.Modules.pullback sq.p₂).obj A))) :
    IsTransposedCocycleAt sq θ a := by
  rw [IsTransposedCocycleAt]
  subst hA
  subst hk
  obtain rfl := eq_of_heq hθ
  refine Pseudofunctor.descentDataCoassoc_of_isTransposeOf sq
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction sq.p₁) sq'
    (Scheme.Modules.pullbackPushforwardAdjunction sq'.p₁) D ?_ ?_ ?_
  · exact ha
  · rw [descentBaseChange_eq_baseChangeNatTrans]
    exact h₁
  · rw [descentBaseChange_eq_baseChangeNatTrans]
    exact h₂

/-- For a descent datum `D` for a one-element family `g` of schemes whose base-change morphism
over the chosen pullback `sq` is invertible on the component, there is a morphism
`a : A ⟶ g^* g_* A` on the component transposing to the transition morphism of `D` over `sq`. -/
theorem exists_isTransposeOf_scheme {T Y : Scheme.{u}} {g : Y ⟶ T} (sq : ChosenPullback g g)
    {ι : Type t} [Unique ι] (D : modulePullbackPseudofunctor.DescentData (fun _ : ι ↦ g))
    {A : Y.Modules} (hA : A = D.obj default)
    {θ : (modulePullbackPseudofunctor.map sq.p₁.op.toLoc).toFunctor.obj A ⟶
      (modulePullbackPseudofunctor.map sq.p₂.op.toLoc).toFunctor.obj A}
    (hθ : HEq θ (D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂))
    (h₁ : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (sq.hp₂.trans sq.hp₁.symm)).app A)) :
    ∃ a : A ⟶ (modulePullbackPseudofunctor.map g.op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward g).obj A),
      Pseudofunctor.IsTransposeOf (F := modulePullbackPseudofunctor) sq
        (Scheme.Modules.pullbackPushforwardAdjunction g) a θ := by
  subst hA
  obtain rfl := eq_of_heq hθ
  have hiso : IsIso ((Pseudofunctor.descentBaseChange (F := modulePullbackPseudofunctor) sq
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.pullbackPushforwardAdjunction sq.p₁)).app (D.obj default)) := by
    rwa [descentBaseChange_eq_baseChangeNatTrans]
  exact Pseudofunctor.exists_isTransposeOf sq
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction sq.p₁) D

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- After forgetting quasi-coherence, the counit of the adjunction on quasi-coherent modules is
the counit of the adjunction on all sheaves of modules. -/
@[simp]
lemma counit_pullbackQcohAdjunction_app_hom
    (M : (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).FullSubcategory) :
    ((pullbackQcohAdjunction φ).counit.app M).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.app M.obj := by
  refine (Adjunction.map_restrictFullyFaithful_counit_app
    (L := pullbackQcoh φ) (R := pushforwardQcoh φ)
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    (Functor.FullyFaithful.ofFullyFaithful
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι)
    (Functor.FullyFaithful.ofFullyFaithful
      (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).ι)
    (Iso.refl _) (Iso.refl _) M).trans ?_
  simp only [Iso.refl_inv, NatTrans.id_app]
  refine (Category.id_comp _).trans ?_
  exact (congrArg (· ≫ _) (CategoryTheory.Functor.map_id
    (Scheme.Modules.pullback (Spec.map φ)) _)).trans (Category.id_comp _)

/-- An Eilenberg–Moore coalgebra for the comonad of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)` whose underlying
sheaf of modules is quasi-coherent, as a coalgebra for the comonad of
`Stacks.Descent.pullbackQcohAdjunction`, on the same structure morphism. -/
noncomputable def coalgebraPullbackQcoh (A : (Spec S).Modules) [A.IsQuasicoherent]
    (a : A ⟶ (Scheme.Modules.pullback (Spec.map φ)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj A))
    (hcounit : a ≫ (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.app A =
      𝟙 A)
    (hcoassoc : a ≫ (Scheme.Modules.pullback (Spec.map φ)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            ((Scheme.Modules.pushforward (Spec.map φ)).obj A)) =
        a ≫ (Scheme.Modules.pullback (Spec.map φ)).map
          ((Scheme.Modules.pushforward (Spec.map φ)).map a)) :
    (pullbackQcohAdjunction φ).toComonad.Coalgebra where
  A := ⟨A, ‹A.IsQuasicoherent›⟩
  a := ObjectProperty.homMk a
  counit := by
    apply ObjectProperty.hom_ext
    change a ≫ ((pullbackQcohAdjunction φ).counit.app ⟨A, ‹A.IsQuasicoherent›⟩).hom = 𝟙 A
    rwa [counit_pullbackQcohAdjunction_app_hom]
  coassoc := by
    apply ObjectProperty.hom_ext
    change a ≫ (Scheme.Modules.pullback (Spec.map φ)).map
          ((pullbackQcohAdjunction φ).unit.app
            ((pushforwardQcoh φ).obj ⟨A, ‹A.IsQuasicoherent›⟩)).hom =
      a ≫ (Scheme.Modules.pullback (Spec.map φ)).map
        ((Scheme.Modules.pushforward (Spec.map φ)).map a)
    rwa [unit_pullbackQcohAdjunction_app_hom]

/-- For a faithfully flat `φ : R ⟶ S` and a quasi-coherent module `A` on `Spec S` carrying a
coalgebra structure `a` for the comonad of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)`, there is a
quasi-coherent module `M` on `Spec R` and an isomorphism `(Spec φ)^* M ≅ A` compatible with the
structure morphisms. -/
theorem exists_iso_pullback_of_coalgebra (hφ : φ.hom.FaithfullyFlat)
    (A : (Spec S).Modules) [A.IsQuasicoherent]
    (a : A ⟶ (Scheme.Modules.pullback (Spec.map φ)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj A))
    (hcounit : a ≫ (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.app A =
      𝟙 A)
    (hcoassoc : a ≫ (Scheme.Modules.pullback (Spec.map φ)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            ((Scheme.Modules.pushforward (Spec.map φ)).obj A)) =
        a ≫ (Scheme.Modules.pullback (Spec.map φ)).map
          ((Scheme.Modules.pushforward (Spec.map φ)).map a)) :
    ∃ (M : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory)
      (e : (Scheme.Modules.pullback (Spec.map φ)).obj M.obj ≅ A),
      (Scheme.Modules.pullback (Spec.map φ)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M.obj) ≫
        (Scheme.Modules.pullback (Spec.map φ)).map
          ((Scheme.Modules.pushforward (Spec.map φ)).map e.hom) = e.hom ≫ a := by
  have := isEquivalence_comparison_pullbackQcohAdjunction φ hφ
  obtain ⟨M, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage
    (F := Comonad.comparison (pullbackQcohAdjunction φ))
    (coalgebraPullbackQcoh φ A a hcounit hcoassoc)
  refine ⟨M, (ObjectProperty.ι _).mapIso
    ((pullbackQcohAdjunction φ).toComonad.forget.mapIso i), ?_⟩
  have hh := congrArg InducedCategory.Hom.hom i.hom.h
  change (Scheme.Modules.pullback (Spec.map φ)).map ((pullbackQcohAdjunction φ).unit.app M).hom ≫
      (Scheme.Modules.pullback (Spec.map φ)).map
        ((Scheme.Modules.pushforward (Spec.map φ)).map i.hom.f.hom) =
    i.hom.f.hom ≫ a at hh
  rwa [unit_pullbackQcohAdjunction_app_hom] at hh

/-- `Stacks.Descent.exists_iso_pullback_of_coalgebra` with the inverse image written as the
pullback pseudofunctor writes it. -/
theorem exists_iso_pullback_of_coalgebra' (hφ : φ.hom.FaithfullyFlat)
    (A : (Spec S).Modules) [A.IsQuasicoherent]
    (a : A ⟶ (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj A))
    (hcounit : a ≫ (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.app A =
      𝟙 A)
    (hcoassoc : a ≫ (Scheme.Modules.pullback (Spec.map φ)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            ((Scheme.Modules.pushforward (Spec.map φ)).obj A)) =
        a ≫ (Scheme.Modules.pullback (Spec.map φ)).map
          ((Scheme.Modules.pushforward (Spec.map φ)).map a)) :
    ∃ (M : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory)
      (e : (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.obj M.obj ≅ A),
      (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M.obj) ≫
        (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.map
          ((Scheme.Modules.pushforward (Spec.map φ)).map e.hom) = e.hom ≫ a :=
  exists_iso_pullback_of_coalgebra φ hφ A a hcounit hcoassoc

section Affine

variable {P : CommRingCat.{u}} {ψ₁ ψ₂ : S ⟶ P} (hpc : IsPushout φ φ ψ₁ ψ₂)
  {ι : Type t} [Unique ι] (D : QuasicoherentDescentData (fun _ : ι ↦ Spec.map φ))

/-- The transition morphism of a quasi-coherent descent datum for a one-element affine family,
over the chosen pullback provided by a pushout square of rings. -/
noncomputable abbrev affineTransition :
    (modulePullbackPseudofunctor.map (specChosenPullback hpc).p₁.op.toLoc).toFunctor.obj
        (D.component default) ⟶
      (modulePullbackPseudofunctor.map (specChosenPullback hpc).p₂.op.toLoc).toFunctor.obj
        (D.component default) :=
  D.obj.hom (i₁ := default) (i₂ := default) (specChosenPullback hpc).p
    (specChosenPullback hpc).p₁ (specChosenPullback hpc).p₂ (specChosenPullback hpc).hp₁
    (specChosenPullback hpc).hp₂

/-- For a quasi-coherent descent datum `D` along `Spec φ` and a morphism `a` on its component, the
transition morphism of `D` over the chosen pullback provided by a pushout square of rings is
compatible with `a`, in the sense of `Stacks.Descent.IsTransposedCocycleAt`. -/
def IsTransposedCocycle
    (a : D.component default ⟶
      (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (D.component default))) : Prop :=
  IsTransposedCocycleAt (specChosenPullback hpc) (affineTransition φ hpc D) a

/-- The counit axiom of a structure morphism `a` transposing to the transition morphism of
`D`. -/
theorem counit_affine
    (a : D.component default ⟶
      (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (D.component default)))
    (ha : Pseudofunctor.IsTransposeOf (F := modulePullbackPseudofunctor)
      (specChosenPullback hpc) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) a
      (affineTransition φ hpc D)) :
    a ≫ (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.app
      (D.component default) = 𝟙 (D.component default) :=
  Pseudofunctor.counit_of_descentData (F := modulePullbackPseudofunctor)
    (specChosenPullback hpc) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    D.obj ha

/-- The coassociativity axiom of a structure morphism `a` transposing to the transition morphism
of `D` and satisfying `Stacks.Descent.IsTransposedCocycle`. -/
theorem coassoc_affine
    (hp : MilnorPatching.IsPushoutSquare φ.hom φ.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hpc.w]))
    (a : D.component default ⟶
      (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (D.component default)))
    (ha : Pseudofunctor.IsTransposeOf (F := modulePullbackPseudofunctor)
      (specChosenPullback hpc) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) a
      (affineTransition φ hpc D))
    (hco : IsTransposedCocycle φ hpc D a) :
    a ≫ (Scheme.Modules.pullback (Spec.map φ)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
          ((Scheme.Modules.pushforward (Spec.map φ)).obj (D.component default))) =
      a ≫ (Scheme.Modules.pullback (Spec.map φ)).map
        ((Scheme.Modules.pushforward (Spec.map φ)).map a) := by
  have hqpf : ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (D.component default)).IsQuasicoherent :=
    isQuasicoherent_pushforward_specMap φ (D.component default)
  have hqpb : ((Scheme.Modules.pullback (Spec.map φ)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (D.component default))).IsQuasicoherent :=
    isQuasicoherent_pullback_specMap φ _
  exact coassoc_of_descentDataCoassoc_scheme (specChosenPullback hpc) ha
    (isIso_descentBaseChange_specMap hpc hp ((Scheme.Modules.pullback (Spec.map φ)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (D.component default)))) hco

/-- If the component of `D` carries a morphism `a` transposing to the transition morphism of `D`
over the chosen pullback and satisfying `Stacks.Descent.IsTransposedCocycle`, then there is a
quasi-coherent module `M` on `Spec R` together with an isomorphism of the canonical descent datum
of `M` with `D`. -/
theorem exists_isQuasicoherent_descentDataIso (hφ : φ.hom.FaithfullyFlat)
    (hp : MilnorPatching.IsPushoutSquare φ.hom φ.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hpc.w]))
    (a : D.component default ⟶
      (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (D.component default)))
    (ha : Pseudofunctor.IsTransposeOf (F := modulePullbackPseudofunctor)
      (specChosenPullback hpc) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) a
      (affineTransition φ hpc D))
    (hco : IsTransposedCocycle φ hpc D a) :
    ∃ M : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory,
      Nonempty ((modulePullbackPseudofunctor.toDescentData
        (fun _ : ι ↦ Spec.map φ)).obj M.obj ≅ D.obj) := by
  obtain ⟨M, e, heq⟩ := exists_iso_pullback_of_coalgebra' φ hφ (D.component default) a
    (counit_affine φ hpc D a ha) (coassoc_affine φ hpc D hp a ha hco)
  exact ⟨M, ⟨Pseudofunctor.descentDataIsoOfCoalgebraIso (F := modulePullbackPseudofunctor)
    (specChosenPullback hpc) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    (Scheme.Modules.pullbackPushforwardAdjunction (specChosenPullback hpc).p₁) ha e heq⟩⟩

/-- Let `φ : R ⟶ S` be faithfully flat, let `ψ₁, ψ₂ : S ⟶ P` present `P` as the pushout of `φ`
with itself both categorically and in the sense of `MilnorPatching.IsPushoutSquare`, and let `D`
be a quasi-coherent descent datum for the one-element family `Spec φ`. If the component of `D`
carries a morphism `a` transposing to the transition morphism of `D` over `Spec P`, and `a`
satisfies `Stacks.Descent.IsTransposedCocycle`, then `D` is effective. -/
theorem isEffective_of_isTransposedCocycle (hφ : φ.hom.FaithfullyFlat)
    (hp : MilnorPatching.IsPushoutSquare φ.hom φ.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hpc.w]))
    (a : D.component default ⟶
      (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (D.component default)))
    (ha : Pseudofunctor.IsTransposeOf (F := modulePullbackPseudofunctor)
      (specChosenPullback hpc) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) a
      (affineTransition φ hpc D))
    (hco : IsTransposedCocycle φ hpc D a) : D.IsEffective := by
  obtain ⟨M, ⟨e⟩⟩ := exists_isQuasicoherent_descentDataIso φ hpc D hφ hp a ha hco
  exact isEffective_of_descentDataIso D M e

/-- For a quasi-coherent descent datum `D` along `Spec φ`, a pushout presentation `ψ₁, ψ₂` of
`P` and a morphism `a` on the component of `D` transposing to the transition morphism of `D` over
`Spec P`, the transition morphism is compatible with `a`. -/
theorem isTransposedCocycle
    (hp : MilnorPatching.IsPushoutSquare φ.hom φ.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hpc.w]))
    (a : D.component default ⟶
      (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (D.component default)))
    (ha : Pseudofunctor.IsTransposeOf (F := modulePullbackPseudofunctor)
      (specChosenPullback hpc) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) a
      (affineTransition φ hpc D)) :
    IsTransposedCocycle φ hpc D a := by
  let _i : Algebra S P := ψ₁.hom.toAlgebra
  have hofHom : CommRingCat.ofHom (algebraMap S P) = ψ₁ := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  have hpc' : IsPushout ψ₁ ψ₁
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : P →+* P ⊗[S] P))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : P →+* P ⊗[S] P)) := by
    have h := (CommRingCat.isPushout_tensorProduct S P P).flip
    rwa [hofHom] at h
  exact isTransposedCocycle_scheme (specChosenPullback hpc) rfl (specChosenPullback hpc')
    D.obj rfl ha HEq.rfl
    (Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_baseChangeNatTrans_specMap hpc.w.symm hp
      (D.component default))
    (@Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_baseChangeNatTrans_specMap _ _ _ _ _ _ _ _
      hpc'.w.symm MilnorPatching.tensorPushout
      ((Scheme.Modules.pullback (Spec.map ψ₂)).obj (D.component default))
      (isQuasicoherent_pullback_specMap ψ₂ _))

/-- Let `φ : R ⟶ S` be faithfully flat, let `ψ₁, ψ₂ : S ⟶ P` present `P` as the pushout of `φ`
with itself both categorically and in the sense of `MilnorPatching.IsPushoutSquare`, and let `D`
be a quasi-coherent descent datum for the one-element family `Spec φ`. If the component of `D`
carries a morphism `a` transposing to the transition morphism of `D` over `Spec P`, then `D` is
effective. -/
theorem isEffective_of_isTransposeOf (hφ : φ.hom.FaithfullyFlat)
    (hp : MilnorPatching.IsPushoutSquare φ.hom φ.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hpc.w]))
    (a : D.component default ⟶
      (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (D.component default)))
    (ha : Pseudofunctor.IsTransposeOf (F := modulePullbackPseudofunctor)
      (specChosenPullback hpc) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) a
      (affineTransition φ hpc D)) : D.IsEffective :=
  isEffective_of_isTransposedCocycle φ hpc D hφ hp a ha (isTransposedCocycle φ hpc D hp a ha)

/-- The component of a quasi-coherent descent datum along `Spec φ` carries a morphism `a`
transposing to the transition morphism of the datum over the chosen pullback `Spec P`. -/
theorem exists_isTransposeOf_affine
    (hp : MilnorPatching.IsPushoutSquare φ.hom φ.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hpc.w])) :
    ∃ a : D.component default ⟶
        (modulePullbackPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.obj
          ((Scheme.Modules.pushforward (Spec.map φ)).obj (D.component default)),
      Pseudofunctor.IsTransposeOf (F := modulePullbackPseudofunctor)
        (specChosenPullback hpc) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) a
        (affineTransition φ hpc D) :=
  exists_isTransposeOf_scheme (specChosenPullback hpc) D.obj rfl HEq.rfl
    (Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_baseChangeNatTrans_specMap hpc.w.symm hp
      (D.component default))

/-- Let `φ : R ⟶ S` be faithfully flat, let `ψ₁, ψ₂ : S ⟶ P` present `P` as the pushout of `φ`
with itself both categorically and in the sense of `MilnorPatching.IsPushoutSquare`, and let `D`
be a quasi-coherent descent datum for the one-element family `Spec φ`. Then `D` is effective. -/
@[sga "1 VIII 1.3" "Cor. 1.3, special case"]
theorem isEffective_of_faithfullyFlat_affine (hφ : φ.hom.FaithfullyFlat)
    (hp : MilnorPatching.IsPushoutSquare φ.hom φ.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hpc.w])) : D.IsEffective := by
  obtain ⟨a, ha⟩ := exists_isTransposeOf_affine φ hpc D hp
  exact isEffective_of_isTransposeOf φ hpc D hφ hp a ha

end Affine

end Stacks.Descent

end
