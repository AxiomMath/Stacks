module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiStack
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Galois descent data for quasi-coherent modules

Let `f : X ⟶ Y` be a morphism of schemes equipped with an action of a group `G` on `X` over
`Y`, and suppose the action identifies the disjoint union of the copies of `X` indexed by `G`
with `X ×_Y X`.  A *Galois descent datum* is a quasi-coherent module `ℱ` on `X` together with
isomorphisms `φ_σ : ℱ ≅ f_σ^* ℱ` satisfying `φ_(στ) = f_σ^*(φ_τ) ∘ φ_σ`.

This file sets up that category and the comparison between it and the descent data of
`Stacks.Descent.qcohPseudofunctor` for the one-element family `{f}`.

## Main definitions

* `Stacks.Descent.galoisCoverComparison` is the map from the disjoint union indexed by `G` to
  `X ×_Y X` induced by the action.
* `Stacks.Descent.GaloisDescentData` is the category of quasi-coherent modules equipped with
  the action-indexed isomorphisms and their cocycle.
* `Stacks.Descent.galoisDescentFunctor` is the comparison functor from the quasi-coherent
  descent data of Stacks 023B for the one-element family `{f}` to `GaloisDescentData`.

## Main results

* `Stacks.Descent.ofArrows_galoisFamily_mem_fpqcPrecoverage`: a surjective finite étale
  morphism is a one-element fpqc covering.
* `Stacks.Descent.galoisDescentFunctor_obj_φ` and
  `Stacks.Descent.galoisDescentFunctor_map_hom`: the computation rules for the comparison
  functor.
* `Stacks.Descent.nonempty_equivalence_galoisDescentData_of_isStack`: if quasi-coherent modules
  form a stack for the fpqc topology (Stacks 023T) and the comparison functor is an equivalence,
  then quasi-coherent modules on `Y` are equivalent to Galois descent data.

## Implementation notes

The isomorphism `φ_σ` attached to a descent datum `D` is `D.iso f (𝟙 X) f_σ`, precomposed with
the inverse of `Scheme.Modules.pullbackId`; see `Stacks.Descent.galoisIso`.  Its cocycle
identity is the conjunction of `CategoryTheory.Pseudofunctor.DescentData.hom_comp` (at the
triple `𝟙 X`, `f_σ`, `f_(στ)`) and `CategoryTheory.Pseudofunctor.DescentData.pullHom_hom`
(along `g = f_σ`); the two coherence constants appearing after expanding
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` are identified by
`Stacks.Descent.galoisMapComp'_inv_app` and `Stacks.Descent.galoisMapComp'_id_hom_app`.

Terms such as `D.obj PUnit.unit` carry the type `modulePullbackPseudofunctor.obj (.mk (op X))`
rather than `X.Modules`, and the two are interchangeable only at default transparency.  This
makes `rw`/`simp` with `Functor.map_comp` and `Category.assoc` fail on goals mentioning
`Scheme.Modules.pullbackId`, so the two associativity rearrangements that finish the cocycle
and the compatibility proof are isolated as the category-theoretic lemmas
`Stacks.Descent.galoisRearrangeCocycle` and `Stacks.Descent.galoisRearrangeComm`, which are
applied as terms.

## References

* [Stacks Project, Tag 0D1V](https://stacks.math.columbia.edu/tag/0D1V)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Pseudofunctor.LocallyDiscreteOpToCat

universe v u

namespace Stacks.Descent

/-- The canonical map `G × X ⟶ X ×_Y X` associated to an action of `Gᵐᵒᵖ` on `X` over `Y`; on
the summand indexed by `σ` it is `(id, f_σ)`. -/
def galoisCoverComparison {G : Type v} [Group G] [Finite G]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Gᵐᵒᵖ →* Aut (Over.mk f)) :
    (∐ fun _ : G ↦ X) ⟶ pullback f f :=
  Sigma.desc fun σ ↦ pullback.lift (𝟙 X) (a (.op σ)).asIso.hom.left (by
    simpa using (a (.op σ)).asIso.hom.w.symm)

namespace GaloisDescentData

variable (G : Type v) [Group G] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (a : Gᵐᵒᵖ →* Aut (Over.mk f))

/-- The automorphism `f_σ` of `X` supplied by the action over `Y`. -/
abbrev twist (σ : G) : X ⟶ X := (a (.op σ)).asIso.hom.left

/-- The automorphisms supplied by the action are morphisms over `Y`. -/
lemma twist_comp (σ : G) : twist G f a σ ≫ f = f := by simpa using (a (.op σ)).asIso.hom.w

/-- The action is multiplicative; the opposite multiplication on `Gᵐᵒᵖ` turns it into a left
action by composition on the left. -/
lemma twist_mul (σ τ : G) : twist G f a σ ≫ twist G f a τ = twist G f a (σ * τ) := by
  change (a (.op σ)).asIso.hom.left ≫ (a (.op τ)).asIso.hom.left =
    (a (.op (σ * τ))).asIso.hom.left
  rw [← Over.comp_left]
  exact congrArg (fun e : Aut (Over.mk f) ↦ e.asIso.hom.left) ((a.map_mul (.op τ) (.op σ)).symm)

/-- The unit of the group acts trivially. -/
lemma twist_one : twist G f a 1 = 𝟙 X := by
  change (a (.op 1)).asIso.hom.left = _
  rw [show (MulOpposite.op (1 : G)) = 1 from rfl, map_one]
  rfl

/-- The canonical comparison from two successive pullbacks to pullback by the product
automorphism. -/
def pullbackMulIso (σ τ : G) :
    Scheme.Modules.pullback (twist G f a τ) ⋙ Scheme.Modules.pullback (twist G f a σ) ≅
      Scheme.Modules.pullback (twist G f a (σ * τ)) :=
  Scheme.Modules.pullbackComp (twist G f a σ) (twist G f a τ) ≪≫
    Scheme.Modules.pullbackCongr (twist_mul G f a σ τ)

/-- A quasi-coherent module on `X` with an isomorphism to its pullback by every `f_σ`,
satisfying the Galois cocycle condition. -/
@[ext]
structure Obj where
  /-- The underlying module on `X`. -/
  module : X.Modules
  /-- The underlying module is quasi-coherent. -/
  isQuasicoherent : module.IsQuasicoherent
  /-- The isomorphism associated to `σ`. -/
  φ (σ : G) : module ≅ (Scheme.Modules.pullback (twist G f a σ)).obj module
  /-- The Galois cocycle condition. -/
  cocycle (σ τ : G) :
    φ (σ * τ) =
      φ σ ≪≫
        (Scheme.Modules.pullback (twist G f a σ)).mapIso (φ τ) ≪≫
        (pullbackMulIso G f a σ τ).app module

/-- A morphism of Galois descent systems is a module morphism commuting with every
action-indexed isomorphism. -/
@[ext]
structure Hom (A B : Obj G f a) where
  /-- The underlying morphism of modules. -/
  hom : A.module ⟶ B.module
  /-- Compatibility with every action-indexed isomorphism. -/
  comm (σ : G) :
    (A.φ σ).hom ≫ (Scheme.Modules.pullback (twist G f a σ)).map hom =
      hom ≫ (B.φ σ).hom

/-- Galois descent data form a category, with composition that of the underlying module
morphisms. -/
instance : Category (Obj G f a) where
  Hom := Hom G f a
  id A := ⟨𝟙 A.module, by simp⟩
  comp h k := ⟨h.hom ≫ k.hom, by
    intro σ
    simp only [Functor.map_comp]
    rw [← Category.assoc, h.comm, Category.assoc, k.comm, ← Category.assoc]⟩
  id_comp h := by apply Hom.ext; simp
  comp_id h := by apply Hom.ext; simp
  assoc h k l := by apply Hom.ext; simp

/-- The underlying module morphism of the identity is the identity. -/
@[simp] lemma id_hom (A : Obj G f a) : Hom.hom (𝟙 A) = 𝟙 A.module := rfl

/-- The underlying module morphism of a composite is the composite of the underlying morphisms. -/
@[simp] lemma comp_hom {A B C : Obj G f a} (h : A ⟶ B) (k : B ⟶ C) :
    Hom.hom (h ≫ k) = Hom.hom h ≫ Hom.hom k := rfl

end GaloisDescentData

/-- The category of systems `(ℱ, (φ_σ)_σ)` occurring in Galois descent for the action `a`. -/
abbrev GaloisDescentData (G : Type v) [Group G] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : Gᵐᵒᵖ →* Aut (Over.mk f)) :=
  GaloisDescentData.Obj G f a

section Family

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The one-element family consisting of `f`, as the family of a descent problem. -/
abbrev galoisFamily : ∀ _ : PUnit.{1}, X ⟶ Y := fun _ ↦ f

/-- **A surjective finite étale morphism is a one-element fpqc covering.** -/
lemma ofArrows_galoisFamily_mem_fpqcPrecoverage [IsFinite f] [Etale f] [Surjective f] :
    Presieve.ofArrows (fun _ : PUnit.{1} ↦ X) (galoisFamily f) ∈
      Scheme.fpqcPrecoverage.{u} Y := by
  rw [Presieve.ofArrows_pUnit.{0}]
  exact f.singleton_mem_fpqcPrecoverage

end Family

section Coherence

/-- The inverse of the comparison `Pseudofunctor.mapComp'` for
`AlgebraicGeometry.modulePullbackPseudofunctor`, in terms of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
lemma galoisMapComp'_inv_app {X₁ X₂ X₃ : Scheme.{u}} (p : X₂ ⟶ X₃) (q : X₁ ⟶ X₂)
    (r : X₁ ⟶ X₃) (h : q ≫ p = r)
    (M : modulePullbackPseudofunctor.{u}.obj (.mk (op X₃))) :
    (modulePullbackPseudofunctor.mapComp' p.op.toLoc q.op.toLoc r.op.toLoc
        (by simp [← h])).inv.toNatTrans.app M =
      ((Scheme.Modules.pullbackComp q p).hom ≫ (Scheme.Modules.pullbackCongr h).hom).app M := by
  subst h; rfl

/-- The comparison `Pseudofunctor.mapComp'` at an identity first leg, in terms of
`AlgebraicGeometry.Scheme.Modules.pullbackId`. -/
lemma galoisMapComp'_id_hom_app {X₁ X₃ : Scheme.{u}} (q : X₁ ⟶ X₃)
    (M : modulePullbackPseudofunctor.{u}.obj (.mk (op X₃))) :
    (modulePullbackPseudofunctor.mapComp' (𝟙 X₃).op.toLoc q.op.toLoc q.op.toLoc
        (by simp)).hom.toNatTrans.app M =
      (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackId X₃).inv.app M) :=
  Pseudofunctor.mapComp'_id_comp_hom_app (F := modulePullbackPseudofunctor.{u}) q.op.toLoc M

/-- Reassociation of the composite `(A ≫ B) ≫ P.map (A ≫ B') ≫ c` for a functor `P`. -/
lemma galoisRearrangeCocycle {C : Type*} [Category C] (P : C ⥤ C) {U V W Z : C}
    (A : U ⟶ V) (B : V ⟶ P.obj U) (B' : V ⟶ W) (c : P.obj W ⟶ Z) :
    (A ≫ B) ≫ P.map (A ≫ B') ≫ c = A ≫ B ≫ P.map A ≫ P.map B' ≫ c := by
  simp

/-- For functors `P` and `Q`, if `u₁ ≫ Q.map h = h ≫ u₂` and `Q.map h ≫ d₂ = d₁ ≫ P.map h`, then
`(u₁ ≫ d₁) ≫ P.map h = h ≫ u₂ ≫ d₂`. -/
lemma galoisRearrangeComm {C : Type*} [Category C] (P Q : C ⥤ C) {M₁ M₂ : C}
    (h : M₁ ⟶ M₂) (u₁ : M₁ ⟶ Q.obj M₁) (u₂ : M₂ ⟶ Q.obj M₂)
    (d₁ : Q.obj M₁ ⟶ P.obj M₁) (d₂ : Q.obj M₂ ⟶ P.obj M₂)
    (hnat : u₁ ≫ Q.map h = h ≫ u₂) (hcomm : Q.map h ≫ d₂ = d₁ ≫ P.map h) :
    (u₁ ≫ d₁) ≫ P.map h = h ≫ u₂ ≫ d₂ := by
  rw [Category.assoc, ← hcomm, ← Category.assoc, hnat, Category.assoc]

end Coherence

section Decomposition

open GaloisDescentData

variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (a : Gᵐᵒᵖ →* Aut (Over.mk f))

omit [Group G] in
/-- A summand of the disjoint union is an open subscheme of it. -/
lemma isOpenImmersion_sigmaι_const (σ : G) :
    IsOpenImmersion (Sigma.ι (fun _ : G ↦ X) σ) :=
  (sigmaOpenCover (fun _ : G ↦ X)).map_prop σ

/-- **The Galois decomposition of a pair of morphisms into `X` agreeing over `Y`.**  If the
action identifies `∐_{σ : G} X` with `X ×_Y X`, then any two morphisms `f₁, f₂ : W ⟶ X` with
`f₁ ≫ f = f₂ ≫ f` become `g` and `g ≫ f_σ` on the members of an open cover of `W` indexed by
`G`. -/
theorem exists_openCover_twist [IsIso (galoisCoverComparison f a)] {W : Scheme.{u}}
    (f₁ f₂ : W ⟶ X) (hcomm : f₁ ≫ f = f₂ ≫ f) :
    ∃ (V : G → Scheme.{u}) (p : ∀ σ, V σ ⟶ W) (_ : ∀ σ, IsOpenImmersion (p σ))
      (g : ∀ σ, V σ ⟶ X), ⨆ σ, (p σ).opensRange = ⊤ ∧
        (∀ σ, p σ ≫ f₁ = g σ) ∧ ∀ σ, p σ ≫ f₂ = g σ ≫ twist G f a σ := by
  have hoi := isOpenImmersion_sigmaι_const (X := X) (G := G)
  set k : W ⟶ (∐ fun _ : G ↦ X) :=
    pullback.lift f₁ f₂ hcomm ≫ inv (galoisCoverComparison f a) with hk
  have hE : ∀ σ : G, pullback.fst k (Sigma.ι (fun _ : G ↦ X) σ) ≫ pullback.lift f₁ f₂ hcomm =
      pullback.snd k (Sigma.ι (fun _ : G ↦ X) σ) ≫
        pullback.lift (𝟙 X) (twist G f a σ) (by rw [Category.id_comp, twist_comp]) := by
    intro σ
    rw [show pullback.lift f₁ f₂ hcomm = k ≫ galoisCoverComparison f a by
      rw [hk, Category.assoc, IsIso.inv_hom_id, Category.comp_id], ← Category.assoc,
      pullback.condition, Category.assoc]
    simp [galoisCoverComparison]
  refine ⟨fun σ ↦ pullback k (Sigma.ι (fun _ : G ↦ X) σ), fun σ ↦ pullback.fst _ _,
    fun σ ↦ have := hoi σ; inferInstance,
    fun σ ↦ pullback.snd _ _, ?_, fun σ ↦ ?_, fun σ ↦ ?_⟩
  · exact Scheme.OpenCover.iSup_opensRange ((sigmaOpenCover (fun _ : G ↦ X)).pullback₁ k)
  · simpa only [Category.assoc, pullback.lift_fst, Category.comp_id] using
      congrArg (· ≫ pullback.fst f f) (hE σ)
  · simpa only [Category.assoc, pullback.lift_snd] using congrArg (· ≫ pullback.snd f f) (hE σ)

end Decomposition

section Comparison

open GaloisDescentData

variable {G : Type v} [Group G] {X Y : Scheme.{u}} {f : X ⟶ Y}
  {a : Gᵐᵒᵖ →* Aut (Over.mk f)}

/-- The isomorphism `ℱ ≅ f_σ^* ℱ` carried by a descent datum for the one-element family
`{f}`. -/
def galoisIso (D : modulePullbackPseudofunctor.DescentData (galoisFamily f)) (σ : G) :
    D.obj .unit ≅ (Scheme.Modules.pullback (twist G f a σ)).obj (D.obj .unit) :=
  ((Scheme.Modules.pullbackId X).app (D.obj .unit)).symm ≪≫
    D.iso f (𝟙 X) (twist G f a σ) (by simp) (twist_comp G f a σ)

/-- The Galois cocycle identity for `Stacks.Descent.galoisIso`, on underlying morphisms, with
each `Stacks.Descent.galoisIso` written as the inverse of `Scheme.Modules.pullbackId` followed by
`D.hom`. -/
lemma galoisIso_mul_hom (D : modulePullbackPseudofunctor.DescentData (galoisFamily f))
    (σ τ : G) :
    ((Scheme.Modules.pullbackId X).app (D.obj .unit)).inv ≫
        D.hom f (𝟙 X) (twist G f a (σ * τ)) (by simp) (twist_comp G f a (σ * τ)) =
      ((Scheme.Modules.pullbackId X).app (D.obj .unit)).inv ≫
        D.hom f (𝟙 X) (twist G f a σ) (by simp) (twist_comp G f a σ) ≫
          (Scheme.Modules.pullback (twist G f a σ)).map
              ((Scheme.Modules.pullbackId X).app (D.obj .unit)).inv ≫
            (Scheme.Modules.pullback (twist G f a σ)).map
                (D.hom f (𝟙 X) (twist G f a τ) (by simp) (twist_comp G f a τ)) ≫
              (pullbackMulIso G f a σ τ).hom.app (D.obj .unit) := by
  have key := D.pullHom_hom (i₁ := PUnit.unit) (i₂ := PUnit.unit)
    (twist G f a σ) f f (twist_comp G f a σ) (𝟙 X) (twist G f a τ)
    (by simp) (twist_comp G f a τ) (twist G f a σ) (twist G f a (σ * τ))
    (by simp) (twist_mul G f a σ τ)
  rw [← D.hom_comp f (𝟙 X) (twist G f a σ) (twist G f a (σ * τ))
    (by simp) (twist_comp G f a σ) (twist_comp G f a (σ * τ)), ← key]
  dsimp only [pullHom]
  rw [galoisMapComp'_id_hom_app, galoisMapComp'_inv_app _ _ _ (twist_mul G f a σ τ)]
  rfl

/-- **The Galois cocycle identity** `φ_(στ) = f_σ^*(φ_τ) ∘ φ_σ` for
`Stacks.Descent.galoisIso`. -/
lemma galoisIso_mul (D : modulePullbackPseudofunctor.DescentData (galoisFamily f)) (σ τ : G) :
    galoisIso D (σ * τ) = galoisIso (a := a) D σ ≪≫
      (Scheme.Modules.pullback (twist G f a σ)).mapIso (galoisIso D τ) ≪≫
        (pullbackMulIso G f a σ τ).app (D.obj .unit) := by
  apply Iso.ext
  change ((Scheme.Modules.pullbackId X).app (D.obj .unit)).inv ≫
        D.hom f (𝟙 X) (twist G f a (σ * τ)) (by simp) (twist_comp G f a (σ * τ)) =
      (((Scheme.Modules.pullbackId X).app (D.obj .unit)).inv ≫
          D.hom f (𝟙 X) (twist G f a σ) (by simp) (twist_comp G f a σ)) ≫
        (Scheme.Modules.pullback (twist G f a σ)).map
            (((Scheme.Modules.pullbackId X).app (D.obj .unit)).inv ≫
              D.hom f (𝟙 X) (twist G f a τ) (by simp) (twist_comp G f a τ)) ≫
          (pullbackMulIso G f a σ τ).hom.app (D.obj .unit)
  exact (galoisIso_mul_hom D σ τ).trans
    (galoisRearrangeCocycle (Scheme.Modules.pullback (twist G f a σ)) _ _ _ _).symm

/-- A morphism of descent data for the one-element family `{f}` is compatible with the Galois
isomorphisms. -/
lemma galoisIso_comm {D₁ D₂ : modulePullbackPseudofunctor.DescentData (galoisFamily f)}
    (ψ : D₁ ⟶ D₂) (σ : G) :
    (galoisIso (a := a) D₁ σ).hom ≫
        (Scheme.Modules.pullback (twist G f a σ)).map (ψ.hom .unit) =
      ψ.hom .unit ≫ (galoisIso (a := a) D₂ σ).hom := by
  change (((Scheme.Modules.pullbackId X).app (D₁.obj .unit)).inv ≫
        D₁.hom f (𝟙 X) (twist G f a σ) (by simp) (twist_comp G f a σ)) ≫
      (Scheme.Modules.pullback (twist G f a σ)).map (ψ.hom .unit) =
    ψ.hom .unit ≫ ((Scheme.Modules.pullbackId X).app (D₂.obj .unit)).inv ≫
      D₂.hom f (𝟙 X) (twist G f a σ) (by simp) (twist_comp G f a σ)
  exact galoisRearrangeComm (Scheme.Modules.pullback (twist G f a σ))
    (Scheme.Modules.pullback (𝟙 X)) (ψ.hom .unit) _ _ _ _
    (((Scheme.Modules.pullbackId X).inv.naturality (ψ.hom .unit)).symm)
    (ψ.comm f (𝟙 X) (twist G f a σ) (by simp) (twist_comp G f a σ))

variable (G) (f) (a) in
/-- **The comparison functor of Galois descent.**  It sends a quasi-coherent descent datum for
the one-element family `{f}` to the Galois descent datum given by the isomorphisms
`D.iso f (𝟙 X) f_σ`. -/
def galoisDescentFunctor :
    QuasicoherentDescentData (galoisFamily f) ⥤ GaloisDescentData G f a where
  obj D :=
    { module := D.obj.obj .unit
      isQuasicoherent := D.property .unit
      φ σ := galoisIso D.obj σ
      cocycle σ τ := galoisIso_mul D.obj σ τ }
  map ψ := ⟨ψ.hom.hom .unit, fun σ ↦ galoisIso_comm ψ.hom σ⟩
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by apply Hom.ext; rfl

/-- The module underlying the image of `D` under `Stacks.Descent.galoisDescentFunctor`. -/
@[simp]
lemma galoisDescentFunctor_obj_module (D : QuasicoherentDescentData (galoisFamily f)) :
    ((galoisDescentFunctor G f a).obj D).module = D.obj.obj .unit := rfl

/-- The isomorphisms of the image of `D` under `Stacks.Descent.galoisDescentFunctor` are the
`Stacks.Descent.galoisIso D.obj σ`. -/
@[simp]
lemma galoisDescentFunctor_obj_φ (D : QuasicoherentDescentData (galoisFamily f)) (σ : G) :
    ((galoisDescentFunctor G f a).obj D).φ σ = galoisIso D.obj σ := rfl

/-- The module morphism underlying the image of `ψ` under `Stacks.Descent.galoisDescentFunctor`
is the component of `ψ`. -/
@[simp]
lemma galoisDescentFunctor_map_hom {D₁ D₂ : QuasicoherentDescentData (galoisFamily f)}
    (ψ : D₁ ⟶ D₂) :
    Hom.hom ((galoisDescentFunctor G f a).map ψ) = ψ.hom.hom .unit := rfl

/-- **The comparison functor of Galois descent is faithful.** -/
instance : (galoisDescentFunctor G f a).Faithful where
  map_injective h :=
    ObjectProperty.hom_ext _ <| Pseudofunctor.DescentData.hom_ext fun ⟨⟩ ↦ congrArg Hom.hom h

end Comparison

section Reduction

open GaloisDescentData

variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [IsFinite f] [Etale f] [Surjective f] (a : Gᵐᵒᵖ →* Aut (Over.mk f))

/-- If quasi-coherent modules form a stack for the fpqc topology, then the canonical descent
functor for the one-element family `{f}` is an equivalence. -/
lemma isEquivalence_canonicalDescentFunctor_galoisFamily
    [qcohPseudofunctor.IsStack Scheme.fpqcTopology.{u}] :
    (canonicalDescentFunctor (galoisFamily f)).IsEquivalence := by
  obtain ⟨hff⟩ := nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack
    (ofArrows_galoisFamily_mem_fpqcPrecoverage f)
  have := hff.full
  have := hff.faithful
  have : (canonicalDescentFunctor (galoisFamily f)).EssSurj :=
    ⟨fun D ↦ isEffective_of_isStack (ofArrows_galoisFamily_mem_fpqcPrecoverage f) D⟩
  exact { }

/-- **Galois descent, conditionally.**  Quasi-coherent modules on `Y` are equivalent to Galois
descent data for a surjective finite étale cover with a Galois action, provided

* quasi-coherent modules form a stack for the fpqc topology (Stacks 023T), and
* the comparison functor `Stacks.Descent.galoisDescentFunctor` is an equivalence. -/
theorem nonempty_equivalence_galoisDescentData_of_isStack
    [qcohPseudofunctor.IsStack Scheme.fpqcTopology.{u}]
    [IsIso (galoisCoverComparison f a)]
    (h : (galoisDescentFunctor G f a).IsEquivalence) :
    Nonempty ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ≌
      GaloisDescentData G f a) := by
  have := isEquivalence_canonicalDescentFunctor_galoisFamily f
  exact ⟨(canonicalDescentFunctor (galoisFamily f) ⋙ galoisDescentFunctor G f a).asEquivalence⟩

end Reduction

end Stacks.Descent

end

end
