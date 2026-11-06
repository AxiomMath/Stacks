module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.AdditiveGroupGaloisModule
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
import StacksCore.Tactic.StacksAttribute

/-!
# The Galois module of a constant sheaf over a field is its value with trivial action

Let `K` be a field and `sbar` a geometric point of `Spec K`, and let `A` be an abelian group.
Under the stalk equivalence of [Stacks, Tag 04JQ] between abelian sheaves on the small étale site
of `Spec K` and discrete modules over the absolute Galois group, the constant sheaf of value `A`
corresponds to `A` with the **trivial** Galois action.  This is clause (1) of the example
[Stacks, Tag 03QV], there stated for `A = 𝐙/n𝐙`, which is the case `A = ULift (ZMod n)` of what
is proved here.

The argument is the one the statement suggests.  The stalk of a constant sheaf at a point of a
site is its value (`CategoryTheory.Sites.constantSheafFiberIso`), and the identification sends the
germ of a constant section to that constant **at every pointed étale neighbourhood**
(`CategoryTheory.Sites.constantSheafFiberIso_toSheafify_app`).  Since every element of the stalk
is the germ of a constant section, and since the Galois action of Tag 04JQ moves such a germ to
the germ of the same constant section at the translated lift, the action fixes every element.

## Main definitions

* `Stacks.GroupCohomology.trivialContinuousGModule`: an abelian group as a discrete `G`-module
  with trivial action.
* `AlgebraicGeometry.constantStalkIso`: the stalk of a constant abelian étale sheaf is its value.
* `AlgebraicGeometry.constantContinuousGModuleIso`: **the Galois module of a constant sheaf is its
  value with trivial action**, in the coefficient category of continuous group cohomology.

## Main results

* `CategoryTheory.Sites.exists_toPresheafFiber_toSheafify`: every element of the fibre of a
  constant sheaf at a point of a site is the germ of a constant section.
* `AlgebraicGeometry.etaleGaloisModule_constantEtaleSheaf_rho_apply`: **the absolute Galois group
  acts trivially on the stalk of a constant sheaf.**

## Implementation notes

The file follows
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.AdditiveGroupGaloisModule` step
for step — stalk computation, germwise equivariance, `CategoryTheory.Action.mkIso`, two
`CategoryTheory.ObjectProperty.isoMk`s, and transport along
`CategoryTheory.continuousGModuleEquivContinuousGAddCommGrp` — so that the three correspondences
of the example that this development has are produced by one and the same construction.

**Why `CategoryTheory.Sites.exists_toPresheafFiber_toSheafify` is stated for a general site.**
The equality `(constantSheaf J D).obj A = sheafify J (const A)` holds by definition but is not
seen through at the transparency tactics use, so the surjectivity statement is proved once in the
vocabulary of `CategoryTheory.GrothendieckTopology.Point.presheafFiber`, where no unfolding is
needed, and specialised to the small étale site in term mode.

**The coefficient universe is `u + 1`**, the universe of the objects of the small étale site of
Tag 021B of `Spec K`, which is the one Tag 04JQ and Tag 03QU are stated at in this chapter; the
abelian group `A` therefore lives in `Type (u + 1)`.

## References

* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV): the example, whose
  clause (1) this is.
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ): the stalk equivalence.
* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP): the category the trivial
  module lives in.
* [Stacks Project, Tag 09BG](https://stacks.math.columbia.edu/tag/09BG): the fibre of a constant
  sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ v₂ u

namespace Stacks.GroupCohomology

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Type*) [AddCommGroup A]

/-- The trivial discrete `G`-module on an abelian group. -/
def trivialContinuousGModule : ContinuousGModule.{_, _} G :=
  ofRepresentation (Representation.trivial ℤ G A) (by
    rw [isContinuous_actionOfRepresentation_iff]
    intro x
    simp)

end Stacks.GroupCohomology

namespace CategoryTheory.Sites

open Limits Opposite GrothendieckTopology

variable {C : Type*} [Category.{v₁} C] {J : GrothendieckTopology C}
  {D : Type*} {FD : D → D → Type*} {CD : D → Type v₂}
  [∀ A B, FunLike (FD A B) (CD A) (CD B)] [Category.{v₂} D] [ConcreteCategory.{v₂} D FD]
  [LocallySmall.{w} C] [HasWeakSheafify J D] [J.WEqualsLocallyBijective D]
  [UnivLE.{w, v₂}] [PreservesFilteredColimitsOfSize.{v₂, v₂} (forget D)]
  [PreservesFilteredColimitsOfSize.{w, w} (forget D)]
  [(forget D).ReflectsIsomorphisms] [HasColimitsOfSize.{w, w} D]

include FD CD in
/-- **Every element of the fibre of a constant sheaf is the germ of a constant section.**  The
sheafification map is an isomorphism on the fibre, and germs of sections of the constant
*presheaf* are jointly surjective onto its fibre. -/
theorem exists_toPresheafFiber_toSheafify (Φ : J.Point.{w}) (A : D)
    (x : CD (Φ.presheafFiber.obj (sheafify J ((Functor.const Cᵒᵖ).obj A)))) :
    ∃ (V : C) (q : Φ.fiber.obj V) (a : CD A),
      x = Φ.toPresheafFiber V q (sheafify J ((Functor.const Cᵒᵖ).obj A))
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op V) a) := by
  have := isIso_presheafFiber_map_toSheafify Φ A
  obtain ⟨V, q, a, ha⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := (Functor.const Cᵒᵖ).obj A)
    (ConcreteCategory.hom
      (inv (Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj A)))) x)
  refine ⟨V, q, a, ?_⟩
  have hx : ConcreteCategory.hom
      (Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj A)))
      (ConcreteCategory.hom
        (inv (Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj A)))) x) = x := by
    simp
  rw [← hx, ← ha]
  simp

end CategoryTheory.Sites

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

attribute [local instance]
  preservesFilteredColimitsOfSize_forget_addCommGrpCat
  isGrothendieckAbelian_sheaf_smallEtale_pinnedCoefficients

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K))) (A : Type (u + 1)) [AddCommGroup A]

/-- The constant abelian sheaf on the small étale site of `Spec K`. -/
abbrev constantEtaleSheaf :
    Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1} :=
  (constantSheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of A)

/-- The constant presheaf of value `A` on the small étale site of `Spec K`. -/
abbrev constantEtalePresheaf : (SmallEtale B (Spec (.of K)) hK)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.const _).obj (AddCommGrpCat.of A)

/-- The sheafification map of the constant presheaf, with its target spelled as the underlying
presheaf of the constant sheaf. -/
abbrev constantEtaleToSheafify :
    constantEtalePresheaf B K hK A ⟶
      (constantEtaleSheaf B K hK A).obj :=
  toSheafify (SmallEtale.topology B (Spec (.of K)) hK) (constantEtalePresheaf B K hK A)

/-- The stalk of a constant sheaf at a geometric point is its value. -/
def constantStalkIso :
    (abelianEtaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK sbar).obj
        (constantEtaleSheaf B K hK A) ≅ AddCommGrpCat.of A :=
  Sites.constantSheafFiberIso (fieldSitePoint B K hK sbar) (AddCommGrpCat.of A)

/-- The identification of the stalk of a constant sheaf with its value is injective, being an
isomorphism of abelian groups. -/
theorem constantStalkIso_injective :
    Function.Injective
      (ConcreteCategory.hom (constantStalkIso B K hK sbar A).hom) :=
  ((ConcreteCategory.isIso_iff_bijective
    (constantStalkIso B K hK sbar A).hom).mp inferInstance).1

/-- **Every element of the stalk of a constant sheaf is the germ of a constant section.**  The
sheafification map is an isomorphism on the stalk, and germs of sections of the constant
*presheaf* are jointly surjective onto its stalk. -/
theorem exists_abelianEtaleStalkGerm_toSheafify
    (x : ((abelianEtaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK sbar).obj
      (constantEtaleSheaf B K hK A) : _)) :
    ∃ (V : SmallEtale B (Spec (.of K)) hK)
      (q : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V) (a : A),
      x = abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
        (constantEtaleSheaf B K hK A) ((geometricPointFiber B (Spec (.of K)) hK sbar).elementsMk V q)
        (ConcreteCategory.hom ((constantEtaleToSheafify B K hK A).app (op V)) a) :=
  Sites.exists_toPresheafFiber_toSheafify (fieldSitePoint B K hK sbar) (AddCommGrpCat.of A) x

/-- **The identification of the stalk of a constant sheaf with its value sends the germ of a
constant section to that constant** — at *every* pointed étale neighbourhood, which is what makes
the Galois action trivial. -/
theorem constantStalkIso_abelianEtaleStalkGerm (V : SmallEtale B (Spec (.of K)) hK)
    (q : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V) (a : A) :
    ConcreteCategory.hom (constantStalkIso B K hK sbar A).hom
        (abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
          (constantEtaleSheaf B K hK A) ((geometricPointFiber B (Spec (.of K)) hK sbar).elementsMk V q)
          (ConcreteCategory.hom ((constantEtaleToSheafify B K hK A).app (op V)) a)) = a :=
  Sites.constantSheafFiberIso_toSheafify_app (fieldSitePoint B K hK sbar)
    (AddCommGrpCat.of A) V q a

/-- **The germ of a constant section does not depend on the lift of the geometric point**, in
particular not on its Galois translate: both germs go to the same constant under the
identification of the stalk with the value of the sheaf, which is injective. -/
theorem abelianEtaleStalkGerm_constant_galoisFiberAction
    (σ : GeometricPoint.absoluteGaloisGroup sbar) (V : SmallEtale B (Spec (.of K)) hK)
    (q : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V) (a : A) :
    abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar (constantEtaleSheaf B K hK A)
        ((geometricPointFiber B (Spec (.of K)) hK sbar).elementsMk V
          (galoisFiberAction B K hK sbar σ q))
        (ConcreteCategory.hom ((constantEtaleToSheafify B K hK A).app (op V)) a) =
      abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar (constantEtaleSheaf B K hK A)
        ((geometricPointFiber B (Spec (.of K)) hK sbar).elementsMk V q) (ConcreteCategory.hom ((constantEtaleToSheafify B K hK A).app (op V)) a) :=
  constantStalkIso_injective B K hK sbar A
    ((constantStalkIso_abelianEtaleStalkGerm B K hK sbar A V
      (galoisFiberAction B K hK sbar σ q) a).trans
        (constantStalkIso_abelianEtaleStalkGerm B K hK sbar A V q a).symm)

/-- **The absolute Galois group acts trivially on the Galois module of a constant sheaf.**  Every
element of the stalk is the germ of a constant section; the Galois action moves that germ to the
germ of the same constant section at the translated lift; and that germ does not depend on the
lift. -/
@[sga "4½ Arcata 2.4.5" "(a)"]
theorem etaleGaloisModule_constantEtaleSheaf_rho_apply
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (x : ((etaleGaloisModule.{u, u + 1} B K hK sbar
      (constantEtaleSheaf B K hK A)).obj.obj.V : _)) :
    ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
      (constantEtaleSheaf B K hK A)).obj.obj.ρ σ).asHom x = x := by
  obtain ⟨V, q, a, hx⟩ := exists_abelianEtaleStalkGerm_toSheafify B K hK sbar A
    (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar (constantEtaleSheaf B K hK A) x)
  have hxs : x = (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
      (constantEtaleSheaf B K hK A)).symm
        (abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
          (constantEtaleSheaf B K hK A) ((geometricPointFiber B (Spec (.of K)) hK sbar).elementsMk V q)
          (ConcreteCategory.hom ((constantEtaleToSheafify B K hK A).app (op V)) a)) :=
    ((etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
      (constantEtaleSheaf B K hK A)).symm_apply_apply x).symm.trans
        (congrArg (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
          (constantEtaleSheaf B K hK A)).symm hx)
  refine (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
    (constantEtaleSheaf B K hK A)).injective (Eq.trans ?_ hx.symm)
  exact ((congrArg (fun z : ((etaleGaloisModule.{u, u + 1} B K hK sbar
          (constantEtaleSheaf B K hK A)).obj.obj.V : _) =>
        etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar (constantEtaleSheaf B K hK A)
          (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
            (constantEtaleSheaf B K hK A)).obj.obj.ρ σ).asHom z)) hxs).trans
      (etaleGaloisModuleAddEquivStalk_rho_abelianEtaleStalkGerm.{u, u + 1} B K hK sbar
        (constantEtaleSheaf B K hK A) σ
        ((geometricPointFiber B (Spec (.of K)) hK sbar).elementsMk V q)
        (ConcreteCategory.hom ((constantEtaleToSheafify B K hK A).app (op V)) a))).trans
    (abelianEtaleStalkGerm_constant_galoisFiberAction B K hK sbar A σ V q a)

/-! ### The trivial Galois module -/

/-- The value of the constant sheaf as a discrete Galois module with trivial action. -/
abbrev constantGModule :
    ContinuousGModule.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) :=
  Stacks.GroupCohomology.trivialContinuousGModule
    (GeometricPoint.absoluteGaloisGroup sbar) A

/-- The same module in the abelian-group encoding of discrete Galois modules, which is the
encoding the stalk equivalence of Tag 04JQ produces. -/
abbrev constantGAddCommGrp :
    ContinuousGAddCommGrp.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) :=
  (continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
    (GeometricPoint.absoluteGaloisGroup sbar)).functor.obj (constantGModule K sbar A)

/-- The action on the trivial module is the identity. -/
theorem constantGAddCommGrp_rho (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    ((constantGAddCommGrp K sbar A).obj.obj.ρ σ).asHom = 𝟙 _ := rfl

/-- The abelian group of the Galois module of a constant sheaf, identified with the value of the
sheaf: the identification of Tag 04JQ followed by the stalk computation. -/
abbrev constantGaloisModuleIsoValue :
    ((etaleGaloisModule.{u, u + 1} B K hK sbar
        (constantEtaleSheaf B K hK A)).obj.obj.V : _) ≅ AddCommGrpCat.of A :=
  (abelianEtaleStalkEquivalenceIso.{u, u + 1} B K hK sbar).app
      (constantEtaleSheaf B K hK A) ≪≫
    constantStalkIso B K hK sbar A

/-- The identification is Galois equivariant, the action on the right being trivial: this is the
hypothesis `CategoryTheory.Action.mkIso` asks for. -/
@[sga "4½ Arcata 2.4.5" "more general"]
theorem constantGaloisModuleIsoValue_comm (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    ((etaleGaloisModule.{u, u + 1} B K hK sbar
          (constantEtaleSheaf B K hK A)).obj.obj.ρ σ).asHom ≫
        (constantGaloisModuleIsoValue B K hK sbar A).hom =
      (constantGaloisModuleIsoValue B K hK sbar A).hom ≫
        ((constantGAddCommGrp K sbar A).obj.obj.ρ σ).asHom := by
  refine Eq.trans ?_ (Category.comp_id (constantGaloisModuleIsoValue B K hK sbar A).hom).symm
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x =>
    congrArg (ConcreteCategory.hom (constantGaloisModuleIsoValue B K hK sbar A).hom)
      (etaleGaloisModule_constantEtaleSheaf_rho_apply B K hK sbar A σ x))

/-- The underlying action of `Gal(Kˢᵉᵖ/K)` on the stalk of a constant sheaf is trivial. -/
@[sga "4½ Arcata 2.4.5" "more general"]
def constantGaloisActionIso :
    (etaleGaloisModule.{u, u + 1} B K hK sbar
        (constantEtaleSheaf B K hK A)).obj.obj ≅
      (constantGAddCommGrp K sbar A).obj.obj :=
  Action.mkIso (constantGaloisModuleIsoValue B K hK sbar A)
    (constantGaloisModuleIsoValue_comm B K hK sbar A)

/-- The same isomorphism between the underlying continuous actions. -/
def constantGaloisContActionIso :
    (etaleGaloisModule.{u, u + 1} B K hK sbar (constantEtaleSheaf B K hK A)).obj ≅
      (constantGAddCommGrp K sbar A).obj :=
  ObjectProperty.isoMk _ (constantGaloisActionIso B K hK sbar A)

/-- **The Galois module of a constant sheaf is its value with trivial action**, in the
abelian-group encoding of discrete Galois modules. -/
@[sga "4½ Arcata 2.4.5" "more general"]
def constantGaloisModuleIso :
    etaleGaloisModule.{u, u + 1} B K hK sbar (constantEtaleSheaf B K hK A) ≅
      constantGAddCommGrp K sbar A :=
  ObjectProperty.isoMk _ (constantGaloisContActionIso B K hK sbar A)

/-- **Stacks Project, Tag 03QV, clause (1).**  Under the stalk equivalence of Tag 04JQ, the
constant abelian sheaf on the small étale site of `Spec K` corresponds to its value with the
trivial action of the absolute Galois group. -/
@[sga "4½ Arcata 2.4.5" "more general"]
def constantContinuousGModuleIso :
    (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
        (constantEtaleSheaf B K hK A) ≅ constantGModule K sbar A :=
  (continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar)).inverse.mapIso
      (constantGaloisModuleIso B K hK sbar A) ≪≫
    ((continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar)).unitIso.app (constantGModule K sbar A)).symm

end AlgebraicGeometry

end
