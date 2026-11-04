module

public import Mathlib.Algebra.Module.Torsion.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Lift
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# The kernel of a small extension, and functoriality of lifts

Two pieces of basic structure attached to lifts of an object along a morphism of Artinian
local algebras.

First, if `f : A' → A` is a morphism of Artinian local algebras whose kernel is annihilated by
the maximal ideal of `A'`, then that kernel is a vector space over the fixed residue field: the
annihilation hypothesis makes it a module over the residue field of `A'`, and the structural
identification of that residue field with `k` transports the structure to `k`.

Second, a morphism of categories over the base carries lifting arrows to lifting arrows, hence
induces a functor between the categories of lifts and a map on their isomorphism classes.

## Main definitions

* `Deformation.kernelModule`: the kernel of such a morphism as a `k`-vector space.
* `Deformation.liftFunctor`: the functor on categories of lifts induced by a based functor.
* `Deformation.mapLiftClasses`: the induced map on isomorphism classes of lifts.

## Main results

* `Deformation.homToResidueFieldObject_unique`: morphisms into the residue-field object are
  unique.
* `Deformation.nonempty_iso_of_liftFactorizations`: two lifts receiving a factorization of one
  lift over the same morphism are isomorphic.

## Implementation notes

`kernelModule` is produced as a bare `Module` instance rather than installed globally: which
module structure is meant depends on the annihilation hypothesis, which is not part of the
data of `f`.

## References

* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
* [Stacks Project, Tag 06JJ](https://stacks.math.columbia.edu/tag/06JJ)
-/

@[expose] public section

namespace Deformation

/-! ### The kernel of a small extension as a vector space over the residue field -/

section
open CategoryTheory IsLocalRing
universe u v w

/-- The kernel of a morphism of Artinian local algebras annihilated by the maximal ideal of
the source, viewed as a vector space over the specified residue field. -/
@[instance_reducible]
public noncomputable def kernelModule
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0) :
    Module k (RingHom.ker f.hom.toRingHom) := by
  letI : Module (ResidueField A') (RingHom.ker f.hom.toRingHom) :=
    Module.IsTorsionBySet.module fun i a => Subtype.ext (hann a.1 a.2 i)
  exact Module.compHom _ A'.residueEquiv.symm.toRingHom

/-- An element of the kernel of a morphism of Artinian local algebras lies in the maximal
ideal of the source, the morphism being local. -/
public lemma kernel_mem_maximalIdeal
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A' ⟶ A)
    (i : RingHom.ker f.hom.toRingHom) :
    (i : A') ∈ maximalIdeal A' := by
  have : IsLocalHom f.hom.toRingHom := f.isLocal
  rw [← maximalIdeal_comap f.hom.toRingHom]
  show f.hom.toRingHom (i : A') ∈ maximalIdeal A
  rw [RingHom.mem_ker.mp i.2]
  exact zero_mem _

end

/-! ### Morphisms into the residue-field object -/

section
open CategoryTheory IsLocalRing
universe u v w

/-- Any two morphisms of `𝒞_Λ` with target the residue-field object agree: the residue map of
the residue-field object is injective, and every morphism of `𝒞_Λ` is compatible with the
structural residue-field identifications. -/
public lemma homToResidueFieldObject_unique
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {X : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (g h : X ⟶ residueFieldObject.{u, v, w} Λ k) : g = h := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  have hinj : Function.Injective
      (residue (residueFieldObject.{u, v, w} Λ k)) := by
    apply (RingHom.injective_iff_ker_eq_bot _).2
    rw [ker_residue]
    show maximalIdeal (ULift.{v} k) = ⊥
    exact maximalIdeal_eq_bot
  exact hinj <| (residueFieldObject.{u, v, w} Λ k).residueEquiv.injective <|
    (g.residue_comm a).trans (h.residue_comm a).symm

end

/-! ### Lifts in a category cofibered in groupoids -/

section
open CategoryTheory
universe u v uF vF

/-- Two lifts of `x` along `f` that both receive a factorization of one lift of `x` along
`g ≫ f`, over `g`, are isomorphic. -/
public lemma nonempty_iso_of_liftFactorizations
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    {A₀ A₁ A : C} (g : A₀ ⟶ A₁) (f : A₁ ⟶ A) (x : p.Fiber A)
    (z : Lift p (g ≫ f) x) (a b : Lift p f x)
    (φ : z.obj ⟶ a.obj) (ψ : z.obj ⟶ b.obj)
    (hφ : p.IsHomLift g φ) (hψ : p.IsHomLift g ψ)
    (hfacφ : φ ≫ a.hom = z.hom) (hfacψ : ψ ≫ b.hom = z.hom) :
    Nonempty (a ≅ b) := by
  let : p.IsHomLift g φ := hφ
  let : p.IsHomLift g ψ := hψ
  have ha := CategoryTheory.IsHomLift.codomain_eq p g φ
  have hb := CategoryTheory.IsHomLift.codomain_eq p g ψ
  let q : p.obj a.obj ⟶ p.obj b.obj := eqToHom ha ≫ eqToHom hb.symm
  have hcomm : p.map φ ≫ q = p.map ψ := by
    rw [CategoryTheory.IsHomLift.fac' p g φ,
      CategoryTheory.IsHomLift.fac' p g ψ]
    simp [q, Category.assoc]
  obtain ⟨h, ⟨hbase, htri⟩, _⟩ := existsUnique_factor_of_isHomLift hp φ ψ q hcomm
  have hh : p.IsHomLift (𝟙 A₁) h := by
    apply CategoryTheory.IsHomLift.of_fac' p (𝟙 A₁) h ha hb
    simpa [q] using hbase
  let : p.IsHomLift (𝟙 A₁) h := hh
  let : p.IsStronglyCocartesian g φ :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp g φ hφ
  have hfac : h ≫ b.hom = a.hom := by
    apply Functor.IsStronglyCocartesian.ext p g φ f
    calc
      φ ≫ (h ≫ b.hom) = (φ ≫ h) ≫ b.hom := (Category.assoc _ _ _).symm
      _ = z.hom := by rw [htri, hfacψ]
      _ = φ ≫ a.hom := hfacφ.symm
  let l : a ⟶ b := ⟨h, hh, hfac⟩
  have : IsIso l := isIso_liftHom hp l
  exact ⟨asIso l⟩

end

/-! ### Functoriality of lifts along a morphism over the base -/

section
open CategoryTheory IsLocalRing
universe u w uF vF uG vG

/-- A based functor takes a lifting arrow to its image lifting arrow. -/
public def liftFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : A' ⟶ A)
    (x : 𝓕.p.Fiber A) :
    Lift 𝓕.p f x ⥤ Lift 𝓖.p f ((fiberFunctor φ A).obj x) where
  obj a :=
    { obj := φ.obj a.obj
      hom := φ.map a.hom
      isHomLift := by
        let := a.isHomLift
        exact φ.preserves_isHomLift f a.hom }
  map g :=
    { hom := φ.map g.hom
      isHomLift := by
        let := g.isHomLift
        exact φ.preserves_isHomLift (𝟙 A') g.hom
      fac := by
        change φ.map g.hom ≫ φ.map _ = φ.map _
        exact (φ.map_comp g.hom _).symm.trans (congrArg φ.map g.fac) }
  map_id a := Lift.Hom.ext (φ.map_id a.obj)
  map_comp g h := Lift.Hom.ext (φ.map_comp g.hom h.hom)

/-- The map on isomorphism classes of lifts induced by a based functor. -/
public def mapLiftClasses
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : A' ⟶ A)
    (x : 𝓕.p.Fiber A) :
    LiftClasses 𝓕.p f x → LiftClasses 𝓖.p f ((fiberFunctor φ A).obj x) :=
  (ThinSkeleton.map (liftFunctor φ f x)).obj

end

end Deformation
