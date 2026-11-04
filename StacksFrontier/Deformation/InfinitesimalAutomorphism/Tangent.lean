module

public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.Elements
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Functor
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.TangentSpace.Predeformation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tangent space of the automorphism functor (Stacks 06JV)

Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ`, let `x` be an object of `𝓕` over
`A`, and let `x₀` be a pushforward of `x` to the special fibre. The automorphism functor
`Aut(x) : 𝒞_A → Sets` of Tag 06JT, localized at the identity of `x₀`, has a tangent space
at that point. This file builds that tangent space and identifies it, on representatives,
with the group of infinitesimal automorphisms of the dual-number pushforward of `x`.

The identification is the "unwinding of definitions" step of the Stacks proof of Tag 06JV:
an object of the dual-number fibre of the localization `Aut(x)_{id}` is an automorphism of
`f_* x` for `f : A → k[ε]` together with the datum that it becomes the identity after
reduction, and two such objects are isomorphic exactly when the automorphisms agree. The
morphism to the residue-field object of `𝒞_A` is unique, which is what makes both the
compatibility datum and the comparison of two representatives automatic.

## Main definitions

* `Deformation.residueAlgebra`: the residue action of an object of `𝒞_Λ` on `k`.
* `Deformation.algebrasUnder`: the comparison `𝒞_A ⥤ Under A`.
* `Deformation.residueMorphism`: the canonical map to the residue-field object.
* `Deformation.infinitesimalAutomorphismKernel`: automorphisms of a chosen pushforward that
  become trivial after a further pushforward.
* `Deformation.automorphismFunctorOverBase`: the automorphism functor of `x`, read on `𝒞_A`.
* `Deformation.localizedAutomorphismFunctorTangent`: its tangent space at the identity.
* `Deformation.tangentReduction`, `Deformation.tangentScaling`: reduction of the dual
  numbers and scaling of the infinitesimal coordinate, as arrows under `A`.
* `Deformation.localizedTangentEquivKernel`: the resulting identification with the kernel.

## Main results

* `Deformation.hom_residueFieldObject_ext`: any two morphisms to the residue-field object of
  `𝒞_Λ` agree.
* `Deformation.categoryOfElements_projection_isCofibered`: the category of elements of a
  covariant set-valued functor is cofibered in groupoids.
* `Deformation.localizedTangentEquivKernelData`: the identification of the localized tangent
  space with the infinitesimal automorphisms, pinned on every representative.

## Implementation notes

The automorphism functor is reindexed from the undercategory to `𝒞_A` using the residue
action of `A` on `k`. Its tangent space is literally Tag 06IK's `tangentSpaceAtPoint` at the
identity in the category of elements; there is no additional fixed-reduction subcategory or
quotient. The identification with the kernel of reduction is therefore specified on
representatives of that tangent space, and the specification determines it, since every
class has a representative.

`categoryOfElements_projection_isCofibered` repeats the private
`categoryOfElements_π_isCofibered` of `StacksFrontier.Deformation.Predeformation.Basic`; it is
restated here because the statement of the tangent space needs it.

## References

* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
-/

@[expose] public section

namespace Deformation

open CategoryTheory IsLocalRing

universe u v w u₁ v₁

/-- Infinitesimal fibre automorphisms, namely those trivial after reduction. -/
public abbrev infinitesimalAutomorphismKernel
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x : F} (P : ChosenPushforwardsAt p x)
    {Uε U₀ : Under (p.obj x)} (r : Uε ⟶ U₀) : Type _ :=
  ↥(MonoidHom.ker (P.transportAutHom r))

/-- The category of elements of a covariant set-valued functor is cofibered in groupoids. -/
@[sga "7 VI 1.1(a)"]
public theorem categoryOfElements_projection_isCofibered
    {C : Type u} [Category.{v} C] (F : C ⥤ Type w) :
    IsCofiberedInGroupoids (CategoryOfElements.π F) := by
  show Functor.IsFiberedInGroupoids (CategoryOfElements.π F).op
  constructor
  · intro V U f y hy
    rcases V with ⟨V⟩
    rcases U with ⟨U⟩
    rcases y with ⟨y⟩
    change Opposite.op ((CategoryOfElements.π F).obj y) = Opposite.op U at hy
    cases hy
    let z := F.elementsMk V (F.map f.unop y.2)
    let g : y ⟶ z := CategoryOfElements.homMk y z f.unop rfl
    refine ⟨Opposite.op z, g.op, ?_⟩
    have hmap : (CategoryOfElements.π F).op.map g.op = f := by
      apply Quiver.Hom.opEquiv.injective
      simp [g, CategoryOfElements.π]
    rw [← hmap]
    infer_instance
  · intro a b c φ ψ f hf
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    have hbase : φ.unop.val ≫ f.unop = ψ.unop.val := by
      simpa using congrArg Quiver.Hom.unop hf
    let g : b ⟶ c := CategoryOfElements.homMk b c f.unop (by
      calc
        F.map f.unop b.2 = F.map f.unop (F.map φ.unop.val a.2) := by
          rw [CategoryOfElements.map_snd]
        _ = F.map (φ.unop.val ≫ f.unop) a.2 := by rw [Functor.map_comp_apply]
        _ = F.map ψ.unop.val a.2 := by rw [hbase]
        _ = c.2 := CategoryOfElements.map_snd ψ.unop)
    refine ⟨g.op, ⟨?_, ?_⟩, ?_⟩
    · apply Quiver.Hom.opEquiv.injective
      simp [g, CategoryOfElements.π]
    · apply Quiver.Hom.opEquiv.symm.injective
      apply CategoryOfElements.ext
      exact hbase
    · intro χ hχ
      apply Quiver.Hom.opEquiv.symm.injective
      apply CategoryOfElements.ext
      exact congrArg Quiver.Hom.unop hχ.1

section OverBase

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The residue action of an Artinian algebra on the fixed residue field. -/
@[instance_reducible]
public noncomputable def residueAlgebra
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) : Algebra A k :=
  (A.residueEquiv.toRingEquiv.toRingHom.comp (residue A)).toAlgebra

/-- Restriction from `A`-algebras to algebras under `A` in `𝒞_Λ`. -/
public noncomputable def algebrasUnder
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    letI := residueAlgebra A
    ArtinianLocalAlgCat.{v, v, w} A k ⥤ Under A := by
  let := residueAlgebra A
  let : IsScalarTower Λ A k := IsScalarTower.of_algebraMap_eq' (by
    ext t
    exact (A.residueEquiv.commutes t).symm)
  let obj (B : ArtinianLocalAlgCat.{v, v, w} A k) :
      ArtinianLocalAlgCat.{u, v, w} Λ k :=
    let : Algebra Λ B := ((algebraMap A B).comp (algebraMap Λ A)).toAlgebra
    let : IsScalarTower Λ A B := IsScalarTower.of_algebraMap_eq' rfl
    { carrier := B
      residueEquiv := B.residueEquiv.restrictScalars Λ }
  let arrow (B : ArtinianLocalAlgCat.{v, v, w} A k) : A ⟶ obj B :=
    { hom := { toRingHom := algebraMap A B, commutes' := fun _ => rfl }
      isLocal := by
        refine ⟨fun a ha => ?_⟩
        apply (residue_ne_zero_iff_isUnit a).mp
        have hb := (residue_ne_zero_iff_isUnit (algebraMap A B a)).mpr ha
        have he : B.residueEquiv (residue B (algebraMap A B a)) =
            A.residueEquiv (residue A a) := B.residueEquiv.commutes a
        intro hz
        apply hb
        apply B.residueEquiv.injective
        simpa [hz] using he
      residue_comm := fun a => B.residueEquiv.commutes a }
  exact
    { obj := fun B => Under.mk (arrow B)
      map := fun {B D} f => Under.homMk
        { hom := { toRingHom := f.hom.toRingHom
                   commutes' := fun t => f.hom.commutes (algebraMap Λ A t) }
          isLocal := f.isLocal
          residue_comm := fun a => f.residue_comm a }
        (by ext a; exact f.hom.commutes a)
      map_id := fun B => by ext; rfl
      map_comp := fun f g => by apply Under.UnderMorphism.ext; ext; rfl }

/-- The canonical map of an Artinian local algebra to its fixed residue field. -/
public noncomputable def residueMorphism
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    A ⟶ residueFieldObject.{u, v, w} Λ k where
  hom := (ULift.algEquiv (R := Λ) (A := k)).symm.toAlgHom.comp
    (A.residueEquiv.toAlgHom.comp (IsScalarTower.toAlgHom Λ A (ResidueField A)))
  isLocal := by
    refine ⟨fun a ha => (residue_ne_zero_iff_isUnit a).mp ?_⟩
    intro hz
    apply ha.ne_zero
    change ULift.up (A.residueEquiv (residue A a)) = 0
    simp only [hz, map_zero]
    rfl
  residue_comm := fun _ => rfl

/-- Every morphism to the residue-field object is the canonical one. -/
public theorem eq_residueMorphism
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A ⟶ residueFieldObject.{u, v, w} Λ k) :
    f = residueMorphism A := by
  apply ArtinianLocalAlgCat.hom_ext
  ext a
  have hres : residue (residueFieldObject.{u, v, w} Λ k) (f.hom a) =
      residue (residueFieldObject.{u, v, w} Λ k) ((residueMorphism A).hom a) :=
    (residueFieldObject.{u, v, w} Λ k).residueEquiv.injective
      ((f.residue_comm a).trans ((residueMorphism A).residue_comm a).symm)
  have hzero : residue (residueFieldObject.{u, v, w} Λ k)
      (f.hom a - (residueMorphism A).hom a) = 0 := by
    rw [map_sub, hres, sub_self]
  have hmax : maximalIdeal ↑(residueFieldObject.{u, v, w} Λ k) = ⊥ := by
    show maximalIdeal (ULift.{v} k) = ⊥
    exact maximalIdeal_eq_bot
  have hz : f.hom a - (residueMorphism A).hom a = 0 := by
    simpa [hmax] using (residue_eq_zero_iff _).mp hzero
  exact sub_eq_zero.mp hz

/-- Any two morphisms to the residue-field object agree. -/
public theorem hom_residueFieldObject_ext
    {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f g : A ⟶ residueFieldObject.{u, v, w} Λ k) : f = g :=
  (eq_residueMorphism f).trans (eq_residueMorphism g).symm

end OverBase

/-! ### Transport of functor values along equalities of objects -/

section EqToHom

open CategoryTheory

/-- If two values of a set-valued functor agree after transport to a common object, then one
is the transport of the other along the composite identification. -/
private theorem map_eqToHom_trans_apply {C : Type*} [Category C] (G : C ⥤ Type*)
    {A B D : C} (h : A = B) (h' : D = B) (a : G.obj A) (b : G.obj D)
    (hab : G.map (eqToHom h) a = G.map (eqToHom h') b) :
    G.map (eqToHom (h.trans h'.symm)) a = b := by
  subst h'
  subst h
  simpa using hab

/-- Conversely, if one value is the transport of the other along the composite
identification, then the two agree after transport to the common object. -/
private theorem map_eqToHom_apply_eq {C : Type*} [Category C] (G : C ⥤ Type*)
    {A B D : C} (h : A = B) (h' : D = B) (a : G.obj A) (b : G.obj D)
    (hab : G.map (eqToHom (h.trans h'.symm)) a = b) :
    G.map (eqToHom h) a = G.map (eqToHom h') b := by
  subst h'
  subst h
  simpa using hab

end EqToHom
section Tangent

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
  {x : F} (P : ChosenPushforwardsAt p x)

/-- The automorphism functor, on the source's category `𝒞_A`. -/
public noncomputable abbrev automorphismFunctorOverBase :
    letI := residueAlgebra (p.obj x)
    ArtinianLocalAlgCat.{max v w, max v w, w} (p.obj x) k ⥤ Type v₁ :=
  algebrasUnder (p.obj x) ⋙ automorphismFunctor P

/-- The identity point of the automorphism functor over the residue field. -/
public noncomputable def identityPoint :
    letI := residueAlgebra (p.obj x)
    (CategoryOfElements.π (automorphismFunctorOverBase P)).Fiber
      (residueFieldObject.{max v w, v, w} (p.obj x) k) :=
  ⟨⟨_, Iso.refl _⟩, rfl⟩

/-- The accepted tangent-space construction, applied directly over `𝒞_A` at the identity. -/
public noncomputable abbrev localizedAutomorphismFunctorTangent : Type _ :=
  let := residueAlgebra (p.obj x)
  tangentSpaceAtPoint
    (CategoryOfElements.π (automorphismFunctorOverBase P))
    (categoryOfElements_projection_isCofibered _) (identityPoint P)

/-- The residue-field object under the base of `x`. -/
public noncomputable abbrev specialFibreUnder : Under (p.obj x) :=
  let := residueAlgebra (p.obj x)
  (algebrasUnder (p.obj x)).obj
    (residueFieldObject.{max v w, v, w} (p.obj x) k)

/-- The canonical dual numbers under the base of `x`. -/
public noncomputable abbrev dualNumbersUnder : Under (p.obj x) :=
  let := residueAlgebra (p.obj x)
  (algebrasUnder (p.obj x)).obj
    (artinianDualNumbers.{max v w, w, v} (p.obj x) k)

/-- Reduction from the canonical dual numbers to the residue field. -/
public noncomputable def tangentReduction : dualNumbersUnder (p := p) (x := x) ⟶
    specialFibreUnder (p := p) (x := x) :=
  let := residueAlgebra (p.obj x)
  (algebrasUnder (p.obj x)).map (residueMorphism _)

/-- The slice category whose associated tangent space is used at the identity. -/
public noncomputable abbrev localizedAutomorphismCategory :
    letI := residueAlgebra (p.obj x)
    BasedCategory (ArtinianLocalAlgCat.{max v w, max v w, w} (p.obj x) k) :=
  BasedCategory.ofFunctor (objectsOverFunctor
    (CategoryOfElements.π (automorphismFunctorOverBase P)) (identityPoint P).1)

/-- The automorphism attached to the identity point is the identity automorphism. -/
private theorem identityPoint_snd :
    letI := residueAlgebra (p.obj x)
    (identityPoint P).1.2 =
      (1 : Aut (P.obj (specialFibreUnder (p := p) (x := x)))) := rfl

/-- The slice category at the identity is a predeformation category. -/
public theorem isPredeformationCategory_localizedAutomorphismCategory :
    letI := residueAlgebra (p.obj x)
    IsPredeformationCategory (localizedAutomorphismCategory P).p := by
  let := residueAlgebra (p.obj x)
  exact isPredeformationCategory_objectsOverFunctor
    (CategoryOfElements.π (automorphismFunctorOverBase P))
    (categoryOfElements_projection_isCofibered _) (identityPoint P)

/-- A morphism of representatives of the dual-number fibre is the canonical `eqToHom` on the
underlying objects of `𝒞_A`. -/
private theorem localizedAutomorphismFiber_hom_left_val
    (z z' : letI := residueAlgebra (p.obj x)
      (localizedAutomorphismCategory P).p.Fiber
        (artinianDualNumbers.{max v w, w, v} (p.obj x) k)) (f : z ⟶ z') :
    letI := residueAlgebra (p.obj x)
    f.1.left.val = eqToHom (z.2.trans z'.2.symm) := by
  let := residueAlgebra (p.obj x)
  let _ := f.2
  have h : f.1.left.val = eqToHom z.2 ≫ 𝟙 (artinianDualNumbers.{max v w, w, v} (p.obj x) k) ≫
      eqToHom z'.2.symm :=
    IsHomLift.fac' (localizedAutomorphismCategory P).p
      (𝟙 (artinianDualNumbers.{max v w, w, v} (p.obj x) k))
      (Functor.Fiber.fiberInclusion.map f)
  rw [h, Category.id_comp, eqToHom_trans]

/-- Fibres of the localized projection over the dual numbers are thin: the compatibility
datum of a representative is determined, so any two morphisms between representatives
agree. -/
private theorem localizedAutomorphismFiber_hom_ext
    (z z' : letI := residueAlgebra (p.obj x)
      (localizedAutomorphismCategory P).p.Fiber
        (artinianDualNumbers.{max v w, w, v} (p.obj x) k)) (f g : z ⟶ z') : f = g := by
  let := residueAlgebra (p.obj x)
  apply Functor.Fiber.hom_ext
  apply Over.OverMorphism.ext
  apply CategoryOfElements.ext
  exact (localizedAutomorphismFiber_hom_left_val P z z' f).trans
    (localizedAutomorphismFiber_hom_left_val P z z' g).symm

/-- The automorphism read off a representative of the dual-number fibre becomes trivial
after reduction, so it lies in the kernel. -/
private theorem localizedAutomorphism_mem_ker
    (y : letI := residueAlgebra (p.obj x)
      (localizedAutomorphismCategory P).p.Fiber
        (artinianDualNumbers.{max v w, w, v} (p.obj x) k)) :
    letI := residueAlgebra (p.obj x)
    (automorphismFunctorOverBase P).map (eqToHom y.2) y.1.left.2 ∈
      MonoidHom.ker (P.transportAutHom (tangentReduction (p := p) (x := x))) := by
  let := residueAlgebra (p.obj x)
  have hhom : y.1.hom.val = eqToHom y.2 ≫
      residueMorphism (artinianDualNumbers.{max v w, w, v} (p.obj x) k) :=
    hom_residueFieldObject_ext _ _
  have e1 : (automorphismFunctorOverBase P).map
        (eqToHom y.2 ≫
          residueMorphism (artinianDualNumbers.{max v w, w, v} (p.obj x) k))
        y.1.left.2 =
      (automorphismFunctorOverBase P).map y.1.hom.val y.1.left.2 := by
    rw [hhom]
    rfl
  have e2 : (automorphismFunctorOverBase P).map
        (eqToHom y.2 ≫
          residueMorphism (artinianDualNumbers.{max v w, w, v} (p.obj x) k))
        y.1.left.2 =
      (automorphismFunctorOverBase P).map
        (residueMorphism (artinianDualNumbers.{max v w, w, v} (p.obj x) k))
        ((automorphismFunctorOverBase P).map (eqToHom y.2) y.1.left.2) :=
    Functor.map_comp_apply (automorphismFunctorOverBase P) _ _ _
  exact e2.symm.trans
    (e1.trans ((CategoryOfElements.map_snd y.1.hom).trans (identityPoint_snd P)))

/-- The morphism of representatives built from an agreement of their automorphisms. -/
private noncomputable def localizedAutomorphismFiberHom
    (z z' : letI := residueAlgebra (p.obj x)
      (localizedAutomorphismCategory P).p.Fiber
        (artinianDualNumbers.{max v w, w, v} (p.obj x) k))
    (hzz : letI := residueAlgebra (p.obj x)
      (automorphismFunctorOverBase P).map (eqToHom z.2) z.1.left.2 =
        (automorphismFunctorOverBase P).map (eqToHom z'.2) z'.1.left.2) :
    z ⟶ z' := by
  let := residueAlgebra (p.obj x)
  refine ⟨Over.homMk (CategoryOfElements.homMk z.1.left z'.1.left
    (eqToHom (z.2.trans z'.2.symm))
    (map_eqToHom_trans_apply (automorphismFunctorOverBase P) z.2 z'.2 _ _ hzz)) ?_, ?_⟩
  · apply CategoryOfElements.ext
    exact hom_residueFieldObject_ext _ _
  · refine IsHomLift.of_fac' (localizedAutomorphismCategory P).p
      (𝟙 (artinianDualNumbers.{max v w, w, v} (p.obj x) k)) _ z.2 z'.2 ?_
    change eqToHom (z.2.trans z'.2.symm) =
      eqToHom z.2 ≫ 𝟙 (artinianDualNumbers.{max v w, w, v} (p.obj x) k) ≫ eqToHom z'.2.symm
    simp

/-- Representatives carrying the same automorphism are isomorphic. -/
private theorem localizedAutomorphismFiber_nonempty_iso
    (z z' : letI := residueAlgebra (p.obj x)
      (localizedAutomorphismCategory P).p.Fiber
        (artinianDualNumbers.{max v w, w, v} (p.obj x) k))
    (hzz : letI := residueAlgebra (p.obj x)
      (automorphismFunctorOverBase P).map (eqToHom z.2) z.1.left.2 =
        (automorphismFunctorOverBase P).map (eqToHom z'.2) z'.1.left.2) :
    Nonempty (z ≅ z') :=
  ⟨⟨localizedAutomorphismFiberHom P z z' hzz,
    localizedAutomorphismFiberHom P z' z hzz.symm,
    localizedAutomorphismFiber_hom_ext P _ _ _ _,
    localizedAutomorphismFiber_hom_ext P _ _ _ _⟩⟩

/-- Isomorphic representatives carry the same automorphism. -/
private theorem localizedAutomorphism_map_eqToHom_eq_of_iso
    (z z' : letI := residueAlgebra (p.obj x)
      (localizedAutomorphismCategory P).p.Fiber
        (artinianDualNumbers.{max v w, w, v} (p.obj x) k)) (e : z ≅ z') :
    letI := residueAlgebra (p.obj x)
    (automorphismFunctorOverBase P).map (eqToHom z.2) z.1.left.2 =
      (automorphismFunctorOverBase P).map (eqToHom z'.2) z'.1.left.2 := by
  let := residueAlgebra (p.obj x)
  have hb2 := localizedAutomorphismFiber_hom_left_val P z z' e.hom
  refine map_eqToHom_apply_eq (automorphismFunctorOverBase P) z.2 z'.2 _ _ ?_
  rw [← hb2]
  exact CategoryOfElements.map_snd _

/-- Every element of the kernel of reduction is read off some representative. -/
private theorem exists_localizedAutomorphismFiber
    (α : letI := residueAlgebra (p.obj x)
      Aut (P.obj (dualNumbersUnder (p := p) (x := x))))
    (hα : letI := residueAlgebra (p.obj x)
      α ∈ MonoidHom.ker (P.transportAutHom (tangentReduction (p := p) (x := x)))) :
    letI := residueAlgebra (p.obj x)
    ∃ z : (localizedAutomorphismCategory P).p.Fiber
      (artinianDualNumbers.{max v w, w, v} (p.obj x) k),
      (automorphismFunctorOverBase P).map (eqToHom z.2) z.1.left.2 = α := by
  let := residueAlgebra (p.obj x)
  have hcond : (automorphismFunctorOverBase P).map
      (residueMorphism (artinianDualNumbers.{max v w, w, v} (p.obj x) k)) α =
      (identityPoint P).1.2 := by
    rw [identityPoint_snd P]
    exact hα
  refine ⟨⟨Over.mk (CategoryOfElements.homMk
    ((automorphismFunctorOverBase P).elementsMk
      (artinianDualNumbers.{max v w, w, v} (p.obj x) k) α)
    (identityPoint P).1
    (residueMorphism (artinianDualNumbers.{max v w, w, v} (p.obj x) k)) hcond), rfl⟩, ?_⟩
  show (automorphismFunctorOverBase P).map (eqToHom rfl) α = α
  rw [eqToHom_refl]
  exact Functor.map_id_apply _ _ _

/-- The equivalence between isomorphism classes of representatives and the kernel of
reduction, pinned on representatives. -/
public theorem exists_localizedAutomorphismQuotientEquiv :
    letI := residueAlgebra (p.obj x)
    ∃ e : Quotient (isIsomorphicSetoid
        ((localizedAutomorphismCategory P).p.Fiber
          (artinianDualNumbers.{max v w, w, v} (p.obj x) k))) ≃
        infinitesimalAutomorphismKernel P (tangentReduction (p := p) (x := x)),
      ∀ z, (e (Quotient.mk _ z)).1 =
        (automorphismFunctorOverBase P).map (eqToHom z.2) z.1.left.2 := by
  let := residueAlgebra (p.obj x)
  refine ⟨{
      toFun := Quotient.lift
          (fun z => (⟨(automorphismFunctorOverBase P).map (eqToHom z.2) z.1.left.2,
            localizedAutomorphism_mem_ker P z⟩ :
              infinitesimalAutomorphismKernel P (tangentReduction (p := p) (x := x))))
          (fun z z' h => Subtype.ext
            (localizedAutomorphism_map_eqToHom_eq_of_iso P z z'
              ((Functor.isIsomorphicSetoid_r_iff z z').1 h).some)),
      invFun := fun α => Quotient.mk _
        (Classical.choose (exists_localizedAutomorphismFiber P α.1 α.2)),
      left_inv := ?_,
      right_inv := fun α => Subtype.ext (Classical.choose_spec
        (exists_localizedAutomorphismFiber P α.1 α.2)) }, fun z => rfl⟩
  · intro c
    induction c using Quotient.ind with
    | _ z =>
      exact Quotient.sound ((Functor.isIsomorphicSetoid_r_iff _ _).2
        (localizedAutomorphismFiber_nonempty_iso P _ _ (Classical.choose_spec
          (exists_localizedAutomorphismFiber P _ (localizedAutomorphism_mem_ker P z)))))

-- Unfolding the slice and isomorphism-class functors during elaboration is expensive, so
-- every step of the identification is its own declaration.
/-- The canonical identification with the kernel, specified on every representative
of the accepted tangent space. -/
public noncomputable def localizedTangentEquivKernelData :
    letI := residueAlgebra (p.obj x)
    let hpre := isPredeformationCategory_localizedAutomorphismCategory P
    { E : localizedAutomorphismFunctorTangent P ≃
        infinitesimalAutomorphismKernel P (tangentReduction (p := p) (x := x)) //
      ∀ y : (localizedAutomorphismCategory P).p.Fiber
          (artinianDualNumbers.{max v w, w, v} (p.obj x) k),
        (E (classOf (localizedAutomorphismCategory P) hpre.cofibered y)).1 =
          (automorphismFunctorOverBase P).map (eqToHom y.2) y.1.left.2 } := by
  let := residueAlgebra (p.obj x)
  have hex := exists_localizedAutomorphismQuotientEquiv P
  refine ⟨(Equiv.cast (isomorphismClasses_obj (localizedAutomorphismCategory P)
    (isPredeformationCategory_localizedAutomorphismCategory P).cofibered
    (artinianDualNumbers.{max v w, w, v} (p.obj x) k))).trans hex.choose, fun y => ?_⟩
  exact (congrArg (fun t => (hex.choose t).1)
    (classOf_eq (localizedAutomorphismCategory P)
      (isPredeformationCategory_localizedAutomorphismCategory P).cofibered
      y)).trans (hex.choose_spec y)

/-- The representative-pinned equivalence with infinitesimal automorphisms. -/
public noncomputable abbrev localizedTangentEquivKernel :
    localizedAutomorphismFunctorTangent P ≃
      infinitesimalAutomorphismKernel P (tangentReduction (p := p) (x := x)) :=
  (localizedTangentEquivKernelData P).1

/-- Scaling the infinitesimal coordinate by an element of the fixed residue field. -/
public noncomputable def tangentScaling (c : k) :
    dualNumbersUnder (p := p) (x := x) ⟶ dualNumbersUnder (p := p) (x := x) :=
  let := residueAlgebra (p.obj x)
  (algebrasUnder (p.obj x)).map ((squareZeroExtensionArtinian (p.obj x) k).map
    (FGModuleCat.ofHom (c • LinearMap.id : ULift.{v} k →ₗ[k] ULift.{v} k)))

/-- **The underlying ring map of `Deformation.tangentScaling` is `TrivSqZeroExt.map (c • id)`.**
Restriction from algebras over the base to algebras under it changes neither the carrier nor the
underlying map, and the square-zero extension functor sends a map of coefficient modules to
`TrivSqZeroExt.map` of it, so the scaling is that map of the rank-one coefficient module read on
the dual numbers. -/
public theorem tangentScaling_right_hom (c : k)
    (y : (dualNumbersUnder (p := p) (x := x)).right) :
    (tangentScaling (p := p) (x := x) c).right.hom y =
      TrivSqZeroExt.map (R' := k)
        (c • LinearMap.id : ULift.{v} k →ₗ[k] ULift.{v} k) y := rfl

/-- **`Deformation.tangentScaling` does not move the residue coordinate.** -/
public theorem tangentScaling_right_hom_fst (c : k)
    (y : (dualNumbersUnder (p := p) (x := x)).right) :
    TrivSqZeroExt.fst ((tangentScaling (p := p) (x := x) c).right.hom y) =
      TrivSqZeroExt.fst y := by
  rw [tangentScaling_right_hom]
  exact TrivSqZeroExt.fst_map _ _

/-- **`Deformation.tangentScaling` multiplies the infinitesimal coordinate by `c`.** This is the
coordinate computation behind the name: on the dual numbers `k[ε]` under the base, the scaling
attached to `c : k` fixes the residue coordinate by
`Deformation.tangentScaling_right_hom_fst` and sends `ε` to `c • ε`.

The scalar action of the tangent space of an automorphism functor is implemented by transport
along this map, by `Deformation.naturalLocalizedTangentModule_spec` (2), so this is the fact that
any computation of that scalar action in terms of a derivation has to start from. -/
public theorem tangentScaling_right_hom_snd (c : k)
    (y : (dualNumbersUnder (p := p) (x := x)).right) :
    TrivSqZeroExt.snd ((tangentScaling (p := p) (x := x) c).right.hom y) =
      c • TrivSqZeroExt.snd y := by
  rw [tangentScaling_right_hom]
  exact TrivSqZeroExt.snd_map _ _

end Tangent

end Deformation

end
