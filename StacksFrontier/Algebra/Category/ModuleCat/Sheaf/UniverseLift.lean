module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFinitePresentationCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSectionsTuples
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# The universe lift of a ringed site and of its sheaves of modules

This file `ULift`s the structure sheaf of a ringed site and, over the lifted structure sheaf, the
sections of a sheaf of modules, to the universe `max u v w`, and it shows that coherence is
unchanged by the operation.  On a site whose objects live in `Type u` with morphisms in `Type v`,
sheafification of abelian groups is available on every slice at the module universe `max u v w`.

## Main definitions

* `Stacks.SheafOfModules.CoherentLift.liftRingedSite`: the sectionwise `ULift` of the structure
  sheaf of a ringed site, as a ringed site on the same category and topology.
* `Stacks.SheafOfModules.CoherentLift.liftModule`: the sectionwise `ULift` of a sheaf of modules,
  as a sheaf of modules over the lifted structure sheaf.
* `Stacks.SheafOfModules.CoherentLift.relationsEquiv`: the comparison of the presheaves of
  relations among two matching finite families of sections.

## Main results

* `Stacks.SheafOfModules.CoherentLift.relations_isFiniteType_of_sectionwiseEquiv`: finite type of
  the presheaf of relations among a finite family of sections transports along a sectionwise
  additive equivalence which is semilinear over a sectionwise ring equivalence.
* `Stacks.SheafOfModules.CoherentLift.isCoherentOnSite_liftModule_iff`: **a sheaf of modules is
  coherent if and only if its universe lift is coherent.**

## Implementation notes

`liftModule` is the only place where the two spellings of the lifted sheaf of rings have to be
identified: the sections of `Tensor.ringSheaf (liftRingedSite X).O` are, definitionally, the
`ULift` of the sections of `Tensor.ringSheaf X.O`, but the identification passes through
`Tensor.ringSheaf` and `CategoryTheory.sheafCompose`, which instance resolution does not unfold.
The restriction maps therefore restrict scalars with the source and target rings written as the
`ULift`s, so that their `Module` instances resolve; marking `liftRingedSite` and `sheafCompose`
locally `implicit_reducible` lets the functoriality proofs see through the lifted site, and
nothing else in the file needs it.

Finite type of the sections themselves transports by
`Stacks.SheafOfModules.isFiniteType_of_sectionwiseEquiv`, which already allows the ring and the
module universes to differ on the two sides.  The second condition of coherence is about the
presheaf of relations on a slice site, and `relationsEquiv` is the corresponding comparison:
on an object of the slice it reindexes a tuple of scalars by the ring equivalence, the
relation `∑ aᵢ • sᵢ = 0` being preserved because the equivalence is semilinear and natural.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.CoherentLift


universe u v w

/-- The sectionwise `ULift` of the structure sheaf of a ringed site, as a ringed site on the
same category and the same topology. -/
noncomputable def liftRingedSite (X : AlgebraicGeometry.RingedSite.{u, v, w}) :
    AlgebraicGeometry.RingedSite.{u, v, max u v w} where
  C := X.C
  J := X.J
  O := ⟨{ obj V := CommRingCat.of (ULift.{max u v} (X.O.obj.obj V))
          map f := CommRingCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp
              ((X.O.obj.map f).hom.comp ULift.ringEquiv.toRingHom))
          map_id V := by ext x; exact ConcreteCategory.congr_hom (X.O.obj.map_id V) x.down
          map_comp f g := by
            ext x; exact ConcreteCategory.congr_hom (X.O.obj.map_comp f g) x.down },
    (Presheaf.isSheaf_iff_isSheaf_comp X.J _ (forget CommRingCat.{max u v w})).mpr
      (Presheaf.isSheaf_comp_of_isSheaf X.J (X.O.obj ⋙ forget CommRingCat.{w}) uliftFunctor
        (Presheaf.isSheaf_comp_of_isSheaf X.J _ _ X.O.property))⟩

/-- The sections of the lifted structure sheaf over an object are the `ULift` of the sections of
the original one: the identification is definitional. -/
noncomputable def liftRingEquiv (X : AlgebraicGeometry.RingedSite.{u, v, w}) (V : X.Cᵒᵖ) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O).obj.obj V ≃+*
      ULift.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) :=
  RingEquiv.refl _

attribute [local implicit_reducible] liftRingedSite CategoryTheory.sheafCompose

/-- The sectionwise `ULift` of a sheaf of modules, over the lifted structure sheaf. -/
noncomputable def liftModule (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O) where
  val :=
    { obj V := ModuleCat.of (ULift.{max u v} ((Tensor.ringSheaf X.O).obj.obj V))
        (ULift.{max u v} (M.val.obj V))
      map {V W} f := ModuleCat.ofHom
        (Y := (ModuleCat.restrictScalars
          (R := ULift.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V))
          (S := ULift.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj W))
          ((Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O).obj.map f).hom).obj
          (ModuleCat.of (ULift.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj W))
            (ULift.{max u v} (M.val.obj W))))
        { toFun x := ULift.up (M.val.map f x.down)
          map_add' x y := congrArg ULift.up (map_add (M.val.map f).hom x.down y.down)
          map_smul' a x := congrArg ULift.up (M.val.map_smul f a.down x.down) }
      map_id V := by
        ext x
        apply ULift.ext
        change M.val.map (𝟙 V) x.down = x.down
        rw [M.val.map_id]
        rfl
      map_comp f g := by ext x; exact congrArg ULift.up (M.val.map_comp_apply f g x.down) }
  isSheaf := Presheaf.isSheaf_comp_of_isSheaf X.J M.val.presheaf
    AddCommGrpCat.uliftFunctor M.isSheaf

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

universe w' m m'

/-- Comparison of the presheaves of relations among two matching finite families of sections,
along a sectionwise additive equivalence semilinear over a sectionwise ring equivalence. -/
noncomputable def relationsEquiv
    {R : Cᵒᵖ ⥤ RingCat.{w}} {S : Cᵒᵖ ⥤ RingCat.{w'}}
    {M : PresheafOfModules.{m} R} {N : PresheafOfModules.{m'} S}
    (eR : ∀ V, R.obj V ≃+* S.obj V) (e : ∀ V, M.obj V ≃+ N.obj V)
    (he : ∀ V (a : R.obj V) (x : M.obj V), e V (a • x) = eR V a • e V x)
    (hn : ∀ {V W} (f : V ⟶ W) (x : M.obj V),
      e W (M.restrictₛₗ f x) = N.restrictₛₗ f (e V x))
    {U : C} {n : ℕ} (s : Fin n → N.obj (op U)) (V : (Over U)ᵒᵖ) :
    (PresheafOfModules.relations M (fun i ↦ (e (op U)).symm (s i))).obj V ≃+
      (PresheafOfModules.relations N s).obj V where
  toFun a := ⟨fun i ↦ eR (op V.unop.left) (a.val i), by
    have ha := congrArg (e (op V.unop.left)) a.property
    change e (op V.unop.left)
      (∑ i, a.val i • M.restrictₛₗ V.unop.hom.op ((e (op U)).symm (s i))) =
      e (op V.unop.left) 0 at ha
    change (∑ i, eR (op V.unop.left) (a.val i) •
      N.restrictₛₗ V.unop.hom.op (s i)) = 0
    simpa only [map_sum, he, hn, AddEquiv.apply_symm_apply, map_zero] using ha⟩
  invFun a := ⟨fun i ↦ (eR (op V.unop.left)).symm (a.val i), by
    apply (e (op V.unop.left)).injective
    change e (op V.unop.left)
      (∑ i, (eR (op V.unop.left)).symm (a.val i) •
        M.restrictₛₗ V.unop.hom.op ((e (op U)).symm (s i))) = e (op V.unop.left) 0
    have ha := a.property
    change (∑ i, a.val i • N.restrictₛₗ V.unop.hom.op (s i)) = 0 at ha
    simpa only [map_sum, he, hn, AddEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, map_zero] using ha⟩
  left_inv a := Subtype.ext (funext fun _ ↦ (eR (op V.unop.left)).symm_apply_apply _)
  right_inv a := Subtype.ext (funext fun _ ↦ (eR (op V.unop.left)).apply_symm_apply _)
  map_add' a b := Subtype.ext (funext fun _ ↦ map_add (eR (op V.unop.left)) _ _)

/-- Finite type of the presheaf of relations transports along a sectionwise additive
equivalence semilinear over a sectionwise ring equivalence. -/
theorem relations_isFiniteType_of_sectionwiseEquiv
    {R : Cᵒᵖ ⥤ RingCat.{w}} {S : Cᵒᵖ ⥤ RingCat.{w'}}
    {M : PresheafOfModules.{m} R} {N : PresheafOfModules.{m'} S}
    (eR : ∀ V, R.obj V ≃+* S.obj V)
    (hR : ∀ {V W} (f : V ⟶ W) (a : R.obj V), eR W (R.map f a) = S.map f (eR V a))
    (e : ∀ V, M.obj V ≃+ N.obj V)
    (he : ∀ V (a : R.obj V) (x : M.obj V), e V (a • x) = eR V a • e V x)
    (hn : ∀ {V W} (f : V ⟶ W) (x : M.obj V),
      e W (M.restrictₛₗ f x) = N.restrictₛₗ f (e V x))
    {U : C} {n : ℕ} (s : Fin n → N.obj (op U))
    (h : PresheafOfModules.IsFiniteType (J.over U)
      (PresheafOfModules.relations M (fun i ↦ (e (op U)).symm (s i)))) :
    PresheafOfModules.IsFiniteType (J.over U) (PresheafOfModules.relations N s) := by
  apply Stacks.SheafOfModules.isFiniteType_of_sectionwiseEquiv
    (fun V ↦ eR (op V.unop.left)) (relationsEquiv eR e he hn s) _ _ h
  · intro V a x
    apply Subtype.ext
    funext i
    exact map_mul (eR (op V.unop.left)) a (x.val i)
  · intro V W f x
    apply Subtype.ext
    funext i
    exact hR f.unop.left.op (x.val i)

end Transport

/-- Coherence is unchanged by the sectionwise `ULift` of a sheaf of modules and of its
structure sheaf. -/
theorem isCoherentOnSite_liftModule_iff (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.IsCoherentOnSite (liftModule.{u, v, w} X M) ↔
      SheafOfModules.IsCoherentOnSite M := by
  refine ⟨fun h ↦ ⟨?_, fun U n s ↦ ?_⟩, fun h ↦ ⟨?_, fun U n s ↦ ?_⟩⟩
  · exact Stacks.SheafOfModules.isFiniteType_of_sectionwiseEquiv
      (fun _ ↦ ULift.ringEquiv) (fun _ ↦ AddEquiv.ulift) (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl)
      h.isFiniteType
  · exact relations_isFiniteType_of_sectionwiseEquiv
      (fun _ ↦ ULift.ringEquiv) (fun _ _ ↦ rfl) (fun _ ↦ AddEquiv.ulift)
      (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl) s (h.kernel_isFiniteType U n _)
  · exact Stacks.SheafOfModules.isFiniteType_of_sectionwiseEquiv
      (fun _ ↦ ULift.ringEquiv.symm) (fun _ ↦ AddEquiv.ulift.symm) (fun _ _ _ ↦ rfl)
      (fun _ _ ↦ rfl) h.isFiniteType
  · exact relations_isFiniteType_of_sectionwiseEquiv
      (fun _ ↦ ULift.ringEquiv.symm) (fun _ _ ↦ rfl) (fun _ ↦ AddEquiv.ulift.symm)
      (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl) s (h.kernel_isFiniteType U n _)

end Stacks.SheafOfModules.CoherentLift

end
