module

public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction

/-!
# Isomorphism classes of extensions with a fixed action form an `Ext¹` torsor

Fix a first order thickening `i : (Sh(C), O) ⟶ (Sh(D), O')` of ringed topoi with square-zero
ideal `I`, two `O`-modules `F`, `K` (modules over the direct image of `O`, the underlying topoi
being identified as in the source) and an `O`-linear map `c : I ⊗_O F ⟶ K`. This file considers
the extensions `0 → K → F' → F → 0` of `O'`-modules (Stacks 08MB) whose canonical action map
`c_{F'}` is `c`, and their *isomorphism classes*: two such extensions are isomorphic when there
is an isomorphism of their middle terms compatible with the maps from `K` and to `F`.

The main result, `exists_addTorsor_fixedActionExtensionIsoClass` (**Stacks 08ME**), says that
when there is such an extension at all, the set of isomorphism classes is a principal
homogeneous space under `Ext¹_O(F, K)`, the action of a class `a` being the Baer sum with the
`O'`-extension underlying `a` — in `Ext¹_{O'}(F, K)`, whose addition is the Baer sum
(Stacks 06XV), this is adding the image of `a`.

## Main definitions

* `Deformation.ToposThickening.FixedActionExtension`: the extensions over the thickening with
  prescribed action map `c`.
* `Deformation.ToposThickening.FixedActionExtension.Isomorphic`: two such extensions are
  isomorphic.
* `Deformation.ToposThickening.FixedActionExtensionIsoClass`: the set of isomorphism classes.

## Main results

* `Deformation.ToposThickening.FixedActionExtension.isomorphic_iff_extensionClass_eq`: two
  extensions are isomorphic exactly when they have the same `Ext¹_{O'}` class.
* `Deformation.ToposThickening.exists_addTorsor_fixedActionExtensionIsoClass` (**Stacks 08ME**).

## Implementation notes

`Deformation.ToposThickening.fixedActionExtensionClass_torsor` states a torsor structure on the
`Ext¹_{O'}` classes realized by an extension with action `c`, and only its existence. Here the
torsor is on the quotient of the extensions by isomorphism, as in the source, and the action is
pinned down: `a +ᵥ [F'₁] = [F'₂]` exactly when the class of `F'₂` is the class of `F'₁` plus the
image of `a`. The comparison of the quotient with the set of realized classes is Stacks 06XV,
through `Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`.

## References

* [Stacks Project, Tag 08ME](https://stacks.math.columbia.edu/tag/08ME)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w' e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}}
  {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]

/-- The extensions `0 → K → F' → F → 0` of `O'`-modules over a first order thickening
(Stacks 08MB) whose canonical action map `I ⊗ F ⟶ K` is the prescribed map `c`. -/
abbrev FixedActionExtension
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K) : Type _ :=
  { E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars (structureRingMap i)).obj K) 0 //
    (extensionActionMap hi E).1 = c }

namespace FixedActionExtension

variable {hi : FirstOrderThickening i}
  {F K : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
  {c : ((Stacks.SheafOfModules.Tensor.sheafTensor
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K}

/-- Two extensions are *isomorphic* if there is an isomorphism of their middle terms which is
compatible with the maps from `K` and the maps to `F`. -/
def Isomorphic (E E' : FixedActionExtension hi F K c) : Prop :=
  ∃ φ : E.1.Z.left ≅ E'.1.Z.left, E.1.f ≫ φ.hom = E'.1.f ∧ φ.hom ≫ E'.1.g = E.1.g

/-- Two extensions are isomorphic exactly when they have the same `Ext¹_{O'}` class
(Stacks 06XV). -/
theorem isomorphic_iff_extensionClass_eq
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (E E' : FixedActionExtension hi F K c) :
    Isomorphic E E' ↔ extensionClass.{_, _, _, _, _, _, e} F K E.1 = extensionClass F K E'.1 :=
  ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum.{e}
    (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((SheafOfModules.restrictScalars (structureRingMap i)).obj F)
    ((SheafOfModules.restrictScalars (structureRingMap i)).obj K)).2.1
    E.1.Z.left E'.1.Z.left E.1.f E.1.g _ E'.1.f E'.1.g _
    (yonedaExtension_shortExact E.1) (yonedaExtension_shortExact E'.1)).symm

/-- Isomorphism of extensions is an equivalence relation. -/
theorem isomorphic_equivalence :
    Equivalence (Isomorphic (hi := hi) (F := F) (K := K) (c := c)) where
  refl E := ⟨Iso.refl _, Category.comp_id _, Category.id_comp _⟩
  symm := by
    rintro E E' ⟨φ, hf, hg⟩
    refine ⟨φ.symm, ?_, ?_⟩
    · rw [Iso.symm_hom, ← hf, Category.assoc, φ.hom_inv_id, Category.comp_id]
    · rw [Iso.symm_hom, ← hg, φ.inv_hom_id_assoc]
  trans := by
    rintro E E' E'' ⟨φ, hf, hg⟩ ⟨ψ, hf', hg'⟩
    refine ⟨φ ≪≫ ψ, ?_, ?_⟩
    · rw [Iso.trans_hom, ← Category.assoc, hf, hf']
    · rw [Iso.trans_hom, Category.assoc, hg', hg]

/-- The setoid of isomorphism of extensions. -/
def isoSetoid : Setoid (FixedActionExtension hi F K c) :=
  ⟨Isomorphic, isomorphic_equivalence⟩

end FixedActionExtension

/-- The set of isomorphism classes of extensions over the thickening inducing the prescribed
action `c` of the square-zero ideal. -/
abbrev FixedActionExtensionIsoClass
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K) : Type _ :=
  Quotient (FixedActionExtension.isoSetoid (hi := hi) (F := F) (K := K) (c := c))

/-- The isomorphism classes of extensions with action `c` are in bijection with the `Ext¹_{O'}`
classes these extensions realize (Stacks 06XV). -/
noncomputable def fixedActionExtensionIsoClassEquiv
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K) :
    FixedActionExtensionIsoClass hi F K c ≃
      FixedActionExtensionClass.{_, _, _, _, _, _, e} hi F K c :=
  Equiv.ofBijective
    (Quotient.lift (fun E => ⟨extensionClass F K E.1, E.1, E.2, rfl⟩)
      fun E E' hE => Subtype.ext
        ((FixedActionExtension.isomorphic_iff_extensionClass_eq.{_, _, _, _, _, _, e} E E').1 hE))
    ⟨fun x y hxy => by
      induction x using Quotient.ind
      induction y using Quotient.ind
      exact Quotient.sound
        ((FixedActionExtension.isomorphic_iff_extensionClass_eq.{_, _, _, _, _, _, e} _ _).2
          (congrArg Subtype.val hxy)),
    fun ⟨_, E, hc, hE⟩ => ⟨⟦⟨E, hc⟩⟧, Subtype.ext hE⟩⟩

/-- **Stacks 08ME.** Let `i` be a first order thickening of ringed topoi, `F`, `K` modules over
the quotient structure sheaf and `c : I ⊗ F ⟶ K` linear. If there is an extension
`0 → K → F' → F → 0` of `O'`-modules with `c_{F'} = c`, then the set of isomorphism classes of
these extensions is a principal homogeneous space under `Ext¹_O(F, K)`: there is a torsor
structure in which `a` sends the class of `F'₁` to the class of `F'₂` exactly when the
`Ext¹_{O'}` class of `F'₂` is the Baer sum of that of `F'₁` with the image of `a`. -/
@[stacks 08ME]
theorem exists_addTorsor_fixedActionExtensionIsoClass
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K)
    (h : Nonempty (FixedActionExtension hi F K c)) :
    ∃ T : AddTorsor (Abelian.Ext.{e} F K 1) (FixedActionExtensionIsoClass hi F K c),
      ∀ (a : Abelian.Ext.{e} F K 1) (E E' : FixedActionExtension hi F K c),
        (T.vadd a ⟦E⟧ = ⟦E'⟧) ↔
          extensionClass F K E'.1 =
            (SheafOfModules.restrictScalars (structureRingMap i)).mapExtAddHom F K 1 a +
              extensionClass F K E.1 := by
  classical
  let R := SheafOfModules.restrictScalars.{w'} (structureRingMap i)
  let ff := hi.restrictScalarsFullyFaithful
  have : R.Full := ff.full
  have : R.Faithful := ff.faithful
  let eqv := fixedActionExtensionIsoClassEquiv.{_, _, _, _, _, _, e} hi F K c
  let T₀ : AddTorsor (Abelian.Ext F K 1)
      (FixedActionExtensionClass.{_, _, _, _, _, _, e} hi F K c) :=
    AddTorsor.ofAddMonoidHomTranslate (R.mapExtAddHom F K 1)
      (Functor.mapExtAddHom_injective_of_fullyFaithful R F K) (eqv ⟦h.some⟧).val _
      (exists_extensionActionMap_eq_iff_exists_add_mapExtAddHom hi (eqv ⟦h.some⟧))
  -- transport along `eqv`
  let T : AddTorsor (Abelian.Ext F K 1) (FixedActionExtensionIsoClass hi F K c) :=
    { vadd := fun a x => eqv.symm (T₀.vadd a (eqv x))
      zero_vadd := fun x => by
        change eqv.symm (T₀.vadd 0 (eqv x)) = x
        rw [Equiv.symm_apply_eq]
        exact T₀.zero_vadd (eqv x)
      add_vadd := fun a a' x => by
        change eqv.symm (T₀.vadd (a + a') (eqv x)) =
          eqv.symm (T₀.vadd a (eqv (eqv.symm (T₀.vadd a' (eqv x)))))
        rw [Equiv.apply_symm_apply]
        exact congrArg eqv.symm (T₀.add_vadd a a' (eqv x))
      vsub := fun x y => T₀.vsub (eqv x) (eqv y)
      nonempty := ⟨⟦h.some⟧⟩
      vsub_vadd' := fun x y => by
        change eqv.symm (T₀.vadd (T₀.vsub (eqv x) (eqv y)) (eqv y)) = x
        rw [Equiv.symm_apply_eq]
        exact T₀.vsub_vadd' (eqv x) (eqv y)
      vadd_vsub' := fun a x => by
        change T₀.vsub (eqv (eqv.symm (T₀.vadd a (eqv x)))) (eqv x) = a
        rw [Equiv.apply_symm_apply]
        exact T₀.vadd_vsub' a (eqv x) }
  refine ⟨T, fun a E E' => ?_⟩
  change eqv.symm (T₀.vadd a (eqv ⟦E⟧)) = ⟦E'⟧ ↔ _
  rw [Equiv.symm_apply_eq, Subtype.ext_iff]
  exact eq_comm

end Deformation.ToposThickening
