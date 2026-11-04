module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftCorrespondence
public import StacksFrontier.Deformation.ToposThickening.FlatLiftTorsors

/-!
# The class-level flat-lift dictionary of Stacks 08MQ

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `𝒥 = Ker(t^♯) ⊂ O_{ℬ'}`, and let `ℱ` be an
`O`-module presented on the thickened topos as an `i_*O`-module. For a strict `(f, f')` and `ℱ`
flat over `O_ℬ`, Stacks 08MQ says that a flat lift of `ℱ` forces the canonical map
`f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` of condition (1) of Stacks 08MV to be an isomorphism, and that once it
is one the flat lifts of `ℱ` are exactly the extensions of `ℱ` by `I ⊗_O ℱ` of Stacks 08MB whose
canonical action of the square-zero ideal is the identity.

`Deformation.ToposThickening.IsFlatLiftCorrespondence` is that dictionary read as an equivalence
of propositions, and `Deformation.ToposThickening.isFlatLiftCorrespondence` proves it.
`Deformation.ToposThickening.IsFlatLiftClassCorrespondence` is the same dictionary with its
second clause strengthened to a **bijection of isomorphism classes**, which is what the
principal homogeneous statement of Stacks 08MU needs, and this file **proves** that, so that it
is no longer a hypothesis of Stacks 08MU.

## Main results

* `Deformation.ToposThickening.yonedaExtension_f_comp_eq_of_fixedActionIdentity`: **the
  inclusion of an extension whose canonical action map is the identity is determined by its
  middle term and its reduction.** A map of middle terms over `ℱ` between two such extensions
  automatically commutes with the two inclusions.
* `Deformation.ToposThickening.extensionClass_eq_iff_exists_iso_of_fixedActionIdentity`: hence
  two extensions with action map the identity have the same `Ext¹_O` class exactly when their
  middle terms are isomorphic over `ℱ` — the isomorphism relation of flat lifts.
* `Deformation.ToposThickening.isIso_idealTensorComparison_iff_isIso_canonicalFirstFactor`: the
  canonical map of condition (1) of Stacks 08MV is invertible exactly when the first factor of
  the canonical map of Stacks 08MQ is.
* `Deformation.ToposThickening.flatLiftClassEquivFixedActionExtensionClass`: **the bijection**
  between the isomorphism classes of flat lifts of `ℱ` and the isomorphism classes of extensions
  of `ℱ` by `I ⊗_O ℱ` with action map the identity.
* `Deformation.ToposThickening.isFlatLiftClassCorrespondence`: **the class-level dictionary
  itself**, which discharges
  `Deformation.ToposThickening.IsFlatLiftClassCorrespondence`.
The dictionary is what makes **Stacks 08MU** unconditional: it is supplied, not assumed, to
`Deformation.ToposThickening.flatLiftClass_torsor` in
`StacksFrontier/Deformation/ToposThickening/FlatLiftTorsors.lean`. The vocabulary the dictionary is
stated over — `Deformation.ToposThickening.FlatLift`,
`Deformation.ToposThickening.FlatLiftClass` and
`Deformation.ToposThickening.IsFlatLiftClassCorrespondence` itself — lives in that same module,
which this one imports.

## How the proof goes

The two maps of the bijection are the two readings of the bookkeeping of Section 08MN that the
library already carries:

* a flat lift `ℱ'` has, by Stacks 08MQ, invertible second factor `I ⊗_O ℱ ⟶ I·ℱ'`, and reading
  its ideal-product sequence through the inverse of that factor gives an extension with action
  map the identity and *the same middle term and reduction* — `Deformation.ToposThickening`'s
  `extensionActionMap_shortExactYonedaExtension_canonicalSecondFactor`;
* an extension with action map the identity has its ideal-product sequence short exact
  (`Deformation.ToposThickening.shortExact_idealProduct`) and middle term flat over `O_{ℬ'}`
  (`Deformation.ToposThickening.isFlat_baseModule_of_fixedActionIdentity`), so it *is* a flat
  lift, again with the same middle term and reduction.

So both readings leave the pair `(ℱ', ℱ' ⟶ i_*ℱ)` alone, and the two notions of isomorphism —
an isomorphism of middle terms commuting with the reductions, for flat lifts, and equality of
`Ext¹_O` classes, for extensions — have to be matched. One direction is Stacks 06XV: isomorphic
extensions have the same class. The other needs that the *inclusion* is not extra data: for an
extension whose action map is the identity, the multiplication map `I ⊗_{O'} ℱ' ⟶ ℱ'` of
Stacks 08M4 is the reduction comparison followed by the inclusion
(`Deformation.ToposThickening.multiplicationMap_eq_comp_f`), and the reduction comparison is
surjective, so a map of middle terms over `ℱ` commutes with the inclusions whether or not it was
asked to. That is
`Deformation.ToposThickening.yonedaExtension_f_comp_eq_of_fixedActionIdentity`, and it turns the
isomorphism relation of flat lifts into equality of classes.

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08MU](https://stacks.math.columbia.edu/tag/08MU)
* [Stacks Project, Tag 08ME](https://stacks.math.columbia.edu/tag/08ME)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
* [Stacks Project, Tag 08MV](https://stacks.math.columbia.edu/tag/08MV)
* [Stacks Project, Tag 06XV](https://stacks.math.columbia.edu/tag/06XV)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (ringMap multiplicationMap reductionTensorMap
  multiplicationMap_tmul reductionTensorMap_tmul reductionTensorMap_epi)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' vS uS wS vS' uS' wS' e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}]

/-! ### The inclusion of an extension with action map the identity is not extra data -/

section Inclusion

variable (i : RingedToposHom X X') (hi : FirstOrderThickening i)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))

/-- **A map of middle terms over `ℱ` between two extensions whose canonical action maps are the
identity commutes with the two inclusions.** So the inclusion `I ⊗_O ℱ ⟶ ℱ'` of such an
extension is determined by its middle term and its reduction: it is not extra data.

Both composites become the multiplication map `I ⊗_{O'} ℱ' ⟶ ℱ'` of Stacks 08M4 after
precomposition with the surjective reduction comparison `I ⊗_{O'} ℱ' ⟶ I ⊗_O ℱ` — the first by
`Deformation.ToposThickening.multiplicationMap_eq_comp_f`, the second because on `α ⊗ x` both
are `α·u(x)`, the action map of the second extension being the identity and `u` being
`O'`-linear and compatible with the reductions. -/
theorem yonedaExtension_f_comp_eq_of_fixedActionIdentity
    (E E' : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj hi.I)) 0)
    (hE : (extensionActionMap hi E).1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i)).flip.obj F).obj hi.I))
    (hE' : (extensionActionMap hi E').1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i)).flip.obj F).obj hi.I))
    (u : E.Z.left ⟶ E'.Z.left) (hu : u ≫ E'.g = E.g) :
    E.f ≫ u = E'.f := by
  have : Epi (reductionTensorMap i.fSharp hi.I E.Z.left F E.g) :=
    reductionTensorMap_epi i.fSharp hi.I E.Z.left F E.g
  refine (cancel_epi (reductionTensorMap i.fSharp hi.I E.Z.left F E.g)).mp ?_
  rw [← Category.assoc, ← multiplicationMap_eq_comp_f hi F E hE]
  refine tensorSheaf_hom_ext X'.O ?_
  intro U a x
  have hm := multiplicationMap_tmul i.fSharp hi.I E.Z.left hi.incl U a x
  have hr := reductionTensorMap_tmul i.fSharp hi.I E.Z.left F E.g U a x
  have hgx : E.g.val.app U x = E'.g.val.app U (u.val.app U x) :=
    (congrArg (fun m ↦ m.val.app U x) hu).symm
  have hact : E'.f.val.app U
      (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)) (𝟙
              (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val F.val)).app U
        (a ⊗ₜ[(baseRing i).obj.obj U] (E'.g.val.app U (u.val.app U x)))) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj.obj U from hi.incl.val.app U a) •
        u.val.app U x := by
    have h := (extensionActionMap hi E').2 U a (u.val.app U x)
    rw [hE'] at h
    exact h
  refine (comp_val_app (multiplicationMap i.fSharp hi.I E.Z.left hi.incl) u U _).trans ?_
  refine (congrArg (fun y ↦ u.val.app U y) hm).trans ?_
  refine (map_smul (ConcreteCategory.hom (u.val.app U)) _ x).trans ?_
  refine hact.symm.trans ?_
  refine (congrArg (fun y ↦ E'.f.val.app U
    (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)) (𝟙
              (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val F.val)).app U
      (a ⊗ₜ[(baseRing i).obj.obj U] y))) hgx).symm.trans ?_
  refine (congrArg (fun y ↦ E'.f.val.app U y) hr).symm.trans ?_
  exact (comp_val_app (reductionTensorMap i.fSharp hi.I E.Z.left F E.g) E'.f U _).symm

variable [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]

/-- **Two extensions whose canonical action maps are the identity have the same `Ext¹_O` class
exactly when their middle terms are isomorphic over `ℱ`.**

An isomorphism of extensions is an isomorphism of middle terms compatible with both the
inclusions and the reductions, and Stacks 06XV says that having the same class is exactly that.
The compatibility with the inclusions is automatic here, by
`Deformation.ToposThickening.yonedaExtension_f_comp_eq_of_fixedActionIdentity`, so only the
compatibility with the reductions remains — which is the isomorphism relation of flat lifts. -/
theorem extensionClass_eq_iff_exists_iso_of_fixedActionIdentity
    (E E' : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj hi.I)) 0)
    (hE : (extensionActionMap hi E).1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i)).flip.obj F).obj hi.I))
    (hE' : (extensionActionMap hi E').1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i)).flip.obj F).obj hi.I)) :
    extensionClass F (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
        hi.I) E =
        extensionClass F (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
            hi.I) E' ↔
      ∃ κ : E.Z.left ≅ E'.Z.left, κ.hom ≫ E'.g = E.g := by
  have h := (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum.{e}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    ((structureRestrict i).obj F)
    ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
        F).obj hi.I))).2.1
      E.Z.left E'.Z.left E.f E.g (yonedaExtension_comp_zero E) E'.f E'.g
      (yonedaExtension_comp_zero E') (yonedaExtension_shortExact E)
      (yonedaExtension_shortExact E')
  refine Iff.trans h ⟨?_, ?_⟩
  · rintro ⟨κ, -, hκ⟩
    exact ⟨κ, hκ⟩
  · rintro ⟨κ, hκ⟩
    exact ⟨κ, yonedaExtension_f_comp_eq_of_fixedActionIdentity i hi F E E' hE hE' κ.hom hκ, hκ⟩

end Inclusion

/-! ### The two factors of the canonical map of Stacks 08MQ, compared -/

section Factors

variable (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))

include comm

/-- **The canonical map `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` of condition (1) of Stacks 08MV is invertible
exactly when the first factor of the canonical map of Stacks 08MQ is.**

The two differ by the identification `f^*𝒥 ≅ t^*𝒥` pulled back to the thickened topos, which is
an isomorphism, so one is invertible exactly when the other is; that identification is
`Deformation.ToposThickening.pullbackIdealIso_hom_comp_pullbackBaseIdealMap`. -/
theorem isIso_idealTensorComparison_iff_isIso_canonicalFirstFactor
    (hstrict : IsStrictPullbackIdealMap i t f f' hi ht comm) :
    IsIso (idealTensorComparison i t f f' hi ht comm F) ↔
      IsIso (canonicalFirstFactor i t f f' hi ht comm F) := by
  have hfac : idealTensorComparison i t f f' hi ht comm F =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj ((SheafOfModules.restrictScalars
          (ringMap i.fSharp)).obj F)).map
          (pullbackIdealIso t f' ht).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj ((SheafOfModules.restrictScalars
            (ringMap i.fSharp)).obj F)).map
          (pullbackBaseIdealMap i t f f' hi ht comm) := by
    rw [idealTensorComparison, ← Functor.map_comp,
      pullbackIdealIso_hom_comp_pullbackBaseIdealMap i t f f' hi ht comm]
  have hiso : IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)).map
        (pullbackIdealIso t f' ht).hom) :=
    Functor.isIso_map_of_isIso _ _ (pullbackIdealIso t f' ht).isIso_hom
  rw [hfac, isIso_comp_left_iff]
  exact isIso_tensor_pullbackBaseIdealMap_iff_isIso_canonicalFirstFactor i t f f' hi ht comm F

end Factors

/-! ### The bijection of isomorphism classes -/

section Dictionary

variable (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))
  (hstrict : IsStrictPullbackIdealMap i t f f' hi ht comm)
  (hF : AlgebraicGeometry.SheafOfModules.IsFlat (reducedBaseModule i t f f' comm F))

include comm hstrict hF

/-- **The second factor `I ⊗_O ℱ ⟶ I·ℱ'` of the canonical map of Stacks 08MQ is invertible for
a flat lift `ℱ'` of `ℱ`.** This is the "moreover" clause of Stacks 08MQ,
`Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap`, applied to the ideal-product
sequence of the flat lift. -/
theorem isIso_canonicalSecondFactor_flatLift (A : FlatLift i f' hi F) :
    IsIso (canonicalSecondFactor i hi F A.module' A.π A.idealProduct_comp A.shortExact) :=
  have h := isFlat_iff_isIso_canonicalMap i t f f' hi ht comm F A.module' A.π A.idealProduct_comp
    A.shortExact hstrict hF
  (h.2 (h.1.mp A.isFlat)).2

/-- **The extension with action map the identity attached to a flat lift**: the ideal-product
sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i_*ℱ ⟶ 0` of the lift with its kernel term read through the inverse
of the second factor. Its middle term is the lifted module and its reduction is the lift's own
map to `i_*ℱ`. -/
noncomputable def FlatLift.fixedActionExtension (A : FlatLift i f' hi F) :
    Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj hi.I)) 0 :=
  Abelian.shortExactYonedaExtension
    (shortExact_canonicalSecondFactor_comp_ι i hi F A.module' A.π A.idealProduct_comp A.shortExact
      (isIso_canonicalSecondFactor_flatLift i t f f' hi ht comm F hstrict hF A))

/-- The canonical action of the square-zero ideal on the extension attached to a flat lift is
the identity. -/
theorem FlatLift.extensionActionMap_fixedActionExtension (A : FlatLift i f' hi F) :
    (extensionActionMap hi
        (A.fixedActionExtension i t f f' hi ht comm F hstrict hF)).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj hi.I) :=
  extensionActionMap_shortExactYonedaExtension_canonicalSecondFactor i hi F A.module' A.π
    A.idealProduct_comp A.shortExact
    (isIso_canonicalSecondFactor_flatLift i t f f' hi ht comm F hstrict hF A)

variable [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]

/-- **The isomorphism class of extensions with action map the identity attached to a flat
lift.** -/
noncomputable def FlatLift.fixedActionExtensionClass (A : FlatLift i f' hi F) :
    FixedActionExtensionClass.{_, _, _, _, _, _, e} hi F
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj hi.I)
      (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj hi.I)) :=
  ⟨extensionClass F (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj hi.I)
      (A.fixedActionExtension i t f f' hi ht comm F hstrict hF),
    A.fixedActionExtension i t f f' hi ht comm F hstrict hF,
    A.extensionActionMap_fixedActionExtension i t f f' hi ht comm F hstrict hF, rfl⟩

/-- **Two flat lifts have the same attached class exactly when they are isomorphic.** The
extension attached to a flat lift has the lift's own module for its middle term and the lift's
own map to `i_*ℱ` for its reduction, so this is
`Deformation.ToposThickening.extensionClass_eq_iff_exists_iso_of_fixedActionIdentity`. -/
theorem FlatLift.fixedActionExtensionClass_eq_iff (A B : FlatLift i f' hi F) :
    A.fixedActionExtensionClass i t f f' hi ht comm F hstrict hF =
      B.fixedActionExtensionClass i t f f' hi ht comm F hstrict hF ↔
    A.IsIsomorphic B := by
  rw [FlatLift.fixedActionExtensionClass, FlatLift.fixedActionExtensionClass, Subtype.mk_eq_mk]
  exact extensionClass_eq_iff_exists_iso_of_fixedActionIdentity i hi F _ _
    (A.extensionActionMap_fixedActionExtension i t f f' hi ht comm F hstrict hF)
    (B.extensionActionMap_fixedActionExtension i t f f' hi ht comm F hstrict hF)

omit hstrict hF in
/-- **An extension of `ℱ` by `I ⊗_O ℱ` whose canonical action map is the identity is a flat lift
of `ℱ`**, granting the first factor of the canonical map of Stacks 08MQ. Its ideal-product
sequence is short exact (`Deformation.ToposThickening.shortExact_idealProduct`) and its middle
term is flat over `O_{ℬ'}`
(`Deformation.ToposThickening.isFlat_baseModule_of_fixedActionIdentity`). -/
noncomputable def flatLiftOfFixedActionIdentity
    (hstrict : IsStrictPullbackIdealMap i t f f' hi ht comm)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat (reducedBaseModule i t f f' comm F))
    (hcff : IsIso (canonicalFirstFactor i t f f' hi ht comm F))
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj hi.I)) 0)
    (hE : (extensionActionMap hi E).1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i)).flip.obj F).obj hi.I)) :
    FlatLift i f' hi F where
  module' := E.Z.left
  π := E.g
  idealProduct_comp := idealProduct_ι_comp_g_eq_zero hi F E hE
  isFlat :=
    isFlat_baseModule_of_fixedActionIdentity i t f f' hi ht comm F hstrict hF hcff E hE
  shortExact := shortExact_idealProduct hi F E hE

/-- **The class attached to the flat lift of an extension with action map the identity is the
class of that extension.** Both have the same middle term and the same reduction, so this is
`Deformation.ToposThickening.extensionClass_eq_iff_exists_iso_of_fixedActionIdentity` applied to
the identity. -/
theorem fixedActionExtensionClass_flatLiftOfFixedActionIdentity
    (hcff : IsIso (canonicalFirstFactor i t f f' hi ht comm F))
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj hi.I)) 0)
    (hE : (extensionActionMap hi E).1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i)).flip.obj F).obj hi.I)) :
    ((flatLiftOfFixedActionIdentity i t f f' hi ht comm F hstrict hF hcff E
            hE).fixedActionExtensionClass i t f f' hi ht comm F hstrict hF).1 =
      extensionClass F (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
          hi.I) E :=
  (extensionClass_eq_iff_exists_iso_of_fixedActionIdentity i hi F _ E
    ((flatLiftOfFixedActionIdentity i t f f' hi ht comm F hstrict hF hcff E
      hE).extensionActionMap_fixedActionExtension i t f f' hi ht comm F hstrict hF) hE).2
    ⟨Iso.refl _, Category.id_comp _⟩

/-- **The bijection of Section 08MN.** Granting the hypotheses of Stacks 08MQ and condition (1)
of Stacks 08MV, the isomorphism classes of flat lifts of `ℱ` are in bijection with the
isomorphism classes of extensions of `ℱ` by `I ⊗_O ℱ` of Stacks 08MB whose canonical action of
the square-zero ideal is the identity.

The bijection leaves the pair `(ℱ', ℱ' ⟶ i_*ℱ)` alone in both directions; see the module
docstring. -/
noncomputable def flatLiftClassEquivFixedActionExtensionClass
    (hcff : IsIso (canonicalFirstFactor i t f f' hi ht comm F)) :
    FlatLiftClass i f' hi F ≃
      FixedActionExtensionClass.{_, _, _, _, _, _, e} hi F
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj hi.I)
        (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj hi.I)) :=
  Equiv.ofBijective
    (Quotient.lift
      (fun A : FlatLift i f' hi F =>
        A.fixedActionExtensionClass i t f f' hi ht comm F hstrict hF)
      fun _ _ h =>
        (FlatLift.fixedActionExtensionClass_eq_iff
          i t f f' hi ht comm F hstrict hF _ _).2 h)
    ⟨by
      intro a b hab
      obtain ⟨A, rfl⟩ := Quotient.exists_rep a
      obtain ⟨B, rfl⟩ := Quotient.exists_rep b
      exact Quotient.sound
        ((FlatLift.fixedActionExtensionClass_eq_iff
          i t f f' hi ht comm F hstrict hF A B).1 hab),
     by
      intro ξ
      obtain ⟨E, hE, hξ⟩ := ξ.2
      refine ⟨Quotient.mk (flatLiftSetoid i f' hi F)
        (flatLiftOfFixedActionIdentity i t f f' hi ht comm F hstrict hF hcff E hE), ?_⟩
      refine Subtype.ext ?_
      rw [← hξ]
      exact fixedActionExtensionClass_flatLiftOfFixedActionIdentity
        i t f f' hi ht comm F hstrict hF hcff E hE⟩

end Dictionary

/-! ### The dictionary -/

section Statement

variable (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (F : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))

include comm

/-- **The consequence of Stacks 08MQ that the proof of Stacks 08MU consumes.** Granting that the
square is strict and that `ℱ` is flat over `O_ℬ`, a flat lift of `ℱ` forces the canonical map
`f^*𝒥 ⊗ ℱ ⟶ I ⊗ ℱ` to be an isomorphism, and once that map is an isomorphism the isomorphism
classes of flat lifts of `ℱ` are in bijection with the isomorphism classes of extensions of `ℱ`
by `I ⊗_O ℱ` of Stacks 08MB whose canonical action of the square-zero ideal is the identity.

This discharges `Deformation.ToposThickening.IsFlatLiftClassCorrespondence`, which used to be
carried as a hypothesis at Stacks 08MU; `Deformation.ToposThickening.flatLiftClass_torsor` now
supplies it from here. -/
theorem isFlatLiftClassCorrespondence
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))] :
    IsFlatLiftClassCorrespondence.{_, _, _, _, _, _, _, _, _, _, _, e}
      i t f f' hi ht comm F := by
  intro hstrictD hflat
  refine ⟨(isFlatLiftCorrespondence i t f f' hi ht comm F hstrictD hflat).1, fun hiso ↦ ?_⟩
  have hstrict : IsStrictPullbackIdealMap i t f f' hi ht comm :=
    (isStrictPullbackIdealMap_iff_isStrict i t f f' hi ht comm).mpr hstrictD
  have hF : AlgebraicGeometry.SheafOfModules.IsFlat (reducedBaseModule i t f f' comm F) :=
    isFlat_reducedBaseModule_of_isFlatOverBase i t f f' hi ht comm F hflat
  exact ⟨flatLiftClassEquivFixedActionExtensionClass i t f f' hi ht comm F hstrict hF
    ((isIso_idealTensorComparison_iff_isIso_canonicalFirstFactor i t f f' hi ht comm F
      hstrict).mp hiso)⟩

end Statement

end Deformation.ToposThickening

end
