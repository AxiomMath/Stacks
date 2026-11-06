module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.RestrictScalars
public import StacksFrontier.Deformation.ToposThickening.ExtensionFunctoriality
public import StacksFrontier.Deformation.ToposThickening.IdealActionNaturality
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ExtBoundary
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ExtTorsor
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.TensorSheafSections
public import StacksFrontier.Deformation.ToposThickening.RestrictScalarsEssentialImage

/-!
# Extensions with a fixed first-order action: the torsor

Fix a first order thickening `i` of ringed topoi with square-zero ideal `I`. This file defines
the `Ext¹_O` class of an extension over the thickening, shows that its action map depends only
on, and additively on, that class, and that the isomorphism classes of extensions inducing a
prescribed action form a principal homogeneous space under `Ext¹_{i_*O'}(F, K)`
(`Deformation.ToposThickening.fixedActionExtensionClass_torsor`, **Stacks 08ME**).

See `StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction` for an overview.

## References

* [Stacks Project, Tag 08ME](https://stacks.math.columbia.edu/tag/08ME)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
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

/-! ### The structure map on underlying sheaves of rings

`Deformation.ToposThickening.structureRingMap` is **not** declared here. It is the one in
`StacksFrontier.Deformation.ToposThickening.ExtensionFunctoriality`, imported above, and the uses
below bind to it. This file carried a second copy, which clashed with the imported one and broke
every module importing both.

The copy existed for a reason worth recording, and the surviving declaration satisfies it. The
underlying functor application has source `(sheafCompose Y.J (forget₂ CommRingCat RingCat)).obj
Y.O`, which is definitionally but not reducibly the canonical
`Stacks.SheafOfModules.Tensor.ringSheaf Y.O`. Since `Category (SheafOfModules R)` is indexed by
`R`, the two spellings carry two different category instances, and this file's instances --
`HasExt`, `HasSheafify`, local surjectivity of the structure map -- are all stated at the
canonical one, so an ascription naming the canonical source and target is load-bearing. The
declaration in `ExtensionFunctoriality` ascribes to `Tensor.ringSheaf Y.O ⟶ Tensor.ringSheaf
(baseRing i)`, and `baseRing i` is by definition `(pushforwardCommRingFunctor i.toToposHom).obj
X.O` -- the same term this copy spelled out -- so both sides are the canonical spelling and
nothing is lost. `Deformation.ToposThickening.extensionActionMap` carries the same ascription. -/

/-! ### Restriction of scalars along the structure map -/

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- The structure map of a first order thickening is locally surjective on the underlying
sheaves of rings. -/
lemma FirstOrderThickening.structureMap_locallySurjective (hi : FirstOrderThickening i) :
    Presheaf.IsLocallySurjective Y.J
      (structureRingMap i).hom := by
  show Presheaf.IsLocallySurjective Y.J
    (Functor.whiskerRight i.fSharp.hom (forget₂ CommRingCat RingCat))
  refine ⟨?_⟩
  intro U s
  simpa [Presheaf.imageSieve] using hi.surjective.imageSieve_mem s

/-- Restriction of scalars along the structure map of a first order thickening is fully
faithful: the structure map is locally surjective, so an `O`-linear map between modules
restricted from `i_*O'` is already `i_*O'`-linear. -/
noncomputable def FirstOrderThickening.restrictScalarsFullyFaithful
    (hi : FirstOrderThickening i) :
    (SheafOfModules.restrictScalars.{w'}
      (structureRingMap i)).FullyFaithful :=
  letI := hi.structureMap_locallySurjective
  Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective.{w'} _

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- **The essential image of restriction of scalars along the structure map.** A sheaf of
`O`-modules is isomorphic to one restricted from an `i_*O'`-module exactly when the square-zero
ideal of the thickening annihilates it, section by section.

This is the module-theoretic half of the essential-image criterion of Stacks 08M3, with the
kernel of the structure map written as the square-zero ideal. It carries no Stacks attribute:
the 08M3 clause is about the direct image of modules and is already recorded on
`AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates`. -/
theorem FirstOrderThickening.essImage_restrictScalars_iff (hi : FirstOrderThickening i)
    (M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (SheafOfModules.restrictScalars.{w'}
        (structureRingMap i)).essImage M ↔
      ∀ (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (m : M.val.obj U),
        (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
          from hi.incl.val.app U a) • m = 0 := by
  have := hi.structureMap_locallySurjective
  refine (ToposThickening.essImage_restrictScalars_iff _ M).trans ⟨?_, ?_⟩
  · intro h U a m
    exact h U (hi.incl.val.app U a) ((hi.kernel U _).2 ⟨a, rfl⟩) m
  · intro h U a ha m
    obtain ⟨b, rfl⟩ := (hi.kernel U a).1 ha
    exact h U b m

/-! ### The `Ext` class of an extension, and its action map -/

/-- The `Ext¹_O` class of an extension of modules over the thickened structure sheaf. -/
noncomputable def extensionClass
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0) :
    Abelian.Ext
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 1 :=
  (yonedaExtension_shortExact E).extClass

/-- The action map of an extension takes the value `z` on the pure tensor `a ⊗ g x` exactly when
`f z` is the action of `a` on `x`. -/
private lemma extensionActionMap_unit_eq_iff
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : E.Z.left.val.obj U) (z : K.val.obj U) :
    (extensionActionMap hi E).1.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
            i.toToposHom).obj X.O))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
            i.toToposHom).obj X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val F.val)).app U
          (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U]
            E.g.val.app U x)) = z ↔
      E.f.val.app U z =
        (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
          from hi.incl.val.app U a) • x := by
  have : Mono E.f := E.mono_f
  have hinj : Function.Injective (E.f.val.app U) := by
    rw [← ModuleCat.mono_iff_injective]
    exact Functor.map_mono
      (SheafOfModules.evaluation (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) U) E.f
  rw [← (extensionActionMap hi E).property U a x, eq_comm]
  exact hinj.eq_iff.symm

/-- Two maps out of the tensor product with the square-zero ideal are equal if they agree on the
pure tensors `a ⊗ g x`, where `g` is the surjection of an extension. -/
private lemma eq_of_agree_on_unit_tensor_lifts
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0)
    (c c' : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K)
    (h : ∀ (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : E.Z.left.val.obj U),
      c.val.app U
          (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O)).obj)).unit.app
            (PresheafOfModules.tensorObj hi.I.val F.val)).app U
            (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U]
              E.g.val.app U x)) =
        c'.val.app U
          (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O)).obj)).unit.app
            (PresheafOfModules.tensorObj hi.I.val F.val)).app U
            (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U]
              E.g.val.app U x))) :
    c = c' := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
    i.toToposHom).obj X.O)
  let O := (pushforwardCommRingFunctor i.toToposHom).obj X.O
  have hc (d : ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj hi.I).obj F ⟶ K)
      (W : Y.Cᵒᵖ) (b : hi.I.val.obj W) (z : F.val.obj W) :
      d.val.app W
          (((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit.app
            (PresheafOfModules.tensorObj hi.I.val F.val)).app W (b ⊗ₜ[O.obj.obj W] z)) =
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) d).app W (b ⊗ₜ[O.obj.obj W] z) :=
    (congrArg (fun q => q.app W (b ⊗ₜ[O.obj.obj W] z))
      (PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
        (α := 𝟙 R.obj) (f := d))).symm
  let t := PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) c
  let t' := PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) c'
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a y
  let f :=
    (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj).map E.g.val
  have : Presheaf.IsLocallySurjective Y.J f := sheafModule_epi_locallySurjective E.g
  have hS := Presheaf.imageSieve_mem Y.J f y
  apply K.isSheaf.isSeparated U.unop _ hS
  rintro V g ⟨x, hx⟩
  have hnat := PresheafOfModules.naturality_apply t g.op (a ⊗ₜ[O.obj.obj U] y)
  have hnat' := PresheafOfModules.naturality_apply t' g.op (a ⊗ₜ[O.obj.obj U] y)
  change t.app (Opposite.op V) (hi.I.val.map g.op a ⊗ₜ[O.obj.obj (Opposite.op V)]
      F.val.map g.op y) = (K.val.map g.op) (t.app U (a ⊗ₜ[O.obj.obj U] y)) at hnat
  change t'.app (Opposite.op V) (hi.I.val.map g.op a ⊗ₜ[O.obj.obj (Opposite.op V)]
      F.val.map g.op y) = (K.val.map g.op) (t'.app U (a ⊗ₜ[O.obj.obj U] y)) at hnat'
  change (K.val.map g.op) (t.app U (a ⊗ₜ[O.obj.obj U] y)) =
    (K.val.map g.op) (t'.app U (a ⊗ₜ[O.obj.obj U] y))
  have hx' : E.g.val.app (Opposite.op V) x = F.val.map g.op y := hx
  have := h (Opposite.op V) (hi.I.val.map g.op a) x
  rw [hx'] at this
  rw [← hnat, ← hnat']
  exact ((hc c _ _ _).symm.trans this).trans (hc c' _ _ _)

/-- If the action map of an extension vanishes, the square-zero ideal annihilates its middle
term. -/
private lemma middle_smul_eq_zero_of_extensionActionMap_eq_zero
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0)
    (h : (extensionActionMap hi E).1 = 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : E.Z.left.val.obj U) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
      from hi.incl.val.app U a) • x = 0 := by
  rw [← (extensionActionMap hi E).property U a x, h]
  show (E.f.val.app U) 0 = 0
  exact map_zero _

/-- Conversely, if the square-zero ideal annihilates the middle term of an extension, the action
map vanishes. -/
private lemma extensionActionMap_eq_zero_of_middle_smul_eq_zero
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0)
    (hE : ∀ (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : E.Z.left.val.obj U),
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
        from hi.incl.val.app U a) • x = 0) :
    (extensionActionMap hi E).1 = 0 := by
  refine eq_of_agree_on_unit_tensor_lifts hi E _ 0 fun U a x => ?_
  rw [extensionActionMap_unit_eq_iff]
  exact (map_zero _).trans (hE U a x).symm

/-- A map of middle terms compatible with the inclusion of the kernel intertwines the two action
maps on local pure tensors. -/
private lemma extensionActionMap_agrees_on_lift
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E E' : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0)
    (φ : E.Z.left ⟶ E'.Z.left)
    (hf : E.f ≫ φ = E'.f)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : E.Z.left.val.obj U) :
    ((extensionActionMap hi E).1.val.app U)
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
            i.toToposHom).obj X.O))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj
            X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val F.val)).app U
          (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U]
            E.g.val.app U x)) =
      ((extensionActionMap hi E').1.val.app U)
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
            i.toToposHom).obj X.O))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj
            X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val F.val)).app U
          (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U]
            E'.g.val.app U (φ.val.app U x))) := by
  have hfU : E.f.val.app U ≫ φ.val.app U = E'.f.val.app U := by
    simpa using congrArg (fun f => f.val.app U) hf
  rw [eq_comm, extensionActionMap_unit_eq_iff, ← hfU]
  have step := (φ.val.app U).hom.map_smul
    (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U a) x
  exact (congrArg (φ.val.app U) ((extensionActionMap hi E).property U a x)).trans step

/-- Two extensions related by a map of middle terms over the identity on both end terms have the
same action map. -/
private lemma extensionActionMap_eq_of_extensionHom
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E E' : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0)
    (φ : E.Z.left ⟶ E'.Z.left)
    (hf : E.f ≫ φ = E'.f) (hg : φ ≫ E'.g = E.g) :
    (extensionActionMap hi E).1 = (extensionActionMap hi E').1 := by
  refine eq_of_agree_on_unit_tensor_lifts hi E _ _ fun U a x => ?_
  have hgU : E'.g.val.app U (φ.val.app U x) = E.g.val.app U x :=
    congrArg (fun q => q.val.app U x) hg
  rw [extensionActionMap_agrees_on_lift hi E E' φ hf U a x, hgU]

/-- The action map depends only on the `Ext¹_O` class of the extension. -/
private lemma extensionActionMap_eq_of_extensionClass_eq
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E E' : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0)
    (h : extensionClass F K E = extensionClass F K E') :
    (extensionActionMap hi E).1 = (extensionActionMap hi E').1 := by
  have hS := yonedaExtension_shortExact E
  have hS' := yonedaExtension_shortExact E'
  have hiso :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K)).2.1
      E.Z.left E'.Z.left E.f E.g _ E'.f E'.g _ hS hS'
  obtain ⟨φ, hf, hg⟩ := hiso.1 h
  exact extensionActionMap_eq_of_extensionHom hi E E' φ.hom hf hg

/-! ### Additivity of the action map in the `Ext` class -/

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- Every `Ext¹_O` class between modules restricted from the thickening is the class of an
extension. -/
private lemma exists_extensionClass_eq
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (x : Abelian.Ext
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 1) :
    ∃ E, extensionClass (i := i) F K E = x := by
  obtain ⟨M, f, g, z, h, hx⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ _ _).1 x
  exact ⟨Abelian.shortExactYonedaExtension h, hx⟩

/-- The action map attached to an `Ext¹_O` class: the action map of any extension representing
it, which by `extensionActionMap_eq_of_extensionClass_eq` does not depend on the choice. -/
private noncomputable def actionOfExt
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (x : Abelian.Ext
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 1) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K :=
  (extensionActionMap hi
    (Classical.choose (exists_extensionClass_eq.{_, _, _, _, _, _, e} F K x))).1

private lemma actionOfExt_extensionClass
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0) :
    actionOfExt hi F K (extensionClass F K E) = (extensionActionMap hi E).1 :=
  extensionActionMap_eq_of_extensionClass_eq hi _ _ (Classical.choose_spec
    (exists_extensionClass_eq.{_, _, _, _, _, _, e} F K (extensionClass F K E)))

/-- The map on the tensor products with the square-zero ideal induced by a map of quotient
modules. This is `Deformation.ToposThickening.idealTensorMap` with the two extensions forgotten;
see `idealTensorMap_eq_idealTensorHom`. -/
noncomputable def idealTensorHom (hi : FirstOrderThickening i)
    {F G : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (β : F ⟶ G) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj G :=
  (PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 hi.I.val) β.val)

/-- The ideal tensor map of two extensions only depends on the thickening and the map of
quotient modules. -/
lemma idealTensorMap_eq_idealTensorHom (D : TwoExtensions i) :
    idealTensorMap D = idealTensorHom D.thickening D.quotientMap :=
  rfl

private lemma idealTensorHom_add (hi : FirstOrderThickening i)
    {F G : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (β γ : F ⟶ G) :
    idealTensorHom hi (β + γ) = idealTensorHom hi β + idealTensorHom hi γ := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
    i.toToposHom).obj X.O)
  have := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).isLeftAdjoint
  have : (PresheafOfModules.sheafification (𝟙 R.obj)).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (show PreservesFiniteColimits (PresheafOfModules.sheafification (𝟙 R.obj)) from
        inferInstance)
  have hval : (β + γ).val = β.val + γ.val := Functor.map_add (SheafOfModules.forget R)
  have hadd : PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 hi.I.val) (β + γ).val =
      PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 hi.I.val) β.val +
        PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 hi.I.val) γ.val := by
    rw [hval]
    apply PresheafOfModules.hom_ext
    intro U
    simp only [PresheafOfModules.add_app]
    exact MonoidalPreadditive.tensor_add _ _ _
  exact (congrArg (fun m => (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).map m)
    hadd).trans (Functor.map_add _)

private lemma actionOfExt_naturality
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    {F G K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (β : F ⟶ G)
    (x : Abelian.Ext
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj G)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 1) :
    actionOfExt hi F K ((Abelian.Ext.mk₀
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).map β)).comp x
        (zero_add 1)) = idealTensorHom hi β ≫ actionOfExt hi G K x := by
  let R := SheafOfModules.restrictScalars.{w'}
    (structureRingMap i)
  obtain ⟨E', hE'⟩ := exists_extensionClass_eq.{_, _, _, _, _, _, e} G K x
  obtain ⟨E, hE⟩ := exists_extensionClass_eq.{_, _, _, _, _, _, e} F K
    ((Abelian.Ext.mk₀ (R.map β)).comp x (zero_add 1))
  obtain ⟨φ, hf, hg⟩ := (yonedaExtension_shortExact E).exists_hom_of_extClass_eq
    (yonedaExtension_shortExact E') (R.map β)
    (by change extensionClass F K E = _; rw [hE, ← hE']; rfl)
  let D : TwoExtensions i :=
    { thickening := hi, F := F, K := K, G := G, L := K
      firstExtension := E, secondExtension := E'
      quotientMap := β, kernelMap := 𝟙 K }
  have hkernel : E.f ≫ φ = R.map (𝟙 K) ≫ E'.f := by
    rwa [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := idealActionMap_naturality D φ hkernel hg
  change (extensionActionMap hi E).1 ≫ 𝟙 K =
    idealTensorHom hi β ≫ (extensionActionMap hi E').1 at hn
  rw [Category.comp_id] at hn
  rwa [← hE, ← hE', actionOfExt_extensionClass, actionOfExt_extensionClass]

private lemma actionOfExt_add
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (x y : Abelian.Ext
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 1) :
    actionOfExt hi F K (x + y) = actionOfExt hi F K x + actionOfExt hi F K y := by
  let R := SheafOfModules.restrictScalars.{w'}
    (structureRingMap i)
  let z := (Abelian.Ext.mk₀ (R.map (biprod.fst : F ⊞ F ⟶ F))).comp x (zero_add 1) +
    (Abelian.Ext.mk₀ (R.map (biprod.snd : F ⊞ F ⟶ F))).comp y (zero_add 1)
  have einl_fst : R.map (biprod.inl : F ⟶ F ⊞ F) ≫ R.map (biprod.fst : F ⊞ F ⟶ F) =
      𝟙 (R.obj F) := by
    rw [← CategoryTheory.Functor.map_comp, biprod.inl_fst, CategoryTheory.Functor.map_id]
  have einl_snd : R.map (biprod.inl : F ⟶ F ⊞ F) ≫ R.map (biprod.snd : F ⊞ F ⟶ F) = 0 := by
    rw [← CategoryTheory.Functor.map_comp, biprod.inl_snd, CategoryTheory.Functor.map_zero]
  have einr_fst : R.map (biprod.inr : F ⟶ F ⊞ F) ≫ R.map (biprod.fst : F ⊞ F ⟶ F) = 0 := by
    rw [← CategoryTheory.Functor.map_comp, biprod.inr_fst, CategoryTheory.Functor.map_zero]
  have einr_snd : R.map (biprod.inr : F ⟶ F ⊞ F) ≫ R.map (biprod.snd : F ⊞ F ⟶ F) =
      𝟙 (R.obj F) := by
    rw [← CategoryTheory.Functor.map_comp, biprod.inr_snd, CategoryTheory.Functor.map_id]
  have h₁ : (Abelian.Ext.mk₀ (R.map (biprod.inl : F ⟶ F ⊞ F))).comp z (zero_add 1) = x := by
    show (Abelian.Ext.mk₀ (R.map (biprod.inl : F ⟶ F ⊞ F))).comp
      ((Abelian.Ext.mk₀ (R.map (biprod.fst : F ⊞ F ⟶ F))).comp x (zero_add 1) +
        (Abelian.Ext.mk₀ (R.map (biprod.snd : F ⊞ F ⟶ F))).comp y (zero_add 1))
      (zero_add 1) = x
    rw [Abelian.Ext.comp_add, Abelian.Ext.mk₀_comp_mk₀_assoc,
      Abelian.Ext.mk₀_comp_mk₀_assoc, einl_fst, einl_snd, Abelian.Ext.mk₀_id_comp,
      Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp, add_zero]
  have h₂ : (Abelian.Ext.mk₀ (R.map (biprod.inr : F ⟶ F ⊞ F))).comp z (zero_add 1) = y := by
    show (Abelian.Ext.mk₀ (R.map (biprod.inr : F ⟶ F ⊞ F))).comp
      ((Abelian.Ext.mk₀ (R.map (biprod.fst : F ⊞ F ⟶ F))).comp x (zero_add 1) +
        (Abelian.Ext.mk₀ (R.map (biprod.snd : F ⊞ F ⟶ F))).comp y (zero_add 1))
      (zero_add 1) = y
    rw [Abelian.Ext.comp_add, Abelian.Ext.mk₀_comp_mk₀_assoc,
      Abelian.Ext.mk₀_comp_mk₀_assoc, einr_fst, einr_snd, Abelian.Ext.mk₀_id_comp,
      Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp, zero_add]
  have hsum : (Abelian.Ext.mk₀ (R.map ((biprod.inl : F ⟶ F ⊞ F) + biprod.inr))).comp z
      (zero_add 1) = x + y := by
    rw [Functor.map_add, Abelian.Ext.mk₀_add, Abelian.Ext.add_comp, h₁, h₂]
  rw [← hsum, actionOfExt_naturality, idealTensorHom_add, Preadditive.add_comp,
    ← actionOfExt_naturality, ← actionOfExt_naturality, h₁, h₂]

/-- The action map as an additive homomorphism out of `Ext¹_O`. -/
private noncomputable def actionExtAddHom
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
        i.toToposHom).obj X.O))) :
    Abelian.Ext
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 1 →+
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K) :=
  AddMonoidHom.mk' (actionOfExt.{_, _, _, _, _, _, e} hi F K) (actionOfExt_add hi F K)

/-- **The action map vanishes exactly on the classes pulled back from the quotient structure
sheaf.** -/
private lemma actionExtAddHom_eq_zero_iff
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (x : Abelian.Ext
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 1) :
    actionExtAddHom.{_, _, _, _, _, _, e} hi F K x = 0 ↔
      ∃ y : Abelian.Ext F K 1,
        (SheafOfModules.restrictScalars
          (structureRingMap i)).mapExtAddHom F K 1 y = x := by
  let R := SheafOfModules.restrictScalars.{w'}
    (structureRingMap i)
  let ff := hi.restrictScalarsFullyFaithful
  have : R.Full := ff.full
  have : R.Faithful := ff.faithful
  constructor
  · intro hx
    obtain ⟨E, hE⟩ := exists_extensionClass_eq.{_, _, _, _, _, _, e} F K x
    have hc : (extensionActionMap hi E).1 = 0 := by
      rwa [← actionOfExt_extensionClass, hE]
    have he : R.essImage E.Z.left :=
      (hi.essImage_restrictScalars_iff E.Z.left).2
        (middle_smul_eq_zero_of_extensionActionMap_eq_zero hi E hc)
    apply Functor.exists_mapExtAddHom_eq_of_essImage R F K x
    exact ⟨E.Z.left, E.f, E.g, _, yonedaExtension_shortExact E, hE, he⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨M, f, g, z, h, hy⟩ :=
      (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ F K).1 y
    let T := (ShortComplex.mk f g z).map R
    have hT : T.ShortExact := h.map_of_exact R
    let E := Abelian.shortExactYonedaExtension hT
    have he : extensionClass F K E = R.mapExtAddHom F K 1 y := by
      rw [Functor.mapExtAddHom_apply, ← hy, Abelian.Ext.mapExactFunctor_extClass]
      rfl
    show actionOfExt hi F K (R.mapExtAddHom F K 1 y) = 0
    rw [← he, actionOfExt_extensionClass]
    apply extensionActionMap_eq_zero_of_middle_smul_eq_zero
    intro U a m
    let : Module (((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U)
        (M.val.obj U) := (M.val.obj U).isModule
    show (i.fSharp.hom.app U
        (show Y.O.obj.obj U from hi.incl.val.app U a)) • (show M.val.obj U from m) = 0
    rw [(hi.kernel U _).2 ⟨a, rfl⟩, zero_smul]

/-! ### The torsor of extensions with a fixed action -/

/-- The isomorphism classes of extensions over the thickening inducing a prescribed action `c`
of the square-zero ideal, presented as the `Ext¹_O` classes realized by such an extension. -/
noncomputable abbrev FixedActionExtensionClass
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K) : Type _ :=
  { ξ : Abelian.Ext
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 1 //
    ∃ E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0,
      (extensionActionMap hi E).1 = c ∧ extensionClass F K E = ξ }

/-- **The classes with a fixed action form a coset.** If `b` is the class of an extension over
the thickening inducing the action `c`, then an `Ext¹_O` class is the class of an extension
inducing `c` exactly when it is `b` plus a class pulled back from `Ext¹_{i_*O'}(F, K)`. This is
the translation action behind `fixedActionExtensionClass_torsor`, made explicit. -/
theorem exists_extensionActionMap_eq_iff_exists_add_mapExtAddHom
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    {c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K}
    (b : FixedActionExtensionClass.{_, _, _, _, _, _, e} hi F K c)
    (x : Abelian.Ext
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 1) :
    (∃ E, (extensionActionMap hi E).1 = c ∧ extensionClass F K E = x) ↔
      ∃ a : Abelian.Ext F K 1, b.val + (SheafOfModules.restrictScalars
        (structureRingMap i)).mapExtAddHom F K 1 a = x := by
  let f := (SheafOfModules.restrictScalars.{w'}
    (structureRingMap i)).mapExtAddHom F K 1
  let d := actionExtAddHom.{_, _, _, _, _, _, e} hi F K
  have hb : d b.val = c := by
    obtain ⟨E, hc, he⟩ := b.property
    show actionOfExt hi F K b.val = c
    rw [← he, actionOfExt_extensionClass, hc]
  have hp : (∃ E, (extensionActionMap hi E).1 = c ∧ extensionClass F K E = x) ↔ d x = c := by
    constructor
    · rintro ⟨E, hc, rfl⟩
      exact (actionOfExt_extensionClass hi E).trans hc
    · intro hx
      obtain ⟨E, he⟩ := exists_extensionClass_eq.{_, _, _, _, _, _, e} F K x
      exact ⟨E, by rwa [← actionOfExt_extensionClass, he], he⟩
  rw [hp]
  constructor
  · intro hx
    have hz : d (x - b.val) = 0 := by rw [map_sub, hx, hb, sub_self]
    obtain ⟨a, ha⟩ := (actionExtAddHom_eq_zero_iff hi F K (x - b.val)).1 hz
    exact ⟨a, by change b.val + f a = x; rw [ha]; abel⟩
  · rintro ⟨a, rfl⟩
    have hz : d (f a) = 0 := (actionExtAddHom_eq_zero_iff hi F K (f a)).2 ⟨a, rfl⟩
    show d (b.val + f a) = c
    rw [map_add, hb, hz, add_zero]

/-- **Stacks 08ME.** If some extension over a first order thickening of ringed topoi induces the
prescribed action `c` of the square-zero ideal, then the isomorphism classes of extensions
inducing `c` form a principal homogeneous space under the first `Ext` group over the quotient
structure sheaf. -/
@[stacks 08ME]
theorem fixedActionExtensionClass_torsor
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K)
    (h : Nonempty (FixedActionExtensionClass.{_, _, _, _, _, _, e} hi F K c)) :
    Nonempty (AddTorsor (Abelian.Ext F K 1)
      (FixedActionExtensionClass.{_, _, _, _, _, _, e} hi F K c)) := by
  let R := SheafOfModules.restrictScalars.{w'} (structureRingMap i)
  let ff := hi.restrictScalarsFullyFaithful
  have : R.Full := ff.full
  have : R.Faithful := ff.faithful
  exact ⟨AddTorsor.ofAddMonoidHomTranslate (R.mapExtAddHom F K 1)
    (Functor.mapExtAddHom_injective_of_fullyFaithful R F K) h.some.val _
    (exists_extensionActionMap_eq_iff_exists_add_mapExtAddHom hi h.some)⟩

end Deformation.ToposThickening

end
