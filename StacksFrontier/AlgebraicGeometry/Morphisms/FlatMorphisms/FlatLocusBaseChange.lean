module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewiseFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Module
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksCore.Tactic.StacksAttribute

/-!
# The relative flat locus and base change

For a cartesian square of schemes, pullback preserves flatness of a quasi-coherent module
relative to the base at a point. Over a base morphism which is flat at the relevant point,
relative flatness also descends. Consequently the open flat locus of a finitely presented
quasi-coherent module over a morphism locally of finite presentation commutes with flat base
change.

For a morphism `f : X ⟶ Y` of schemes over a base `S` with `X` locally of finite presentation
over `S` and `Y` locally of finite type over `S`, and a quasi-coherent `𝒪_X`-module `F` of
finite presentation which is flat over `S`, the locus where `F` is flat over `Y` is open and its
formation commutes with an *arbitrary* base change `S' ⟶ S`, flat or not.

## Main results

* `AlgebraicGeometry.isFlatAt_pullback_fst_of_isFlatAt`: the first projection of a fibre
  product of schemes is flat at a point whenever the opposite base morphism is flat at the
  image of that point.
* `AlgebraicGeometry.modulePullback_isFlatOverAt_of_isFlatOverAt` is preservation of relative
  flatness at a point under an arbitrary base change.
* `AlgebraicGeometry.isFlatOverAt_of_modulePullback` is descent of relative flatness at a
  point along a base morphism flat there.
* `AlgebraicGeometry.setOf_isFlatOverAt_modulePullback` identifies the relative flat locus of
  the pulled-back module with the preimage of the relative flat locus under flat base change.
* `AlgebraicGeometry.isOpen_setOf_isFlatOverAt_modulePullback` is openness of the relative flat
  locus after an arbitrary base change.
* `AlgebraicGeometry.isOpen_setOf_isFlatOverAt_of_locallyOfFiniteType` is openness of the locus
  where a module is flat over an intermediate scheme of finite type over the base.
* `AlgebraicGeometry.setOf_isFlatOverAt_modulePullback_of_isFlatOver` identifies that locus after
  an arbitrary base change with the preimage of the original locus.

## Implementation notes

Preservation of relative flatness under an arbitrary base change is proved as
`AlgebraicGeometry.modulePullback_isFlatOverAt`, of which
`AlgebraicGeometry.modulePullback_isFlatOverAt_of_isFlatOverAt` is a restatement. The
identification of the two loci is
pointwise and needs no finite presentation hypotheses, while openness of the base-changed locus
follows from openness over the new base, since finite presentation of both the morphism and the
module is inherited by the base change.

Over an arbitrary, not necessarily flat, base morphism the identification of the two loci is
obtained by passing to the fibres over a point of the new base: flatness of the module over the
base lets the fibrewise criterion
`Stacks.Flatness.isFlatOverBaseAndFiberAt_iff` replace flatness over the intermediate scheme by
flatness on the fibre, and the comparison of fibres is a base change of an extension of residue
fields, hence flat. A point at which the stalk of the module vanishes lies in both loci, which is
why no nonvanishing hypothesis is needed.

The base change is presented by a cartesian square over the intermediate scheme together with one
presenting the intermediate scheme over the new base; pasting them exhibits the new source as the
base change of the old one.

## References

* [Stacks Project, Tag 047C](https://stacks.math.columbia.edu/tag/047C)
* [Stacks Project, Tag 05VJ](https://stacks.math.columbia.edu/tag/05VJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- The first projection out of a fibre product of schemes is flat at a point as soon as the
base morphism it is pulled back along is flat at the image of that point, since the local ring
of the fibre product is a localization of the tensor product of the local rings of the other
three corners. -/
public lemma isFlatAt_pullback_fst_of_isFlatAt
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (t : (Limits.pullback f g).carrier)
    (hg : IsFlatAt g.toLRSHom.toShHom ((Limits.pullback.snd f g).base t)) :
    IsFlatAt (Limits.pullback.fst f g).toLRSHom.toShHom t := by
  let pX : Limits.pullback f g ⟶ X := Limits.pullback.fst f g
  let pY : Limits.pullback f g ⟶ S' := Limits.pullback.snd f g
  let hsq : (pX ≫ f).base t = (pY ≫ g).base t :=
    congrArg (fun k : Limits.pullback f g ⟶ S => k.base t) Limits.pullback.condition
  let R := S.presheaf.stalk ((pX ≫ f).base t)
  let A := X.presheaf.stalk (pX.base t)
  let B := S'.presheaf.stalk (pY.base t)
  let C := (Limits.pullback f g).presheaf.stalk t
  let _ : Algebra R A := (f.stalkMap (pX.base t)).hom.toAlgebra
  let _ : Algebra R B :=
    ((eqToHom (congrArg S.presheaf.stalk hsq)) ≫ g.stalkMap (pY.base t)).hom.toAlgebra
  let _ : Module.Flat R B := by
    change (((g.stalkMap (pY.base t)).hom).comp
      (eqToHom (congrArg S.presheaf.stalk hsq)).hom).Flat
    exact RingHom.Flat.comp (.of_bijective (ConcreteCategory.bijective_of_isIso _)) hg
  obtain ⟨φ, hleft, -, M, hlocal⟩ := BaseChangeStalk.pullback_stalk_isLocalization f g t
  let T := TensorProduct R A B
  let _ : Algebra T C := φ.toAlgebra
  let _ : IsLocalization M C := hlocal
  let _ : Algebra A T := inferInstance
  let _ : Algebra A C := (φ.comp (algebraMap A T)).toAlgebra
  let _ : IsScalarTower A T C := IsScalarTower.of_algebraMap_eq' rfl
  let _ : Module.Flat A T := inferInstance
  let _ : Module.Flat T C := IsLocalization.flat C M
  have hAC : Module.Flat A C := Module.Flat.trans A T C
  change (φ.comp (algebraMap A T)).Flat at hAC
  change ((pX.stalkMap t).hom).Flat
  rw [← hleft]
  exact hAC

/-- **Stacks Project, Tag 047C (1).** For a cartesian square of schemes a quasi-coherent module
which is flat over the base at the image of a point pulls back to a module which is flat over the
new base at that point. Nothing is assumed of the base morphism, so this holds for an arbitrary
base change. This is a restatement of `AlgebraicGeometry.modulePullback_isFlatOverAt`. -/
@[stacks 047C "part (1)"]
public lemma modulePullback_isFlatOverAt_of_isFlatOverAt
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (h : IsPullback g' f' f g)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (x' : X') (hF : IsFlatOverAt f.toLRSHom.toShHom F (g' x')) :
    IsFlatOverAt f'.toLRSHom.toShHom ((modulePullback g'.toLRSHom.toShHom).obj F) x' :=
  modulePullback_isFlatOverAt h F x' hF

/-- **Stacks Project, Tag 047C (2).** Relative flatness of the pullback of a quasi-coherent
module along a cartesian square descends at a point at which the base morphism is flat. -/
@[stacks 047C "part (2)", sga "3 V 7.4" "(i) descent"]
public lemma isFlatOverAt_of_modulePullback
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (h : IsPullback g' f' f g)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (x' : X') (hg : IsFlatAt g.toLRSHom.toShHom (f' x'))
    (hF : IsFlatOverAt f'.toLRSHom.toShHom
      ((modulePullback g'.toLRSHom.toShHom).obj F) x') :
    IsFlatOverAt f.toLRSHom.toShHom F (g' x') := by
  let e := h.isoPullback
  let t := e.hom.base x'
  have hpoint : f'.base x' = (Limits.pullback.snd f g).base t :=
    (congrArg (fun k : X' ⟶ S' => k.base x') h.isoPullback_hom_snd).symm
  have hg' : IsFlatAt g.toLRSHom.toShHom ((Limits.pullback.snd f g).base t) := by
    change (g.stalkMap ((Limits.pullback.snd f g).base t)).hom.Flat
    change (g.stalkMap (f'.base x')).hom.Flat at hg
    rw [← hpoint]
    exact hg
  have hpflat := isFlatAt_pullback_fst_of_isFlatAt f g t hg'
  have hgpflat : IsFlatAt g'.toLRSHom.toShHom x' := by
    change (g'.stalkMap x').hom.Flat
    rw [← show e.hom ≫ Limits.pullback.fst f g = g' by
      simp [e, h.isoPullback_hom_fst], Scheme.Hom.stalkMap_comp]
    change (e.hom.stalkMap x').hom.comp ((Limits.pullback.fst f g).stalkMap t).hom |>.Flat
    exact RingHom.Flat.comp hpflat
      (.of_bijective (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap x')))
  apply (isFlatOverAt_iff_modulePullback_isFlatOverAt g' f F x' hgpflat).2
  change IsFlatOverAt (g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom)
    ((modulePullback g'.toLRSHom.toShHom).obj F) x'
  rw [← show f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom =
      g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom by
    simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
      (congrArg (fun k : X' ⟶ S => k.toLRSHom.toShHom) h.w).symm]
  exact IsFlatOverAt.comp f'.toLRSHom.toShHom g.toLRSHom.toShHom
    ((modulePullback g'.toLRSHom.toShHom).obj F) x' hF hg

/-- **Stacks Project, Tag 047C (flat locus).** Under flat base change the relative flat locus
of a quasi-coherent module is the preimage of the relative flat locus of the module itself. -/
@[stacks 047C "flat locus"]
public theorem setOf_isFlatOverAt_modulePullback
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (h : IsPullback g' f' f g)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    [Flat g] :
    {x' : X' | IsFlatOverAt f'.toLRSHom.toShHom
      ((modulePullback g'.toLRSHom.toShHom).obj F) x'} =
      g' ⁻¹' {x : X | IsFlatOverAt f.toLRSHom.toShHom F x} := by
  ext x'
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · intro hF
    exact isFlatOverAt_of_modulePullback h F x'
      (by change (g.stalkMap (f' x')).hom.Flat; exact Flat.stalkMap g (f' x')) hF
  · exact modulePullback_isFlatOverAt h F x'

/-- **Stacks Project, Tag 047C (open locus).** The relative flat locus of the pullback of a
finitely presented quasi-coherent module along any base change of a morphism locally of finite
presentation is open. Together with
`AlgebraicGeometry.setOf_isFlatOverAt_modulePullback` this says that the open subset of
[Stacks, Tag 0399] commutes with flat base change. -/
@[stacks 047C "open locus after base change", ega "IV 11.3.1" "more general"]
public theorem isOpen_setOf_isFlatOverAt_modulePullback
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (h : IsPullback g' f' f g)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    [F.IsFinitePresentation] [LocallyOfFinitePresentation f] :
    IsOpen {x' : X' | IsFlatOverAt f'.toLRSHom.toShHom
      ((modulePullback g'.toLRSHom.toShHom).obj F) x'} := by
  let F' : X'.Modules := (modulePullback g'.toLRSHom.toShHom).obj F
  let _ : F'.IsQuasicoherent := SheafOfModules.modulePullback_isQuasicoherent _ F
  let _ : F'.IsFinitePresentation :=
    Stacks.SheafOfModules.modulePullback_isFinitePresentation _ F
  have : LocallyOfFinitePresentation f' := by
    have : LocallyOfFinitePresentation (Limits.pullback.snd f g) := inferInstance
    have : LocallyOfFinitePresentation h.isoPullback.hom := inferInstance
    rw [show f' = h.isoPullback.hom ≫ Limits.pullback.snd f g by simp]
    infer_instance
  exact isOpen_setOf_flatOverAt f' F'

/-- A module whose stalk at a point is zero is flat over the target at that point, the zero
module being free. -/
private lemma isFlatOverAt_of_stalk_eq_zero {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X)) (x : X)
    (h0 : ∀ a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x, a = 0) :
    IsFlatOverAt f F x := by
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  have : Subsingleton
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)) :=
    ⟨fun a b => by rw [h0 a, h0 b]⟩
  let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) := inferInstance
  let : Module (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  exact inferInstance

/-- After a base change `S' ⟶ S`, the fibres over a point of `S'` compare with the fibres over its
image in `S` by a cartesian square whose lower edge is flat, being a base change of an extension
of residue fields. -/
private lemma exists_isPullback_fiberHom_baseChange
    {X Y S S' X' Y' : Scheme.{u}} {f : X ⟶ Y} {pY : Y ⟶ S} {g : S' ⟶ S}
    {qY : Y' ⟶ Y} {pY' : Y' ⟶ S'} {qX : X' ⟶ X} {f' : X' ⟶ Y'}
    (hY : IsPullback qY pY' pY g) (hX : IsPullback qX f' f qY) (s' : S') :
    ∃ (eX : (f' ≫ pY').fiber s' ⟶ (f ≫ pY).fiber (g s'))
      (eY : pY'.fiber s' ⟶ pY.fiber (g s')),
      IsPullback eX (Stacks.Flatness.fiberHom f' pY' s')
        (Stacks.Flatness.fiberHom f pY (g s')) eY ∧
      eX ≫ (f ≫ pY).fiberι (g s') = (f' ≫ pY').fiberι s' ≫ qX ∧ Flat eY := by
  have hXS : IsPullback qX (f' ≫ pY') (f ≫ pY) g := hX.paste_vert hY
  obtain ⟨eX, hbX, hAX⟩ :
      ∃ eX : (f' ≫ pY').fiber s' ⟶ (f ≫ pY).fiber (g s'),
        IsPullback eX ((f' ≫ pY').fiberToSpecResidueField s')
          ((f ≫ pY).fiberToSpecResidueField (g s')) (Spec.map (g.residueFieldMap s')) ∧
        eX ≫ (f ≫ pY).fiberι (g s') = (f' ≫ pY').fiberι s' ≫ qX :=
    ⟨_, isPullback_fiberToSpecResidueField_of_isPullback hXS s', Limits.pullback.lift_fst ..⟩
  obtain ⟨eY, hbY, hAY⟩ :
      ∃ eY : pY'.fiber s' ⟶ pY.fiber (g s'),
        IsPullback eY (pY'.fiberToSpecResidueField s')
          (pY.fiberToSpecResidueField (g s')) (Spec.map (g.residueFieldMap s')) ∧
        eY ≫ pY.fiberι (g s') = pY'.fiberι s' ≫ qY :=
    ⟨_, isPullback_fiberToSpecResidueField_of_isPullback hY s', Limits.pullback.lift_fst ..⟩
  have hcomm : eX ≫ Stacks.Flatness.fiberHom f pY (g s') =
      Stacks.Flatness.fiberHom f' pY' s' ≫ eY := by
    refine Limits.pullback.hom_ext ?_ ?_
    · change eX ≫ Stacks.Flatness.fiberHom f pY (g s') ≫ pY.fiberι (g s') =
        (Stacks.Flatness.fiberHom f' pY' s' ≫ eY) ≫ pY.fiberι (g s')
      calc eX ≫ Stacks.Flatness.fiberHom f pY (g s') ≫ pY.fiberι (g s')
          = (eX ≫ (f ≫ pY).fiberι (g s')) ≫ f := by
            rw [Stacks.Flatness.fiberHom_fiberι f pY (g s'), Category.assoc]
        _ = ((f' ≫ pY').fiberι s' ≫ qX) ≫ f := by rw [hAX]
        _ = (f' ≫ pY').fiberι s' ≫ f' ≫ qY := by rw [Category.assoc, hX.w]
        _ = (Stacks.Flatness.fiberHom f' pY' s' ≫ pY'.fiberι s') ≫ qY := by
            rw [Stacks.Flatness.fiberHom_fiberι f' pY' s', Category.assoc]
        _ = (Stacks.Flatness.fiberHom f' pY' s' ≫ eY) ≫ pY.fiberι (g s') := by
            rw [Category.assoc, ← hAY, Category.assoc]
    · change eX ≫ Stacks.Flatness.fiberHom f pY (g s') ≫ pY.fiberToSpecResidueField (g s') =
        (Stacks.Flatness.fiberHom f' pY' s' ≫ eY) ≫ pY.fiberToSpecResidueField (g s')
      calc eX ≫ Stacks.Flatness.fiberHom f pY (g s') ≫ pY.fiberToSpecResidueField (g s')
          = eX ≫ (f ≫ pY).fiberToSpecResidueField (g s') := by
            rw [Stacks.Flatness.fiberHom_fiberToSpecResidueField]
        _ = (f' ≫ pY').fiberToSpecResidueField s' ≫ Spec.map (g.residueFieldMap s') := hbX.w
        _ = (Stacks.Flatness.fiberHom f' pY' s' ≫ pY'.fiberToSpecResidueField s') ≫
              Spec.map (g.residueFieldMap s') := by
          rw [Stacks.Flatness.fiberHom_fiberToSpecResidueField]
        _ = (Stacks.Flatness.fiberHom f' pY' s' ≫ eY) ≫
              pY.fiberToSpecResidueField (g s') := by
            rw [Category.assoc, ← hbY.w, Category.assoc]
  refine ⟨eX, eY, ?_, hAX, MorphismProperty.of_isPullback hbY.flip inferInstance⟩
  have houter := (Stacks.Flatness.isPullback_fiberHom f' pY' s').flip.paste_horiz hX
  rw [← hAX, ← hAY] at houter
  exact IsPullback.of_right houter hcomm (Stacks.Flatness.isPullback_fiberHom f pY (g s')).flip

/-- Flatness over the base together with flatness on the fibre, with the point of the base given
by an equation identifying it with the image of the point of the source. -/
private lemma isFlatOverBaseAndFiberAt_of_eq {X Y S : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (x : X) (s : S)
    (hs : (f ≫ pY) x = s)
    (hbase : IsFlatOverAt (f ≫ pY).toLRSHom.toShHom F x)
    (hfib : IsFlatOverAt (Stacks.Flatness.fiberHom f pY s).toLRSHom.toShHom
      ((modulePullback ((f ≫ pY).fiberι s).toLRSHom.toShHom).obj F)
      (hs ▸ (f ≫ pY).asFiber x)) :
    Stacks.Flatness.IsFlatOverBaseAndFiberAt f pY F x := by
  cases hs
  exact ⟨hbase, hfib⟩

/-- A point of a fibre is the one determined by a point of the source as soon as the inclusion of
the fibre carries it to that point. -/
private lemma asFiber_eq_of_fiberι_eq {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (z : f.fiber s)
    (y : X) (hy : f y = s) (h : y = f.fiberι s z) : hy ▸ f.asFiber y = z := by
  cases hy
  exact (f.fiberι _).isEmbedding.injective (by simpa using h)

/-- **Stacks Project, Tag 05VJ (open locus).** For a morphism `f : X ⟶ Y` of schemes over a base
with `X` locally of finite presentation over the base and `Y` locally of finite type over it, the
locus where a finitely presented quasi-coherent `𝒪_X`-module is flat over `Y` is open, because `f`
is then itself locally of finite presentation. -/
@[stacks 05VJ "open locus"]
public theorem isOpen_setOf_isFlatOverAt_of_locallyOfFiniteType {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (pY : Y ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    [F.IsFinitePresentation] [LocallyOfFinitePresentation (f ≫ pY)] [LocallyOfFiniteType pY] :
    IsOpen {x : X | IsFlatOverAt f.toLRSHom.toShHom F x} := by
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation_of_comp f pY
  let F₀ : X.Modules := F
  have : F₀.IsQuasicoherent := ‹F.IsQuasicoherent›
  have : F₀.IsFinitePresentation := ‹F.IsFinitePresentation›
  exact isOpen_setOf_flatOverAt f F₀

/-- **Stacks Project, Tag 05VJ (base change).** For a morphism `f : X ⟶ Y` of schemes over a base
`S` with `X` locally of finite presentation over `S` and `Y` locally of finite type over `S`, and
a finitely presented quasi-coherent `𝒪_X`-module flat over `S`, the locus where the module is flat
over `Y` commutes with an arbitrary base change `S' ⟶ S`: the corresponding locus upstairs is the
preimage of the original one. -/
@[stacks 05VJ "base change"]
public theorem setOf_isFlatOverAt_modulePullback_of_isFlatOver
    {X Y S S' X' Y' : Scheme.{u}} {f : X ⟶ Y} {pY : Y ⟶ S} {g : S' ⟶ S}
    {qY : Y' ⟶ Y} {pY' : Y' ⟶ S'} {qX : X' ⟶ X} {f' : X' ⟶ Y'}
    (hY : IsPullback qY pY' pY g) (hX : IsPullback qX f' f qY)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    [F.IsFinitePresentation] [LocallyOfFinitePresentation (f ≫ pY)] [LocallyOfFiniteType pY]
    (hF : IsFlatOver (f ≫ pY).toLRSHom.toShHom F) :
    {x' : X' | IsFlatOverAt f'.toLRSHom.toShHom
        ((modulePullback qX.toLRSHom.toShHom).obj F) x'} =
      qX ⁻¹' {x : X | IsFlatOverAt f.toLRSHom.toShHom F x} := by
  have hXS : IsPullback qX (f' ≫ pY') (f ≫ pY) g := hX.paste_vert hY
  ext x'
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  refine ⟨fun hG => ?_, modulePullback_isFlatOverAt hX F x'⟩
  by_cases hx : ∃ a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      F.val.presheaf (qX x'), a ≠ 0
  · obtain ⟨eX, eY, hcart, hAX, hflatY⟩ :=
      exists_isPullback_fiberHom_baseChange hY hX ((f' ≫ pY') x')
    have hGqc : ((modulePullback qX.toLRSHom.toShHom).obj F).IsQuasicoherent :=
      SheafOfModules.modulePullback_isQuasicoherent qX.toLRSHom.toShHom F
    have hMDqc : ((modulePullback
        ((f ≫ pY).fiberι (g ((f' ≫ pY') x'))).toLRSHom.toShHom).obj F).IsQuasicoherent :=
      SheafOfModules.modulePullback_isQuasicoherent _ F
    have hfibG : IsFlatOverAt
        (Stacks.Flatness.fiberHom f' pY' ((f' ≫ pY') x')).toLRSHom.toShHom
        ((modulePullback ((f' ≫ pY').fiberι ((f' ≫ pY') x')).toLRSHom.toShHom).obj
          ((modulePullback qX.toLRSHom.toShHom).obj F))
        ((f' ≫ pY').asFiber x') :=
      modulePullback_isFlatOverAt
        (Stacks.Flatness.isPullback_fiberHom f' pY' ((f' ≫ pY') x')).flip _
        ((f' ≫ pY').asFiber x')
        (by simpa only [Scheme.Hom.fiberι_asFiber] using hG)
    have hmod :
        (modulePullback ((f' ≫ pY').fiberι ((f' ≫ pY') x')).toLRSHom.toShHom).obj
            ((modulePullback qX.toLRSHom.toShHom).obj F) ≅
          (modulePullback eX.toLRSHom.toShHom).obj
            ((modulePullback
              ((f ≫ pY).fiberι (g ((f' ≫ pY') x'))).toLRSHom.toShHom).obj F) :=
      (schemeModulePullbackCompIso ((f' ≫ pY').fiberι ((f' ≫ pY') x')) qX).app F ≪≫
        eqToIso (congrArg (fun k : (f' ≫ pY').fiber ((f' ≫ pY') x') ⟶ X =>
          (modulePullback k.toLRSHom.toShHom).obj F) hAX.symm) ≪≫
        ((schemeModulePullbackCompIso eX
          ((f ≫ pY).fiberι (g ((f' ≫ pY') x')))).app F).symm
    have hfibF : IsFlatOverAt
        (Stacks.Flatness.fiberHom f pY (g ((f' ≫ pY') x'))).toLRSHom.toShHom
        ((modulePullback
          ((f ≫ pY).fiberι (g ((f' ≫ pY') x'))).toLRSHom.toShHom).obj F)
        (eX ((f' ≫ pY').asFiber x')) :=
      isFlatOverAt_of_modulePullback hcart _ ((f' ≫ pY').asFiber x')
        (Flat.stalkMap eY _) (isFlatOverAt_of_moduleIso _ hmod _ hfibG)
    have hbaseEq : (f ≫ pY) (qX x') = g ((f' ≫ pY') x') := by
      simpa using congrArg (fun k : X' ⟶ S => k x') hXS.w
    have hpoint : hbaseEq ▸ (f ≫ pY).asFiber (qX x') = eX ((f' ≫ pY').asFiber x') :=
      asFiber_eq_of_fiberι_eq (f ≫ pY) (g ((f' ≫ pY') x'))
        (eX ((f' ≫ pY').asFiber x')) (qX x') hbaseEq
        (by
          have h : ((f' ≫ pY').fiberι ((f' ≫ pY') x') ≫ qX) ((f' ≫ pY').asFiber x') =
              (eX ≫ (f ≫ pY).fiberι (g ((f' ≫ pY') x'))) ((f' ≫ pY').asFiber x') := by
            rw [hAX]
          simpa only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber] using h)
    exact ((Stacks.Flatness.isFlatOverBaseAndFiberAt_iff f pY F (qX x') hx).mp
      (isFlatOverBaseAndFiberAt_of_eq f pY F (qX x') (g ((f' ≫ pY') x')) hbaseEq
        (hF (qX x')) (hpoint ▸ hfibF))).2
  · exact isFlatOverAt_of_stalk_eq_zero _ F (qX x')
      (by simpa only [not_exists, not_not] using hx)

end AlgebraicGeometry
