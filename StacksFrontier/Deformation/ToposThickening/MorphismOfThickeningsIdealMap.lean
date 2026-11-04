module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposUnitStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseFactorisation
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickenings

/-!
# The induced map of defining ideals of a morphism of thickenings of ringed topoi

Let

```
  (Sh(C), O)  --i-->  (Sh(D), O')
      |                   |
      f                   f'
      v                   v
  (Sh(B), O_B) --t--> (Sh(B'), O_{B'})
```

be a morphism of thickenings of ringed topoi (Stacks 08M7), with defining ideals
`I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`. The structure map of `f'` carries `J` into
`I`, and so induces a map of `O'`-modules

`(f')^*J ⟶ I`.

This file constructs that map, characterises it, and proves it is the only map of ideals whose
composite into `O'` is the structure map of `f'` applied to the inclusion of `J`. Stacks 08M9,
strictness of a morphism of thickenings, is the assertion that it is an epimorphism.

## The engine

The composite `(f')^*J ⟶ (f')^*O_{B'} ⟶ O'`, where the second map is the canonical comparison
`AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap`, is killed by `i^♯`. That is
checked on the direct-image side, where the adjunction `(f')^* ⊣ (f')_*` turns it into the
statement that `J ⟶ O_{B'} ⟶ (f')_*O'⟶ (f')_*i_*O` vanishes; and there the composition formula
`AlgebraicGeometry.RingedToposHom.unitStructureMap_comp` for the unit-module structure map
rewrites the composite as the unit-module structure map of `f' ∘ i`, which by the commutative
square is that of `t ∘ f`, and which therefore factors through `t^♯` — and `J` is the kernel of
`t^♯`.

Once the composite lands in `I` sectionwise, the map of ideals is the unique factorisation of
`Stacks.SheafOfModules.existsUnique_factorThrough` through the sectionwise injective inclusion
`I ⟶ O'`.

## Main definitions

* `Deformation.ToposThickening.MorphismOfThickenings.pullbackIdealToStructure`: the composite
  `(f')^*J ⟶ O'`.
* `Deformation.ToposThickening.MorphismOfThickenings.IsCanonicalIdealMap`: the normalisation
  that pins the map of ideals down — its composite into `O'` is the above.
* `Deformation.ToposThickening.MorphismOfThickenings.idealMap`: **Stacks 08M7**, the induced
  map `(f')^*J ⟶ I`.
* `Deformation.ToposThickening.MorphismOfThickenings.IsStrict`: **Stacks 08M9**, strictness.
* `Deformation.ToposThickening.MorphismOfThickenings.pullbackComparison`: the canonical
  comparison of the two iterated pullbacks around the square.

## Main results

* `Deformation.ToposThickening.IdealOfThickening.incl_comp_unitStructureMap`: the defining
  ideal of a thickening is killed by the unit-module structure map, as a morphism of sheaves of
  modules and not merely sectionwise.
* `Deformation.ToposThickening.MorphismOfThickenings.canonicalIdealMap_existsUnique`:
  **Stacks 08M7**, there is exactly one map of ideals with the normalisation above.
* `Deformation.ToposThickening.MorphismOfThickenings.idealMap_spec` and
  `.homEquiv_idealMap_comp_incl`: the two readings of that normalisation — on the source topos,
  the composite into `O'`; on the target topos, the adjoint transpose is the structure map
  `(f')^♯` applied to the inclusion of `J`. The second is the source's own description of the
  map.

## Implementation notes

The vanishing of `J ⟶ (f')_*i_*O` is stated through an auxiliary morphism `k` with a
hypothesis `k = t ∘ f` rather than by rewriting with the commutativity of the square: the
target of the unit-module structure map of a morphism of ringed topoi depends on that morphism,
so substituting one composite for the other is a transport, and `subst` performs it where `rw`
would have to build a motive.

The defining ideals are carried as data, with their characterizing sectionwise property, as in
`Deformation.ToposThickening.IdealOfThickening`; nothing here names a kernel object, so no
sheafification hypothesis beyond the ones the pullback of sheaves of modules already needs is
required of the two upper topoi, and none at all of the two lower ones.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.RingedToposHom (unitStructureMap pullbackUnitStructureMap
  pushforwardModules pullbackAdjPushforwardModules)

universe v u w v' u' w' v'' u'' w'' v''' u''' w'''

namespace Deformation.ToposThickening

section Thickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The defining ideal of a thickening is killed by the structure map read on unit modules:
`I ⟶ O' ⟶ i_*O` is zero.

`Deformation.ToposThickening.IdealOfThickening.fSharp_incl_apply` is the same statement on
sections; this is the form in which it is composed with other morphisms of sheaves of
modules. -/
theorem IdealOfThickening.incl_comp_unitStructureMap {i : RingedToposHom X Y}
    (hI : IdealOfThickening i) : hI.incl ≫ unitStructureMap i = 0 :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun b ↦
      (RingedToposHom.unitStructureMap_val_app i U _).trans (hI.fSharp_incl_apply U b)))

end Thickening

namespace MorphismOfThickenings

section Vanishing

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w'}}
  {S : RingedTopos.{v'', u'', w''}} {S' : RingedTopos.{v''', u''', w'''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w'})]
  [S.J.HasSheafCompose (forget RingCat.{w''})] [S'.J.HasSheafCompose (forget RingCat.{w'''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{w'''} RingCat.{w'''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w'''})]
  (D : MorphismOfThickenings X X' S S')

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The lower defining ideal `J` is killed by the unit-module structure map of any morphism of
ringed topoi equal to `t ∘ f`.

The hypothesis is stated as an equation rather than taking `t ∘ f` itself because the only
morphism it will be applied to is `f' ∘ i`, which is equal to `t ∘ f` by the commutativity of
the square but not by definition, and the target of the structure map depends on the
morphism. -/
theorem idealJ_incl_comp_unitStructureMap_of_eq {k : RingedToposHom X S'}
    (hk : k = D.t.comp D.f) : D.idealJ.incl ≫ unitStructureMap k = 0 := by
  subst hk
  have key : (D.idealJ.incl ≫ unitStructureMap (D.t.comp D.f)) ≫
      (RingedToposHom.pushforwardModulesCompIso D.f D.t).hom.app
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) = 0 := by
    rw [Category.assoc, RingedToposHom.unitStructureMap_comp D.t D.f, ← Category.assoc,
      D.idealJ.incl_comp_unitStructureMap, Limits.zero_comp]
  simpa using congrArg (fun m ↦ m ≫ (RingedToposHom.pushforwardModulesCompIso D.f D.t).inv.app
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) key

/-- **The structure map of `f'` carries `J` into the kernel of `i^♯`**, in the direct-image
form: `J ⟶ O_{B'} ⟶ (f')_*O' ⟶ (f')_*i_*O` is zero.

This is where the commutative square is used: the composite of the two unit-module structure
maps is the unit-module structure map of `f' ∘ i`, which is that of `t ∘ f`, and `J` is the
kernel ideal of `t^♯`. -/
theorem idealJ_incl_comp_unitStructureMap_comp :
    D.idealJ.incl ≫ unitStructureMap D.f' ≫
      (pushforwardModules D.f').map (unitStructureMap D.i) = 0 := by
  rw [← RingedToposHom.unitStructureMap_comp D.f' D.i, ← Category.assoc,
    D.idealJ_incl_comp_unitStructureMap_of_eq D.comm, Limits.zero_comp]

end Vanishing

section IdealMap

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w'}}
  {S : RingedTopos.{v'', u'', w''}} {S' : RingedTopos.{v''', u''', w'''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w'})]
  [S.J.HasSheafCompose (forget RingCat.{w''})] [S'.J.HasSheafCompose (forget RingCat.{w'''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{w'''} RingCat.{w'''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w'''})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w'}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (D : MorphismOfThickenings X X' S S')

/-- The composite `(f')^*J ⟶ (f')^*O_{B'} ⟶ O'`: the pullback of the inclusion of the lower
defining ideal, followed by the canonical comparison
`AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap` of the pullback of the structure
sheaf with the structure sheaf. The map of ideals is its unique factorisation through `I`. -/
noncomputable def pullbackIdealToStructure :
    (D.f'.toModulesHom.pullbackModules).obj D.idealJ.I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X'.O) :=
  (D.f'.toModulesHom.pullbackModules).map D.idealJ.incl ≫ pullbackUnitStructureMap D.f'

/-- **The composite `(f')^*J ⟶ O'` is killed by `i^♯`.** Transposed across the adjunction
`(f')^* ⊣ (f')_*` this is
`Deformation.ToposThickening.MorphismOfThickenings.idealJ_incl_comp_unitStructureMap_comp`. -/
theorem pullbackIdealToStructure_comp_unitStructureMap :
    D.pullbackIdealToStructure ≫ unitStructureMap D.i = 0 := by
  refine ((pullbackAdjPushforwardModules D.f').homEquiv _ _).injective ?_
  rw [Adjunction.homAddEquiv_zero, Adjunction.homEquiv_naturality_right,
    pullbackIdealToStructure,
    RingedToposHom.homEquiv_map_comp_pullbackUnitStructureMap D.f' D.idealJ.incl,
    Category.assoc, D.idealJ_incl_comp_unitStructureMap_comp]

/-- Equal morphisms of sheaves of modules agree on every local section. -/
private theorem val_app_apply_congr {C : Type*} [Category C] {K : GrothendieckTopology C}
    {R : Sheaf K RingCat} {M N : SheafOfModules R} {f g : M ⟶ N} (h : f = g) (U : Cᵒᵖ)
    (z : M.val.obj U) : f.val.app U z = g.val.app U z := by
  rw [h]

/-- Every local section of `(f')^*J`, read in `O'`, is killed by the structure map of `i`, and
so is a section of the upper defining ideal. -/
theorem fSharp_pullbackIdealToStructure_apply (U : X'.Cᵒᵖ)
    (z : ((D.f'.toModulesHom.pullbackModules).obj D.idealJ.I).val.obj U) :
    D.i.fSharp.hom.app U (D.pullbackIdealToStructure.val.app U z) = 0 :=
  (RingedToposHom.unitStructureMap_val_app D.i U _).symm.trans
    (val_app_apply_congr D.pullbackIdealToStructure_comp_unitStructureMap U z)

/-- The normalisation of the induced map of defining ideals: its composite with the inclusion
`I ⟶ O'` is the structure map of `f'` applied to the inclusion `J ⟶ O_{B'}`.

`Deformation.ToposThickening.MorphismOfThickenings.homEquiv_idealMap_comp_incl` reads the same
condition on the target topos, where it says literally that the map is `(f')^♯` on `J`. -/
def IsCanonicalIdealMap
    (φ : (D.f'.toModulesHom.pullbackModules).obj D.idealJ.I ⟶ D.idealI.I) : Prop :=
  φ ≫ D.idealI.incl = D.pullbackIdealToStructure

/-- **Stacks 08M7.** There is exactly one map of `O'`-modules `(f')^*J ⟶ I` whose composite into
`O'` is the structure map of `f'` applied to the inclusion of `J`.

Existence is the factorisation of
`Stacks.SheafOfModules.existsUnique_factorThrough`: every local section of `(f')^*J`, read in
`O'`, is killed by `i^♯`, hence lies in `I`. Uniqueness is the sectionwise injectivity of
`I ⟶ O'`. -/
@[stacks 08M7 "the canonical map of defining ideals"]
theorem canonicalIdealMap_existsUnique :
    ∃! φ : (D.f'.toModulesHom.pullbackModules).obj D.idealJ.I ⟶ D.idealI.I,
      D.IsCanonicalIdealMap φ :=
  Stacks.SheafOfModules.existsUnique_factorThrough D.idealI.incl D.idealI.injective
    D.pullbackIdealToStructure fun U z ↦
      (D.idealI.kernel U _).1 (D.fSharp_pullbackIdealToStructure_apply U z)

/-- **Stacks 08M7.** The induced map of defining ideals `(f')^*J ⟶ I` of a morphism of
thickenings of ringed topoi. -/
@[stacks 08M7 "the induced map of defining ideals"]
noncomputable def idealMap : (D.f'.toModulesHom.pullbackModules).obj D.idealJ.I ⟶ D.idealI.I :=
  D.canonicalIdealMap_existsUnique.choose

/-- **Stacks 08M7.** The induced map of defining ideals has the normalisation that
characterises it. -/
@[stacks 08M7 "the induced map of defining ideals is the normalised one"]
theorem idealMap_spec : D.IsCanonicalIdealMap D.idealMap :=
  D.canonicalIdealMap_existsUnique.choose_spec.1

/-- Any map of ideals with the normalisation is the induced map. -/
theorem idealMap_unique {φ : (D.f'.toModulesHom.pullbackModules).obj D.idealJ.I ⟶ D.idealI.I}
    (hφ : D.IsCanonicalIdealMap φ) : φ = D.idealMap :=
  D.canonicalIdealMap_existsUnique.choose_spec.2 φ hφ

/-- **Stacks 08M7.** The induced map of defining ideals, read on the target topos: its adjoint
transpose, composed with the inclusion of `I` into `O'`, is the structure map of `f'` applied to
the inclusion of `J` into `O_{B'}`. This is the source's own description of the map. -/
@[stacks 08M7 "the induced map of defining ideals is the structure map of `f'` on `J`"]
theorem homEquiv_idealMap_comp_incl :
    (pullbackAdjPushforwardModules D.f').homEquiv D.idealJ.I
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J)) X'.O))
        (D.idealMap ≫ D.idealI.incl) =
      D.idealJ.incl ≫ unitStructureMap D.f' := by
  rw [D.idealMap_spec, pullbackIdealToStructure,
    RingedToposHom.homEquiv_map_comp_pullbackUnitStructureMap]

/-- The induced map of defining ideals, on sections: a local section of `(f')^*J` is carried to
the section of `I` with the same image in `O'`. -/
theorem incl_idealMap_val_app (U : X'.Cᵒᵖ)
    (z : ((D.f'.toModulesHom.pullbackModules).obj D.idealJ.I).val.obj U) :
    D.idealI.incl.val.app U (D.idealMap.val.app U z) =
      D.pullbackIdealToStructure.val.app U z :=
  val_app_apply_congr D.idealMap_spec U z

/-- **Stacks 08M9.** A morphism of thickenings of ringed topoi is *strict* when its induced map
of defining ideals `(f')^*J ⟶ I` is surjective, i.e. an epimorphism of sheaves of
`O'`-modules. -/
@[stacks 08M9 "strict morphism of thickenings"]
def IsStrict : Prop := Epi D.idealMap

end IdealMap

section PullbackComparison

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w'}}
  {S : RingedTopos.{v'', u'', w''}} {S' : RingedTopos.{v''', u''', w'''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w'})]
  [S.J.HasSheafCompose (forget RingCat.{w''})] [S'.J.HasSheafCompose (forget RingCat.{w'''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{w'''} RingCat.{w'''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w'''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w'}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify S.J AddCommGrpCat.{w''}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (D : MorphismOfThickenings X X' S S')

/-- **Stacks 08M7.** The canonical comparison of the two iterated pullbacks around the square:
pulling back along `f'` and then `i` is pulling back along `t` and then `f`.

Each side is a composite of left adjoints, so it is the mate of the corresponding comparison of
iterated direct images, which is
`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso`; the two are then joined by the
commutativity of the square, the pullback functor depending on the morphism of ringed topoi
only through its value. -/
@[stacks 08M7 "the canonical comparison of the two iterated pullbacks around the square"]
noncomputable def pullbackComparison :
    D.f'.toModulesHom.pullbackModules ⋙ D.i.toModulesHom.pullbackModules ≅
      D.t.toModulesHom.pullbackModules ⋙ D.f.toModulesHom.pullbackModules :=
  Adjunction.leftAdjointCompIso (pullbackAdjPushforwardModules D.f')
      (pullbackAdjPushforwardModules D.i)
      (pullbackAdjPushforwardModules (D.f'.comp D.i))
      (RingedToposHom.pushforwardModulesCompIso D.i D.f').symm ≪≫
    eqToIso (congrArg (fun m ↦ m.toModulesHom.pullbackModules) D.comm) ≪≫
      (Adjunction.leftAdjointCompIso (pullbackAdjPushforwardModules D.t)
        (pullbackAdjPushforwardModules D.f)
        (pullbackAdjPushforwardModules (D.t.comp D.f))
        (RingedToposHom.pushforwardModulesCompIso D.f D.t).symm).symm

end PullbackComparison

end MorphismOfThickenings

end Deformation.ToposThickening

end
