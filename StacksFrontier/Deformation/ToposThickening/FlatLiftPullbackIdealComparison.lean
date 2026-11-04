module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatExtendScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Deformation.ToposThickening.FlatLiftFlatnessEquivalence
public import StacksFrontier.Deformation.ToposThickening.FlatLiftObstruction
public import StacksFrontier.Deformation.ToposThickening.InverseImageIdealStructureMap

/-!
# The two spellings of `f^*𝒥 ⟶ I` in Situation 08M7 agree

Let `(f, f')` be a morphism of first order thickenings of ringed topoi as in Situation 08M7

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_ℬ) --t-->  (Sh(B'), O_{ℬ'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `𝒥 = Ker(t^♯) ⊂ O_{ℬ'}`. The canonical map of
defining ideals `f^*𝒥 ⟶ I` of Situation 08M7 is carried twice in this tree, at two different
spellings of its source:

* as `Deformation.ToposThickening.MorphismOfThickenings.idealMap`, out of the pullback `(f')^*𝒥`
  formed by `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules`, that is, the
  inverse image of Stacks 03D2 followed by extension of scalars along `(f')^♯`;
* as `Deformation.ToposThickening.pullbackBaseIdealMap`, out of
  `Deformation.ToposThickening.pullbackBaseIdeal`, which extends the scalars of the inverse image
  `f⁻¹𝒥` of the ideal *already read over `f⁻¹O_ℬ`*.

The two sources are not the same object — one is the inverse image of a restriction of scalars,
the other the restriction of scalars of an inverse image — and this file identifies them, and the
two maps out of them, so that the results stated in one spelling may be fed from the other.

## Main results

* `Deformation.ToposThickening.inverseImageStructureRingMap_eq_ringMap`: the two spellings of the
  inverse-image form `(f')^♯ : f⁻¹O_{ℬ'} ⟶ O'` of the structure map agree.
* `Deformation.ToposThickening.pullbackIdealIso`: **`(f')^*𝒥 ≅ f^*𝒥`**, the comparison of the two
  spellings of the pullback of the lower defining ideal.
* `Deformation.ToposThickening.pullbackIdealIso_hom_comp_pullbackBaseIdealMap`: **the two
  spellings of the canonical map of defining ideals agree** across that comparison.
* `Deformation.ToposThickening.isStrictPullbackIdealMap_iff_isStrict`: consequently the two
  spellings of strictness, Definition 08M9, agree.

## How the proof goes

Both maps of ideals are pinned down by their composite with the inclusion `I ⟶ O'`, which is a
monomorphism, so everything reduces to an identity of maps into the structure sheaf. Those are
maps out of an extension of scalars along `(f')^♯`, hence determined by their restriction along
the unit of that extension, and there both are the inclusion `𝒥 ⟶ O_{ℬ'}` followed by `(f')^♯`
read on unit modules: for `Deformation.ToposThickening.pullbackBaseIdealToStructure` that is its
definition, and for `Deformation.ToposThickening.MorphismOfThickenings.pullbackIdealToStructure`
it is `MorphismOfThickenings.inverseImageIdealUnit_comp_pullbackIdealToStructure` (in the same
namespace).

## Implementation notes

The extension of scalars along `(f')^♯` carries **two** adjunctions in this tree, and they are
different terms: `Stacks.FlatChangeOfRings.extendScalarsAdjunction`, which
`Deformation.ToposThickening.pullbackBaseIdealToStructure` is defined by, obtains the
presheaf-level adjunction from a `Nonempty`, whereas
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`, which
`Deformation.ToposThickening.MorphismOfThickenings.pullbackIdealToStructure` is read through,
uses the explicit one. Nothing identifies their units, and for a fixed adjoint pair nothing can:
the unit is determined only up to an automorphism of the left adjoint. So the comparison
isomorphism is *not* the extension of scalars of the comparison of the two readings of `f⁻¹𝒥`; it
is the transpose, along one adjunction, of that comparison followed by the unit of the other.
`doubleAdjunctionIso` builds it and shows it is invertible, each triangle being cancelled with the
adjunction whose unit wrote the map in question — which is why two adjunctions suffice and no
comparison between their units is needed.

The crossing between the two spellings `Stacks.Sheaves.RingedToposModules.fSharpCommRingSheaf` and
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage` of the structure map happens once, in
`Deformation.ToposThickening.pullbackIdealIso`, as an `eqToHom`; the crux is stated with that
morphism of sheaves of commutative rings generalised, so that the crossing is discharged by
`subst` rather than by rewriting under a functor.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (ringMap)
open Stacks.SheafOfModules.ChangeOfRings (unitToRestrictScalarsUnit)
open Stacks.Sheaves.ToposPullback (pullbackModuleUnitIso)
open Stacks.Sheaves.RingedToposModules (inverseImageModules
  fSharpCommRingSheaf inverseImageStructureCommRingSheaf pullbackModuleObjRestrictScalarsIso)

universe v u v' u' w vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

/-! ### Two adjunctions sharing a pair of functors -/

section TwoAdjunctions

variable {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂] {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁}

/-- **An isomorphism `L A ≅ L A'` out of an isomorphism `A ≅ A'`, written across two
adjunctions.**

For a single adjunction this would be `L.map ψ.hom`. The point of the construction is that the
two adjunctions are allowed to be different terms: the map is the transpose along `Adj₂` of `ψ`
followed by the unit of `Adj₁`, and its inverse is the transpose along `Adj₁` of `ψ⁻¹` followed by
the unit of `Adj₂`. Each triangle is then cancelled with the adjunction that wrote the map being
cancelled, so no identification of the two units is used — and for a fixed adjoint pair none is
available, the unit being determined only up to an automorphism of `L`. -/
noncomputable def doubleAdjunctionIso (Adj₁ Adj₂ : L ⊣ R) {A A' : C₁} (ψ : A ≅ A') :
    L.obj A ≅ L.obj A' where
  hom := (Adj₂.homEquiv A (L.obj A')).symm (ψ.hom ≫ Adj₁.unit.app A')
  inv := (Adj₁.homEquiv A' (L.obj A)).symm (ψ.inv ≫ Adj₂.unit.app A)
  hom_inv_id := by
    refine (Adj₂.homEquiv A (L.obj A)).injective ?_
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc,
      ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply, Iso.hom_inv_id_assoc,
      Adjunction.homEquiv_id]
  inv_hom_id := by
    refine (Adj₁.homEquiv A' (L.obj A')).injective ?_
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc,
      ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply, Iso.inv_hom_id_assoc,
      Adjunction.homEquiv_id]

/-- The restriction along the unit of `Adj₂` of a transpose along `Adj₁` precomposed with
`doubleAdjunctionIso`: the isomorphism contributes exactly `ψ`. -/
private theorem unit_comp_doubleAdjunctionIso_hom_comp (Adj₁ Adj₂ : L ⊣ R) {A A' : C₁}
    (ψ : A ≅ A') {M : C₂} (w : A' ⟶ R.obj M) :
    Adj₂.unit.app A ≫ R.map ((doubleAdjunctionIso Adj₁ Adj₂ ψ).hom ≫
        (Adj₁.homEquiv A' M).symm w) = ψ.hom ≫ w := by
  rw [Functor.map_comp, ← Category.assoc,
    show Adj₂.unit.app A ≫ R.map (doubleAdjunctionIso Adj₁ Adj₂ ψ).hom = ψ.hom ≫ Adj₁.unit.app A'
      from (Adjunction.homEquiv_unit Adj₂ A _ _).symm.trans (Equiv.apply_symm_apply _ _),
    Category.assoc, ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

/-- Two morphisms out of `L A` whose restrictions along the unit agree are equal. -/
private theorem hom_ext_unit (Adj : L ⊣ R) {A : C₁} {M : C₂} {α β : L.obj A ⟶ M}
    (h : Adj.unit.app A ≫ R.map α = Adj.unit.app A ≫ R.map β) : α = β :=
  (Adj.homEquiv A M).injective ((Adjunction.homEquiv_unit Adj A M α).trans
    (h.trans (Adjunction.homEquiv_unit Adj A M β).symm))

end TwoAdjunctions

/-! ### The square of Situation 08M7 -/

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
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)

/-! ### The structure map in its two spellings -/

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The two spellings of `(f')^♯ : f⁻¹O_{ℬ'} ⟶ O'` agree.** A morphism of thickenings extends
scalars along the comm-ring form of the structure map read as a morphism of sheaves of rings;
`Stacks.SheafOfModules.FlatSquareZero.ringMap` of the inverse-image form of the structure map of
`f'` is the same morphism. The identity is not definitional: the two forms of the structure map
are adjunct to the same morphism of sheaves of sets, for the adjunction on sheaves of rings and
for the one on sheaves of commutative rings respectively, and that is the content of
`AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage`. -/
theorem inverseImageStructureRingMap_eq_ringMap :
    (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).inverseImageStructureRingMap
      = Stacks.SheafOfModules.FlatSquareZero.ringMap f'.fSharpInverseImage :=
  (AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage f').symm

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The commutative-ring forms of the structure map agree: the morphism of sheaves of commutative
rings the pullback of sheaves of modules extends scalars along is the inverse-image form of the
structure map of `f'`. Forgetting commutativity is faithful, so this is
`Deformation.ToposThickening.inverseImageStructureRingMap_eq_ringMap` read backwards. -/
theorem fSharpCommRingSheaf_toModulesHom_eq :
    fSharpCommRingSheaf f'.toModulesHom = f'.fSharpInverseImage :=
  (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map_injective
    (AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage f').symm

/-! ### The two readings of `f⁻¹𝒥` -/

/-- **The two readings of `f⁻¹𝒥` compared.** On the left the inverse image along `f'` of `𝒥` read
over `O_{ℬ'}`, with its scalars then restricted to `f⁻¹O_ℬ`; on the right the inverse image of
`𝒥` already read over `t_*O_ℬ`. The comparison is the identity on underlying sheaves of sets, and
it is the one the inclusion `f⁻¹𝒥 ⟶ f⁻¹O_{ℬ'}` of
`Deformation.ToposThickening.inverseImageBaseIdealIncl` is built from. -/
noncomputable def inverseImageIdealIso :
    (SheafOfModules.restrictScalars (ringMap (inverseImageBaseReduction t f'))).obj
        (inverseImageBaseIdeal t f' ht) ≅
      (inverseImageModules f'.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj ht.idealOfThickening.I :=
  eqToIso (congrArg (fun m ↦ (SheafOfModules.restrictScalars m).obj
      (inverseImageBaseIdeal t f' ht)) (ringMap_inverseImageBaseReduction t f')) ≪≫
    pullbackModuleObjRestrictScalarsIso X'.J f'.toToposHom.inverseImage
      ((Stacks.forgetCommRingSheaf S'.J).map t.fSharp) ht.I

omit [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inclusion `f⁻¹𝒥 ⟶ f⁻¹O_{ℬ'}` is the comparison of the two readings of `f⁻¹𝒥` followed by
the inverse image of the inclusion `𝒥 ⟶ O_{ℬ'}` read on unit modules. This is its definition, up
to the bracketing. -/
private theorem inverseImageIdealIso_hom_comp :
    (inverseImageIdealIso t f' ht).hom ≫
        ((inverseImageModules f'.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map ht.incl ≫
          (pullbackModuleUnitIso X'.J f'.toToposHom.inverseImage
              (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv) =
      inverseImageBaseIdealIncl t f' ht :=
  Category.assoc _ _ _

omit [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison of the two readings of `f⁻¹𝒥`, taken from the reading over `t_*O_ℬ` and
followed by the inclusion into `f⁻¹O_{ℬ'}`, is the inverse image of the inclusion of `𝒥`. -/
private theorem inverseImageIdealIso_symm_hom_comp_incl :
    (inverseImageIdealIso t f' ht).symm.hom ≫ inverseImageBaseIdealIncl t f' ht =
      (inverseImageModules f'.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map ht.incl ≫
        (pullbackModuleUnitIso X'.J f'.toToposHom.inverseImage
            (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv :=
  (Iso.inv_comp_eq _).2 (inverseImageIdealIso_hom_comp t f' ht).symm

omit [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `inverseImageIdealIso_symm_hom_comp_incl` with a further morphism out of `f⁻¹O_{ℬ'}`
appended, which is the bracketing the crux meets it at. -/
private theorem inverseImageIdealIso_symm_hom_comp_incl_comp
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f'))}
    (u : SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')) ⟶ M) :
    (inverseImageIdealIso t f' ht).symm.hom ≫ inverseImageBaseIdealIncl t f' ht ≫ u =
      (inverseImageModules f'.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map ht.incl ≫
        (pullbackModuleUnitIso X'.J f'.toToposHom.inverseImage
            (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv ≫ u :=
  (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ u) (inverseImageIdealIso_symm_hom_comp_incl t f' ht)).trans
      (Category.assoc _ _ _)

/-! ### The crux -/

/-- `f⁻¹𝒥` in the reading the pullback of sheaves of modules produces, retyped at the comm-ring
spelling of `f⁻¹O_{ℬ'}`. -/
noncomputable abbrev upperIdeal : SheafOfModules.{w}
    (Stacks.commRingSheafToRingSheaf (inverseImageStructureCommRingSheaf f'.toModulesHom)) :=
  (inverseImageModules f'.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj ht.idealOfThickening.I

/-- The adjunction of Stacks 03CZ for a morphism of sheaves of commutative rings out of
`f⁻¹O_{ℬ'}`, in the spelling with the explicit presheaf-level unit. At the structure map this is
`Deformation.ToposThickening.MorphismOfThickenings.extendScalarsAdj`. -/
noncomputable def modulesAdj
    (c : inverseImageStructureCommRingSheaf f'.toModulesHom ⟶ X'.O) :
    Stacks.FlatChangeOfRings.extendScalars c ⊣
      SheafOfModules.restrictScalars (Stacks.FlatChangeOfRings.ringSheafMap c) :=
  Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction X'.J c.hom
    (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf f'.toModulesHom.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).property

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
/-- **The two maps `f^*𝒥 ⟶ O'` agree**, with the morphism of sheaves of commutative rings along
which scalars are extended left general, so that the crossing between its two spellings is a
`subst`.

Both sides are morphisms out of an extension of scalars, so it suffices to compare their
restrictions along the unit of `modulesAdj`. On the left that restriction is the comparison of the
two readings of `f⁻¹𝒥` followed by the inclusion `f⁻¹𝒥 ⟶ f⁻¹O_{ℬ'}`, by
`unit_comp_doubleAdjunctionIso_hom_comp`; on the right it is
`MorphismOfThickenings.inverseImageIdealUnit_comp_pullbackIdealToStructure`.
The two agree by `inverseImageIdealIso_symm_hom_comp_incl`. -/
private theorem crux (c : inverseImageStructureCommRingSheaf f'.toModulesHom ⟶ X'.O)
    (hc : fSharpCommRingSheaf f'.toModulesHom = c) :
    eqToHom (congrArg (fun φ : inverseImageStructureCommRingSheaf f'.toModulesHom ⟶ X'.O ↦
          (Stacks.FlatChangeOfRings.extendScalars φ).obj (upperIdeal t f' ht)) hc) ≫
        (doubleAdjunctionIso (Stacks.FlatChangeOfRings.extendScalarsAdjunction c)
              (modulesAdj f' c) (inverseImageIdealIso t f' ht).symm).hom ≫
          ((Stacks.FlatChangeOfRings.extendScalarsAdjunction c).homEquiv _ _).symm
            (inverseImageBaseIdealIncl t f' ht ≫ unitToRestrictScalarsUnit (ringMap c)) =
      (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).pullbackIdealToStructure
        := by
  subst hc
  refine (Category.id_comp _).trans ?_
  refine hom_ext_unit (modulesAdj f' (fSharpCommRingSheaf f'.toModulesHom)) ?_
  refine (unit_comp_doubleAdjunctionIso_hom_comp _ _ _ _).trans ?_
  refine Eq.trans ?_ (MorphismOfThickenings.inverseImageIdealUnit_comp_pullbackIdealToStructure
    (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm)).symm
  exact inverseImageIdealIso_symm_hom_comp_incl_comp t f' ht _

/-! ### The two spellings of `f^*𝒥` -/

/-- **`(f')^*𝒥 ≅ f^*𝒥`**: the pullback of the lower defining ideal in the spelling of
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` — the inverse image of `𝒥` read
over `t_*O_ℬ`,
with scalars then extended — is isomorphic to `Deformation.ToposThickening.pullbackBaseIdeal`,
which extends the scalars of `f⁻¹𝒥` read over `f⁻¹O_ℬ`.

The inner modules are compared by `Deformation.ToposThickening.inverseImageIdealIso`, the identity
on underlying sheaves of sets. The outer extensions of scalars are the same functor, but the two
adjunctions presenting it are different terms with no comparison of their units available, so the
isomorphism is not the extension of scalars of the inner one: it is `doubleAdjunctionIso`, the
transpose along one adjunction of the inner comparison followed by the unit of the other. -/
noncomputable def pullbackIdealIso :
    f'.toModulesHom.pullbackModules.obj ht.idealOfThickening.I ≅ pullbackBaseIdeal t f' ht :=
  eqToIso (congrArg (fun φ : inverseImageStructureCommRingSheaf f'.toModulesHom ⟶ X'.O ↦
      (Stacks.FlatChangeOfRings.extendScalars φ).obj (upperIdeal t f' ht))
    (fSharpCommRingSheaf_toModulesHom_eq f')) ≪≫
    doubleAdjunctionIso (Stacks.FlatChangeOfRings.extendScalarsAdjunction f'.fSharpInverseImage)
      (modulesAdj f' f'.fSharpInverseImage) (inverseImageIdealIso t f' ht).symm

omit [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
/-- `Deformation.ToposThickening.pullbackIdealIso` is, on the nose, the crossing between the two
spellings of the structure map followed by the comparison of the two adjunctions. Naming the
factorisation keeps the consumer from having to unfold the isomorphism under a metavariable. -/
theorem pullbackIdealIso_hom :
    (pullbackIdealIso t f' ht).hom =
      eqToHom (congrArg (fun φ : inverseImageStructureCommRingSheaf f'.toModulesHom ⟶ X'.O ↦
          (Stacks.FlatChangeOfRings.extendScalars φ).obj (upperIdeal t f' ht))
        (fSharpCommRingSheaf_toModulesHom_eq f')) ≫
        (doubleAdjunctionIso
            (Stacks.FlatChangeOfRings.extendScalarsAdjunction f'.fSharpInverseImage)
            (modulesAdj f' f'.fSharpInverseImage) (inverseImageIdealIso t f' ht).symm).hom :=
  rfl

/-- **The two spellings of the canonical map of defining ideals `f^*𝒥 ⟶ I` of Situation 08M7
agree.** Composed with the comparison of the two spellings of its source,
`Deformation.ToposThickening.pullbackBaseIdealMap` is
`Deformation.ToposThickening.MorphismOfThickenings.idealMap`.

Both maps are characterised by their composite with the inclusion `I ⟶ O'`, which is a
monomorphism, so this is the identity the crux proves. -/
theorem pullbackIdealIso_hom_comp_pullbackBaseIdealMap :
    (pullbackIdealIso t f' ht).hom ≫ pullbackBaseIdealMap i t f f' hi ht comm =
      (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap :=
  MorphismOfThickenings.idealMap_unique
      (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm) <|
    (Category.assoc (pullbackIdealIso t f' ht).hom
          (pullbackBaseIdealMap i t f f' hi ht comm) hi.incl).trans <|
      (congrArg (fun m ↦ (pullbackIdealIso t f' ht).hom ≫ m)
          (pullbackBaseIdealMap_comp_incl i t f f' hi ht comm)).trans <|
        (congrArg (fun m ↦ m ≫ pullbackBaseIdealToStructure t f' ht)
            (pullbackIdealIso_hom t f' ht)).trans <|
          (Category.assoc _ _ _).trans
            (crux i t f f' hi ht comm f'.fSharpInverseImage
              (fSharpCommRingSheaf_toModulesHom_eq f'))

/-- **The two spellings of strictness, Definition 08M9, agree**: the canonical map of defining
ideals `f^*𝒥 ⟶ I` is an epimorphism if and only if the induced map `(f')^*𝒥 ⟶ I` of the morphism
of thickenings is. The two differ by the isomorphism
`Deformation.ToposThickening.pullbackIdealIso`. -/
theorem isStrictPullbackIdealMap_iff_isStrict :
    IsStrictPullbackIdealMap i t f f' hi ht comm ↔
      (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict := by
  have hfac : (pullbackIdealIso t f' ht).inv ≫
      (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap =
        pullbackBaseIdealMap i t f f' hi ht comm := by
    rw [← pullbackIdealIso_hom_comp_pullbackBaseIdealMap i t f f' hi ht comm]
    exact (pullbackIdealIso t f' ht).inv_hom_id_assoc _
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : Epi ((pullbackIdealIso t f' ht).inv ≫
        (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap) := by
      rwa [hfac]
    exact epi_of_epi (pullbackIdealIso t f' ht).inv _
  · have : Epi ((pullbackIdealIso t f' ht).hom ≫ pullbackBaseIdealMap i t f f' hi ht comm) := by
      rwa [pullbackIdealIso_hom_comp_pullbackBaseIdealMap i t f f' hi ht comm]
    exact epi_of_epi (pullbackIdealIso t f' ht).hom _

end Deformation.ToposThickening

end
