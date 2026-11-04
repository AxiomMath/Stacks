module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftFlatnessEquivalence
public import StacksFrontier.Deformation.ToposThickening.FlatLiftObstruction
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.UliftTransport

/-!
# The two base rings of a flat lift agree

Let `(f, f')` be a morphism of first order thickenings of ringed topoi as in Situation 08M7

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(ℬ), O_ℬ) --t-->  (Sh(ℬ'), O_{ℬ'})
```

and let `ℱ` be an `O`-module, presented on the thickened topos as a module over the direct image
`i_*O`. Flatness of `ℱ` over `O_ℬ` is read in this tree in two different ways:

* `Deformation.ToposThickening.IsFlatOverBase` restricts `ℱ` along
  `i_*(f⁻¹O_ℬ) ⟶ i_*O`, the direct image of the inverse-image form of the structure map of `f`;
* `Deformation.ToposThickening.reducedBaseModule` restricts `ℱ` along
  `Deformation.ToposThickening.inverseImageReducedStructureMap`, a map
  `f'⁻¹(t_*O_ℬ) ⟶ i_*O`, which is the presentation of `f⁻¹O_ℬ` that Situation 08M7's
  identification of `f⁻¹` with `(f')⁻¹` produces.

The two restrict the same module along two different maps into `i_*O`. The two sources are
isomorphic, compatibly with the two maps, so the first reading of flatness implies the second.

## Main definitions

* `Deformation.ToposThickening.reducedBaseRingIso`: the comparison
  `f'⁻¹(t_*O_ℬ) ≅ i_*(f⁻¹O_ℬ)` of the two presentations of `f⁻¹O_ℬ`.
* `Deformation.ToposThickening.reducedBaseRingComparisonIso`: its adjoint form, an isomorphism
  `i⁻¹f'⁻¹(t_*O_ℬ) ≅ f⁻¹O_ℬ` on the original topos.

## Main results

* `Deformation.ToposThickening.reducedBaseRingIso_hom_comp`: the comparison is compatible with
  the two structure maps: followed by `i_*(f⁻¹O_ℬ) ⟶ i_*O` it is
  `inverseImageReducedStructureMap`.
* `Deformation.ToposThickening.isFlat_restrictScalars_of_iso`: restriction of scalars along an
  isomorphism of sheaves of commutative rings preserves flatness.
* `Deformation.ToposThickening.isFlat_reducedBaseModule_of_isFlatOverBase`: `ℱ` flat over
  `O_ℬ` in the sense of `IsFlatOverBase` is flat over `O_ℬ` in the sense of
  `reducedBaseModule`.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (ringMap)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor inverseImageCommRingFunctor
  commRingImageAdjunction pushforwardCommRingCompIso pushforwardCommRingCompIso_hom_forget
  commRingImageAdjunction_counit_forget forget_map_commRingImageAdjunction_unit_app
  pushforwardCommRingFunctor_isEquivalence)

universe v u v' u' w vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

/-! ## The comparison of iterated inverse images, at independent section universes -/

section CompIso

universe wA wB wD vA uA vB uB vD uD

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {D : Type uD} [Category.{vD} D]
  {JA : GrothendieckTopology A} {JB : GrothendieckTopology B} {JD : GrothendieckTopology D}
  [JA.HasSheafCompose (forget RingCat.{wA})] [JB.HasSheafCompose (forget RingCat.{wB})]
  [JD.HasSheafCompose (forget RingCat.{wD})]
  [JA.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
  [JB.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [JD.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  (g : MorphismOfTopoi (Sheaf JB (Type wB)) (Sheaf JD (Type wD)))
  (h : MorphismOfTopoi (Sheaf JA (Type wA)) (Sheaf JB (Type wB)))

/-- The comparison `h⁻¹g⁻¹M ≅ (g ∘ h)⁻¹M` of the iterated inverse image of a sheaf of
commutative rings with the inverse image along the composite, for two morphisms of topoi whose
three sheaf categories take their sheaves of commutative rings in three independent universes. -/
noncomputable def inverseImageCompIso (M : Sheaf JD CommRingCat.{wD}) :
    (inverseImageCommRingFunctor h).obj ((inverseImageCommRingFunctor g).obj M) ≅
      (inverseImageCommRingFunctor (g.comp h)).obj M :=
  Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCompIso JA JB h.inverseImage g.inverseImage M

/-- The comparison of iterated inverse images is the identity on underlying sheaves of sets. -/
theorem forget_map_inverseImageCompIso_hom (M : Sheaf JD CommRingCat.{wD}) :
    (sheafCompose JA (forget CommRingCat.{wA})).map (inverseImageCompIso g h M).hom =
      𝟙 (h.inverseImage.obj (g.inverseImage.obj
        ((sheafCompose JD (forget CommRingCat.{wD})).obj M))) :=
  Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCompIso_hom_forget JA JB
    h.inverseImage g.inverseImage M

/-- If `F.map e.hom = z` and `z ≫ r = 𝟙 _`, then `F.map e.inv = r`. -/
private theorem map_inv_eq_of_map_hom_eq {C₀ : Type uA} [Category.{vA} C₀] {D₀ : Type uB}
    [Category.{vB} D₀] {F : C₀ ⥤ D₀} {A B : C₀} (e : A ≅ B) {z : F.obj A ⟶ F.obj B}
    (hz : F.map e.hom = z) {r : F.obj B ⟶ F.obj A} (hr : z ≫ r = 𝟙 _) : F.map e.inv = r :=
  ((F.mapIso e).inv_ext' (by simpa [hz] using hr)).symm

/-- The inverse of the comparison of iterated inverse images is also the identity on underlying
sheaves of sets. -/
theorem forget_map_inverseImageCompIso_inv (M : Sheaf JD CommRingCat.{wD}) :
    (sheafCompose JA (forget CommRingCat.{wA})).map (inverseImageCompIso g h M).inv =
      𝟙 (h.inverseImage.obj (g.inverseImage.obj
        ((sheafCompose JD (forget CommRingCat.{wD})).obj M))) :=
  map_inv_eq_of_map_hom_eq _ (forget_map_inverseImageCompIso_hom g h M) (Category.id_comp _)

/-- The inverse of the comparison of iterated direct images is the identity on underlying sheaves
of sets. -/
theorem forget_map_pushforwardCompIso_inv (M : Sheaf JA CommRingCat.{wA}) :
    (sheafCompose JD (forget CommRingCat.{wD})).map (pushforwardCommRingCompIso h g M).inv =
      𝟙 (g.pushforward.obj (h.pushforward.obj
        ((sheafCompose JA (forget CommRingCat.{wA})).obj M))) :=
  map_inv_eq_of_map_hom_eq _ (pushforwardCommRingCompIso_hom_forget h g M) (Category.id_comp _)

end CompIso

/-! ## Forgetting the ring operations -/

section Forget

universe w1 w2 v1 u1 v2 u2

variable {C₁ : Type u1} [Category.{v1} C₁] {C₂ : Type u2} [Category.{v2} C₂]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
  [J₁.HasSheafCompose (forget RingCat.{w1})] [J₂.HasSheafCompose (forget RingCat.{w2})]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{w1} RingCat.{w1})]
  [J₂.HasSheafCompose (forget₂ CommRingCat.{w2} RingCat.{w2})]
  (a : MorphismOfTopoi (Sheaf J₁ (Type w1)) (Sheaf J₂ (Type w2)))

/-- The inverse image of a morphism of sheaves of commutative rings, after forgetting the ring
operations, is the inverse image of the underlying morphism of sheaves of sets. -/
theorem forget_map_inverseImage_map {M N : Sheaf J₂ CommRingCat.{w2}} (x : M ⟶ N) :
    (sheafCompose J₁ (forget CommRingCat.{w1})).map ((inverseImageCommRingFunctor a).map x) =
      a.inverseImage.map ((sheafCompose J₂ (forget CommRingCat.{w2})).map x) :=
  Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap J₁
    (Φ := a.inverseImage) x

/-- The direct image of a morphism of sheaves of commutative rings, after forgetting the ring
operations, is the direct image of the underlying morphism of sheaves of sets. -/
theorem forget_map_pushforward_map {M N : Sheaf J₁ CommRingCat.{w1}} (x : M ⟶ N) :
    (sheafCompose J₂ (forget CommRingCat.{w2})).map ((pushforwardCommRingFunctor a).map x) =
      a.pushforward.map ((sheafCompose J₁ (forget CommRingCat.{w1})).map x) :=
  Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap J₂
    (Φ := a.pushforward) x

/-- Forgetting the ring operations carries the inverse hom-set bijection of the adjunction of
Stacks 00YV on sheaves of commutative rings to the inverse hom-set bijection of `a⁻¹ ⊣ a_*` on
sheaves of sets. -/
theorem forget_map_homEquiv_symm (M : Sheaf J₂ CommRingCat.{w2})
    (N : Sheaf J₁ CommRingCat.{w1}) (x : M ⟶ (pushforwardCommRingFunctor a).obj N) :
    (sheafCompose J₁ (forget CommRingCat.{w1})).map
        (((commRingImageAdjunction a).homEquiv M N).symm x) =
      (a.adj.homEquiv ((sheafCompose J₂ (forget CommRingCat.{w2})).obj M)
          ((sheafCompose J₁ (forget CommRingCat.{w1})).obj N)).symm
        ((sheafCompose J₂ (forget CommRingCat.{w2})).map x) := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, forget_map_inverseImage_map,
    commRingImageAdjunction_counit_forget]
  exact (Adjunction.homEquiv_counit a.adj _ _ _).symm

/-- If `F.map x = z` and `z ≫ F.map y = r`, then `F.map (x ≫ y) = r`. -/
theorem map_comp_cancel {C₀ : Type u1} [Category.{v1} C₀] {D₀ : Type u2}
    [Category.{v2} D₀] {F : C₀ ⥤ D₀} {A B E : C₀} {x : A ⟶ B} (y : B ⟶ E)
    {z : F.obj A ⟶ F.obj B} (hx : F.map x = z) {r : F.obj A ⟶ F.obj E}
    (hz : z ≫ F.map y = r) : F.map (x ≫ y) = r :=
  (F.map_comp x y).trans ((congrArg (fun m ↦ m ≫ F.map y) hx).trans hz)

end Forget

/-! ## Two identities about composites of adjunctions -/

section Adjunctions

universe vA' uA' vB' uB' vD' uD'

/-- For `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` and `φ : M ⟶ R₂.obj N`, transposing `R₁.map φ`
along the composite adjunction splits as the counit of `adj₁` at `M` followed by the transpose of
`φ` along `adj₂`. -/
theorem comp_counit_map_pushforward {CA : Type uA'} [Category.{vA'} CA] {CB : Type uB'}
    [Category.{vB'} CB] {CD : Type uD'} [Category.{vD'} CD] {L₁ : CA ⥤ CB} {R₁ : CB ⥤ CA}
    {L₂ : CB ⥤ CD} {R₂ : CD ⥤ CB} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {M : CB} {N : CD}
    (φ : M ⟶ R₂.obj N) :
    (L₁ ⋙ L₂).map (R₁.map φ) ≫ (adj₁.comp adj₂).counit.app N =
      L₂.map (adj₁.counit.app M) ≫ L₂.map φ ≫ adj₂.counit.app N := by
  rw [Adjunction.comp_counit_app, Functor.comp_map, ← Category.assoc, ← L₂.map_comp,
    show L₁.map (R₁.map φ) = (R₁ ⋙ L₁).map φ from rfl, adj₁.counit.naturality φ,
    L₂.map_comp, Category.assoc]
  rfl

end Adjunctions

/-! ## The compatibility, on underlying sheaves of sets -/

section SetLevel

universe va' ua' vb' ub' vc' uc' vd' ud'

variable {TX : Type ua'} [Category.{va'} TX] {TX' : Type ub'} [Category.{vb'} TX']
  {TS : Type uc'} [Category.{vc'} TS] {TS' : Type ud'} [Category.{vd'} TS']
  (ii : MorphismOfTopoi TX TX') (tt : MorphismOfTopoi TS TS')
  (ff : MorphismOfTopoi TX TS) (ff' : MorphismOfTopoi TX' TS')

/-- Transport of a transpose along an equality `ff' ∘ ii = m` of morphisms of topoi. -/
theorem eqToHom_comp_counit (RX : TX) (m : MorphismOfTopoi TX TS')
    (hm : ff'.comp ii = m) (M : TS') (a : M ⟶ m.pushforward.obj RX) :
    (ff'.comp ii).inverseImage.map (a ≫ eqToHom (congrArg
          (fun n : MorphismOfTopoi TX TS' ↦ n.pushforward.obj RX) hm.symm)) ≫
        (ff'.comp ii).adj.counit.app RX =
      eqToHom (congrArg (fun n : MorphismOfTopoi TX TS' ↦ n.inverseImage.obj M) hm) ≫
        m.inverseImage.map a ≫ m.adj.counit.app RX := by
  subst hm
  exact (congrArg (fun z ↦ (ff'.comp ii).inverseImage.map z ≫
      (ff'.comp ii).adj.counit.app RX) (Category.comp_id a)).trans
    (Category.id_comp _).symm

/-- The compatibility of the comparison with the two structure maps, on underlying sheaves of
sets: for a commuting square `ff' ∘ ii = tt ∘ ff` of morphisms of topoi and a morphism
`φ : RS ⟶ ff_*RX`, the composite of the unit of `ii⁻¹ ⊣ ii_*` with the direct image of

`ii⁻¹ff'⁻¹tt_*RS = ff⁻¹tt⁻¹tt_*RS ⟶ ff⁻¹RS ⟶ RX`,

whose second step is the transpose of `φ`, is the transpose along `ff'⁻¹ ⊣ ff'_*` of the direct
image of `φ` read through the square. -/
theorem unit_comp_pushforward_eq (hc : ff'.comp ii = tt.comp ff) (RS : TS) (RX : TX)
    (φ : RS ⟶ ff.pushforward.obj RX) :
    ii.adj.unit.app (ff'.inverseImage.obj (tt.pushforward.obj RS)) ≫
        ii.pushforward.map (eqToHom (congrArg (fun n : MorphismOfTopoi TX TS' ↦
            n.inverseImage.obj (tt.pushforward.obj RS)) hc) ≫
          ff.inverseImage.map (tt.adj.counit.app RS) ≫
            ff.inverseImage.map φ ≫ ff.adj.counit.app RX) =
      ff'.inverseImage.map (tt.pushforward.map φ ≫ eqToHom (congrArg
          (fun n : MorphismOfTopoi TX TS' ↦ n.pushforward.obj RX) hc.symm)) ≫
        ff'.adj.counit.app (ii.pushforward.obj RX) :=
  have hrho : (ii.adj.homEquiv (ff'.inverseImage.obj (tt.pushforward.obj RS)) RX).symm
      (ff'.inverseImage.map (tt.pushforward.map φ ≫ eqToHom (congrArg
          (fun n : MorphismOfTopoi TX TS' ↦ n.pushforward.obj RX) hc.symm)) ≫
        ff'.adj.counit.app (ii.pushforward.obj RX)) =
      eqToHom (congrArg (fun n : MorphismOfTopoi TX TS' ↦
          n.inverseImage.obj (tt.pushforward.obj RS)) hc) ≫
        ff.inverseImage.map (tt.adj.counit.app RS) ≫
          ff.inverseImage.map φ ≫ ff.adj.counit.app RX :=
    (Adjunction.homEquiv_counit ii.adj _ _ _).trans
      (((congrArg (fun z ↦ z ≫ ii.adj.counit.app RX)
            (ii.inverseImage.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        ((congrArg (fun z ↦ ii.inverseImage.map (ff'.inverseImage.map
                (tt.pushforward.map φ ≫ eqToHom (congrArg
                  (fun n : MorphismOfTopoi TX TS' ↦ n.pushforward.obj RX) hc.symm))) ≫ z)
            (Adjunction.comp_counit_app ff'.adj ii.adj RX).symm).trans
          ((eqToHom_comp_counit ii ff' RX (tt.comp ff) hc (tt.pushforward.obj RS)
              (tt.pushforward.map φ)).trans
            (congrArg (fun z ↦ eqToHom (congrArg
                (fun n : MorphismOfTopoi TX TS' ↦
                  n.inverseImage.obj (tt.pushforward.obj RS)) hc) ≫ z)
              (comp_counit_map_pushforward tt.adj ff.adj φ)))))
  ((Adjunction.homEquiv_unit ii.adj _ _ _).symm.trans
      (congrArg (fun z ↦ ii.adj.homEquiv
        (ff'.inverseImage.obj (tt.pushforward.obj RS)) RX z) hrho.symm)).trans
    (Equiv.apply_symm_apply _ _)

end SetLevel

/-! ## Flatness under restriction of scalars along an isomorphism -/

section FlatTransport

universe wF vF uF

variable {CF : Type uF} [Category.{vF} CF] {JF : GrothendieckTopology CF}
  [JF.HasSheafCompose (forget₂ CommRingCat.{wF} RingCat.{wF})]
  [HasWeakSheafify JF AddCommGrpCat.{wF}] [JF.WEqualsLocallyBijective AddCommGrpCat.{wF}]
  {O₁ O₂ : Sheaf JF CommRingCat.{wF}}

/-- Restriction of scalars along the inverse of an isomorphism `e` of sheaves of commutative
rings is isomorphic to extension of scalars along `e.hom`. -/
noncomputable def restrictScalarsIsoExtendScalars (e : O₁ ≅ O₂) :
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
        ((Stacks.forgetCommRingSheaf JF).mapIso e)).functor ≅
      Stacks.FlatChangeOfRings.extendScalars e.hom :=
  Adjunction.leftAdjointUniq
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      ((Stacks.forgetCommRingSheaf JF).mapIso e)).toAdjunction
    (Stacks.FlatChangeOfRings.extendScalarsAdjunction e.hom)

/-- Flatness of a sheaf of modules is invariant under restriction of scalars along an
isomorphism of the structure sheaf. -/
theorem isFlat_restrictScalars_of_iso (e : O₁ ≅ O₂)
    (M : SheafOfModules.{wF} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat M) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars (ringMap e.hom)).obj M) :=
  AlgebraicGeometry.SheafOfModules.isFlat_of_iso
    ((restrictScalarsIsoExtendScalars e.symm).app M).symm
    (Stacks.FlatChangeOfRings.isFlat_extendScalars e.inv M hM)

end FlatTransport

/-! ## The comparison of the two base rings -/

section Comparison

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (comm : f'.comp i = t.comp f)

/-- The comparison `i⁻¹f'⁻¹(t_*O_ℬ) ≅ f⁻¹O_ℬ` on the original topos: the inverse image along
`i` of the presentation of `f⁻¹O_ℬ` on the thickened topos is `f⁻¹O_ℬ` itself. -/
noncomputable def reducedBaseRingComparisonIso (ht : FirstOrderThickening t) :
    (inverseImageCommRingFunctor i.toToposHom).obj (inverseImageReducedBaseRing t f') ≅
      (inverseImageCommRingFunctor f.toToposHom).obj S.O :=
  haveI : (pushforwardCommRingFunctor t.toToposHom).IsEquivalence :=
    pushforwardCommRingFunctor_isEquivalence t.toToposHom ht.equiv
  inverseImageCompIso f'.toToposHom i.toToposHom
      ((pushforwardCommRingFunctor t.toToposHom).obj S.O) ≪≫
    eqToIso (congrArg (fun m : RingedToposHom X S' ↦
      (inverseImageCommRingFunctor m.toToposHom).obj
        ((pushforwardCommRingFunctor t.toToposHom).obj S.O)) comm) ≪≫
    (inverseImageCompIso t.toToposHom f.toToposHom
      ((pushforwardCommRingFunctor t.toToposHom).obj S.O)).symm ≪≫
    (inverseImageCommRingFunctor f.toToposHom).mapIso
      (asIso ((commRingImageAdjunction t.toToposHom).counit.app S.O))

/-- The comparison `f'⁻¹(t_*O_ℬ) ≅ i_*(f⁻¹O_ℬ)` of the two presentations of `f⁻¹O_ℬ` on the
thickened topos: the unit of `i⁻¹ ⊣ i_*` followed by the direct image along `i` of
`reducedBaseRingComparisonIso`. -/
noncomputable def reducedBaseRingIso (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) :
    inverseImageReducedBaseRing t f' ≅
      (pushforwardCommRingFunctor i.toToposHom).obj
        ((inverseImageCommRingFunctor f.toToposHom).obj S.O) :=
  haveI : (pushforwardCommRingFunctor i.toToposHom).IsEquivalence :=
    pushforwardCommRingFunctor_isEquivalence i.toToposHom hi.equiv
  haveI : (inverseImageCommRingFunctor i.toToposHom).IsEquivalence :=
    (commRingImageAdjunction i.toToposHom).isEquivalence_left_of_isEquivalence_right
  asIso ((commRingImageAdjunction i.toToposHom).unit.app (inverseImageReducedBaseRing t f')) ≪≫
    (pushforwardCommRingFunctor i.toToposHom).mapIso
      (reducedBaseRingComparisonIso i t f f' comm ht)

/-- The comparison of the two base rings is compatible with the two structure maps: followed
by the direct image along `i` of the structure map `f⁻¹O_ℬ ⟶ O` of `f`, the comparison
`f'⁻¹(t_*O_ℬ) ≅ i_*(f⁻¹O_ℬ)` is the structure map
`Deformation.ToposThickening.inverseImageReducedStructureMap`. -/
theorem reducedBaseRingIso_hom_comp (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) :
    (reducedBaseRingIso i t f f' comm hi ht).hom ≫
        (pushforwardCommRingFunctor i.toToposHom).map f.fSharpInverseImage =
      inverseImageReducedStructureMap i t f f' comm := by
  set PT := (pushforwardCommRingFunctor t.toToposHom).obj S.O
  have qIeq : (inverseImageCommRingFunctor (f'.comp i).toToposHom).obj PT =
      (inverseImageCommRingFunctor (t.comp f).toToposHom).obj PT :=
    congrArg (fun m : RingedToposHom X S' ↦
      (inverseImageCommRingFunctor m.toToposHom).obj PT) comm
  have qPeq : (pushforwardCommRingFunctor (t.comp f).toToposHom).obj X.O =
      (pushforwardCommRingFunctor (f'.comp i).toToposHom).obj X.O :=
    congrArg (fun m : RingedToposHom X S' ↦
      (pushforwardCommRingFunctor m.toToposHom).obj X.O) comm.symm
  set cI₁ := (inverseImageCompIso f'.toToposHom i.toToposHom PT).hom
  set qI := eqToHom qIeq
  set cI₂ := (inverseImageCompIso t.toToposHom f.toToposHom PT).inv
  set ct := (inverseImageCommRingFunctor f.toToposHom).map
    ((commRingImageAdjunction t.toToposHom).counit.app S.O)
  set kf := f.fSharpInverseImage
  set ui := (commRingImageAdjunction i.toToposHom).unit.app (inverseImageReducedBaseRing t f')
  set qP := eqToHom qPeq
  set cP₁ := (pushforwardCommRingCompIso f.toToposHom t.toToposHom X.O).hom
  set cP₂ := (pushforwardCommRingCompIso i.toToposHom f'.toToposHom X.O).inv
  have hassoc : (cI₁ ≫ qI ≫ cI₂ ≫ ct) ≫ kf = cI₁ ≫ qI ≫ cI₂ ≫ ct ≫ kf :=
    (Category.assoc cI₁ (qI ≫ cI₂ ≫ ct) kf).trans
      (congrArg (fun z ↦ cI₁ ≫ z)
        ((Category.assoc qI (cI₂ ≫ ct) kf).trans
          (congrArg (fun z ↦ qI ≫ z) (Category.assoc cI₂ ct kf))))
  have hnorm : (ui ≫ (pushforwardCommRingFunctor i.toToposHom).map (cI₁ ≫ qI ≫ cI₂ ≫ ct)) ≫
      (pushforwardCommRingFunctor i.toToposHom).map kf =
        ui ≫ (pushforwardCommRingFunctor i.toToposHom).map (cI₁ ≫ qI ≫ cI₂ ≫ ct ≫ kf) :=
    (Category.assoc ui _ _).trans
      (congrArg (fun z ↦ ui ≫ z)
        (((pushforwardCommRingFunctor i.toToposHom).map_comp
              (cI₁ ≫ qI ≫ cI₂ ≫ ct) kf).symm.trans
          (congrArg (fun z ↦ (pushforwardCommRingFunctor i.toToposHom).map z) hassoc)))
  have hcI₁ := forget_map_inverseImageCompIso_hom f'.toToposHom i.toToposHom PT
  have hcI₂ := forget_map_inverseImageCompIso_inv t.toToposHom f.toToposHom PT
  have hct := (forget_map_inverseImage_map f.toToposHom
      ((commRingImageAdjunction t.toToposHom).counit.app S.O)).trans
    (congrArg (fun z ↦ f.toToposHom.inverseImage.map z)
      (commRingImageAdjunction_counit_forget t.toToposHom S.O))
  have hkf := AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget f
  have hXi := (map_comp_cancel (qI ≫ cI₂ ≫ ct ≫ kf) hcI₁ (Category.id_comp _)).trans
    (((sheafCompose X.J (forget CommRingCat.{w})).map_comp qI (cI₂ ≫ ct ≫ kf)).trans
      (congrArg₂ (· ≫ ·)
        (CategoryTheory.eqToHom_map (sheafCompose X.J (forget CommRingCat.{w})) qIeq)
        ((map_comp_cancel (ct ≫ kf) hcI₂ (Category.id_comp _)).trans
          (((sheafCompose X.J (forget CommRingCat.{w})).map_comp ct kf).trans
            (congrArg₂ (· ≫ ·) hct hkf)))))
  have hL := ((sheafCompose X'.J (forget CommRingCat.{w})).map_comp ui
      ((pushforwardCommRingFunctor i.toToposHom).map (cI₁ ≫ qI ≫ cI₂ ≫ ct ≫ kf))).trans
    (congrArg₂ (· ≫ ·)
      (forget_map_commRingImageAdjunction_unit_app i.toToposHom
        (inverseImageReducedBaseRing t f'))
      ((forget_map_pushforward_map i.toToposHom (cI₁ ≫ qI ≫ cI₂ ≫ ct ≫ kf)).trans
        (congrArg (fun z ↦ i.toToposHom.pushforward.map z) hXi)))
  have hcP₁ := pushforwardCommRingCompIso_hom_forget f.toToposHom t.toToposHom X.O
  have hcP₂ := forget_map_pushforwardCompIso_inv f'.toToposHom i.toToposHom X.O
  have hPSC := ((sheafCompose S'.J (forget CommRingCat.{wS'})).map_comp
      ((pushforwardCommRingFunctor t.toToposHom).map f.fSharp) (cP₁ ≫ qP ≫ cP₂)).trans
    (congrArg₂ (· ≫ ·) (forget_map_pushforward_map t.toToposHom f.fSharp)
      ((map_comp_cancel (qP ≫ cP₂) hcP₁ (Category.id_comp _)).trans
        (((sheafCompose S'.J (forget CommRingCat.{wS'})).map_comp qP cP₂).trans
          ((congrArg₂ (· ≫ ·)
              (CategoryTheory.eqToHom_map
                (sheafCompose S'.J (forget CommRingCat.{wS'})) qPeq) hcP₂).trans
            (Category.comp_id _)))))
  have hR := (forget_map_homEquiv_symm f'.toToposHom PT
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)
      ((pushforwardCommRingFunctor t.toToposHom).map f.fSharp ≫ cP₁ ≫ qP ≫ cP₂)).trans
    ((Adjunction.homEquiv_counit f'.toToposHom.adj _ _ _).trans
      (congrArg (fun z ↦ f'.toToposHom.inverseImage.map z ≫
          f'.toToposHom.adj.counit.app ((sheafCompose X'.J (forget CommRingCat.{w})).obj
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) hPSC))
  exact (sheafCompose X'.J (forget CommRingCat.{w})).map_injective
    ((congrArg (fun z ↦ (sheafCompose X'.J (forget CommRingCat.{w})).map z) hnorm).trans
      (hL.trans
        ((unit_comp_pushforward_eq i.toToposHom t.toToposHom f.toToposHom f'.toToposHom
            (congrArg (fun m : RingedToposHom X S' ↦ m.toToposHom) comm) _ _ _).trans
          hR.symm)))

end Comparison

/-! ## Flatness over the base, in the two readings -/

section FlatnessOverBase

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- For a morphism `(f, f')` of first order thickenings of ringed topoi and an `i_*O`-module `ℱ`
flat over `i_*(f⁻¹O_ℬ)`, the module `ℱ` read over `f'⁻¹(t_*O_ℬ)` — the presentation of `f⁻¹O_ℬ`
on the thickened topos that `Deformation.ToposThickening.reducedBaseModule` uses — is flat. -/
theorem isFlat_reducedBaseModule_of_isFlatOverBase
    (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
    (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
    (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (hF : IsFlatOverBase i f F) :
    AlgebraicGeometry.SheafOfModules.IsFlat (reducedBaseModule i t f f' comm F) := by
  have hsplit : reducedBaseModule i t f f' comm F =
      (SheafOfModules.restrictScalars
        (ringMap (reducedBaseRingIso i t f f' comm hi ht).hom ≫
          ringMap ((pushforwardCommRingFunctor i.toToposHom).map
            f.fSharpInverseImage))).obj F :=
    congrArg (fun m ↦ (SheafOfModules.restrictScalars m).obj F)
      ((congrArg (fun z ↦ ringMap z)
          (reducedBaseRingIso_hom_comp i t f f' comm hi ht).symm).trans
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map_comp _ _))
  have hiter : (SheafOfModules.restrictScalars
        (ringMap (reducedBaseRingIso i t f f' comm hi ht).hom ≫
          ringMap ((pushforwardCommRingFunctor i.toToposHom).map
            f.fSharpInverseImage))).obj F =
      (SheafOfModules.restrictScalars
        (ringMap (reducedBaseRingIso i t f f' comm hi ht).hom)).obj
          ((SheafOfModules.restrictScalars
            (ringMap ((pushforwardCommRingFunctor i.toToposHom).map
              f.fSharpInverseImage))).obj F) :=
    congrArg (fun G ↦ G.obj F)
      (Stacks.Sheaves.RingedToposModules.restrictScalars_comp
        (ringMap (reducedBaseRingIso i t f f' comm hi ht).hom)
        (ringMap ((pushforwardCommRingFunctor i.toToposHom).map f.fSharpInverseImage))).symm
  rw [hsplit, hiter]
  exact isFlat_restrictScalars_of_iso (reducedBaseRingIso i t f f' comm hi ht) _ hF

end FlatnessOverBase

end Deformation.ToposThickening

end
