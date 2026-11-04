module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorMate

/-! # The comparison of Stacks 03EL against the mate of a transformation of direct images

Let `f, g : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be two morphisms of ringed topoi with the same source and
target, in the sense of `Stacks.Sheaves.RingedToposModules.RingedToposHom`. A transformation
`τ : f_* ⟶ g_*` of the direct images of sheaves of modules has a **mate** `β : g^* ⟶ f^*` under the
two adjunctions of Stacks 03D7. If `τ` is, on underlying sheaves of sets, a transformation of the
direct images of sheaves of sets, then **the comparison of Stacks 03EL is monoidal in the
2-morphism variable**,

`β_{F ⊗ G} ≫ c_f = c_g ≫ (β_F ⊗ β_G)`.

This is the situation of a 2-morphism of morphisms of ringed topoi (Stacks 04IC); `τ` is not
assumed to come from one, nor to be invertible.

## Main results

* `Stacks.SheafOfModules.hom_ext_prod'`: two morphisms out of a binary product of sheaves of sets
  agree as soon as they agree on all pairs of local sections.
* `Stacks.SheafOfModules.prodMap_mate_comp_pullbackTensorBottomPairing`: **the pairing identity**
  — the topos-level mates on the two tensor factors commute with the two pairings at the bottom of
  the chain of Stacks 03EL and the module-level mate on the tensor product of the two pullbacks.
* `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_mate`: **the law.** The comparison of
  Stacks 03EL commutes with the mate of a transformation of direct images.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct

universe v u w v' u' w' t

namespace Stacks.SheafOfModules

section Generic

variable {C₀ : Type u} [Category.{v} C₀] {J₀ : GrothendieckTopology C₀}

/-- **Two morphisms out of a binary product of sheaves of sets agree as soon as they agree on all
pairs of local sections.** -/
lemma hom_ext_prod' {A B E : Sheaf J₀ (Type t)} {m m' : A ⨯ B ⟶ E}
    (h : ∀ (V : C₀ᵒᵖ) (x : (Sheaf.sectionsFunctor J₀ V).obj A)
      (y : (Sheaf.sectionsFunctor J₀ V).obj B),
      (Sheaf.sectionsFunctor J₀ V).map m
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{t} J₀ V) x y) =
        (Sheaf.sectionsFunctor J₀ V).map m'
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{t} J₀ V) x y)) :
    m = m' := by
  refine Sheaf.hom_ext_sections fun V s ↦ ?_
  rw [← Functor.prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor.{t} J₀ V) s]
  exact h V _ _

end Generic

section Tmul

variable {R : Type t} [CommRing R] {M N : Type t} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Pure tensors of equal factors are equal. -/
private lemma tmul_congr {m m' : M} {n n' : N} (hm : m = m') (hn : n = n') :
    m ⊗ₜ[R] n = m' ⊗ₜ[R] n' := by
  rw [hm, hn]

end Tmul

section Mate

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (tt : f.toToposHom.pushforward ⟶ g.toToposHom.pushforward)
  (τ : pushforwardModules f ⟶ pushforwardModules g)
  (M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The mate on a local section is the sections functor applied to its underlying morphism of
sheaves of sets.** -/
private lemma mate_val_app_eq_sectionsFunctor_map (V : X.Cᵒᵖ)
    (y : (Sheaf.sectionsFunctor X.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((g.pullbackModules).obj M))) :
    (((conjugateEquiv (pullbackAdjPushforwardModules f)
          (pullbackAdjPushforwardModules g)).symm τ).app M).val.app V y =
      (Sheaf.sectionsFunctor X.J V).map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          (((conjugateEquiv (pullbackAdjPushforwardModules f)
            (pullbackAdjPushforwardModules g)).symm τ).app M)) y :=
  (sectionsFunctor_map_moduleSheafFunctor_map' (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (((conjugateEquiv (pullbackAdjPushforwardModules f)
      (pullbackAdjPushforwardModules g)).symm τ).app M) V y).symm

/-- **The identity of Stacks 03CZ against the mate, read on a local section**: the unit of
extension of scalars for `g` followed by the module-level mate is the topos-level mate followed by
the unit for `f`. -/
private lemma sectionsFunctor_map_extendScalarsUnit_comp_mate (V : X.Cᵒᵖ)
    (hτ : ∀ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map (τ.app N) =
        tt.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))
    (x : ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M).val.obj V) :
    (Sheaf.sectionsFunctor X.J V).map
        (extendScalarsUnitSheafHom g M ≫
          (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
            (((conjugateEquiv (pullbackAdjPushforwardModules f)
              (pullbackAdjPushforwardModules g)).symm τ).app M)) x =
      (Sheaf.sectionsFunctor X.J V).map
        (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M) ≫
          extendScalarsUnitSheafHom f M) x :=
  congrArg (fun m ↦ (Sheaf.sectionsFunctor X.J V).map m x)
    (extendScalarsUnitSheafHom_comp_mate f g tt τ hτ M)

/-- **The mate of a transformation of direct images against the unit of Stacks 03CZ, on a local
section**: the mate of the sheaves-of-modules transformation applied after the unit of Stacks 03CZ
for `g` is the unit for `f` applied after the mate of the sheaves-of-sets transformation. -/
private lemma sectionsFunctor_map_extendScalarsUnitSheafHom_comp_mate (V : X.Cᵒᵖ)
    (hτ : ∀ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map (τ.app N) =
        tt.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))
    (x : ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M).val.obj V) :
    (((conjugateEquiv (pullbackAdjPushforwardModules f)
          (pullbackAdjPushforwardModules g)).symm τ).app M).val.app V
        ((Sheaf.sectionsFunctor X.J V).map (extendScalarsUnitSheafHom g M) x) =
      (Sheaf.sectionsFunctor X.J V).map (extendScalarsUnitSheafHom f M)
        ((Sheaf.sectionsFunctor X.J V).map
          (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M)) x) :=
  by
  refine (mate_val_app_eq_sectionsFunctor_map f g τ M V _).trans ?_
  refine ((Sheaf.sectionsFunctor X.J V).map_comp_apply _ _ x).symm.trans ?_
  refine (sectionsFunctor_map_extendScalarsUnit_comp_mate f g tt τ M V hτ x).trans ?_
  exact (Sheaf.sectionsFunctor X.J V).map_comp_apply _ _ x

/-- **The mate of a transformation of direct images against the unit of Stacks 03CZ, on a local
section**, with the unit of Stacks 03CZ written as the unit of
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction` on both sides. -/
private lemma mate_val_app_extendScalarsUnit (V : X.Cᵒᵖ)
    (hτ : ∀ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map (τ.app N) =
        tt.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))
    (x : ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M).val.obj V) :
    (((conjugateEquiv (pullbackAdjPushforwardModules f)
          (pullbackAdjPushforwardModules g)).symm τ).app M).val.app V
        (((extendRestrictScalarsAdjunction X.J (fSharpCommRing g)
              (inverseImageRingSheaf g.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules g.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M)).val.app V x) =
      ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M)).val.app V
        ((Sheaf.sectionsFunctor X.J V).map
          (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M)) x) :=
  (congrArg (fun z ↦ (((conjugateEquiv (pullbackAdjPushforwardModules f)
          (pullbackAdjPushforwardModules g)).symm τ).app M).val.app V z)
      (sectionsFunctor_map_extendScalarsUnitSheafHom g M V x).symm).trans
    ((sectionsFunctor_map_extendScalarsUnitSheafHom_comp_mate f g tt τ M V hτ x).trans
      (sectionsFunctor_map_extendScalarsUnitSheafHom f M V
        ((Sheaf.sectionsFunctor X.J V).map
          (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M)) x)))

variable (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The left-hand side of the pairing identity on a pair of local sections**: the topos-level
mates on the two factors, followed by the pairing at the bottom of the chain of Stacks 03EL for
`f`, carry a pair of sections to the sheafification-unit image of the pure tensor of the images
of the two mates under the unit of Stacks 03CZ for `f`. -/
private lemma sectionsFunctor_map_prodMap_comp_pullbackTensorBottomPairing (V : X.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor X.J V).obj
      (g.toToposHom.inverseImage.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)))
    (s : (Sheaf.sectionsFunctor X.J V).obj
      (g.toToposHom.inverseImage.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))) :
    (Sheaf.sectionsFunctor X.J V).map
        (prod.map
            (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
            (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
          ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
            (pullbackTensorBottomHom f F G)).1)
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} X.J V) x s) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf X.J X.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) (𝟙 _)).unit.app
          (((f.pullbackModules).obj F).val ⊗ ((f.pullbackModules).obj G).val)).app V
        ((((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
                (inverseImageRingSheaf f.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
              ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)).val.app V
            ((Sheaf.sectionsFunctor X.J V).map
              (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
                (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)) x))
          ⊗ₜ[(ringPresheaf X.O.obj).obj V]
          (((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
                (inverseImageRingSheaf f.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
              ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).val.app V
            ((Sheaf.sectionsFunctor X.J V).map
              (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
                (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) s))) :=
  ((Sheaf.sectionsFunctor X.J V).map_comp_apply
      (prod.map
        (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
        (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
      ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1 _).trans
    ((congrArg ((Sheaf.sectionsFunctor X.J V).map
          ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
            (pullbackTensorBottomHom f F G)).1)
        (Limits.map_prodMap_prodObjMk (P := Sheaf.sectionsFunctor.{w} X.J V)
          (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) x s)).trans
      (pairingApp_pullbackTensorBottom f F G V _ _))

/-- **The right-hand side of the pairing identity on a pair of local sections**: the pairing at
the bottom of the chain of Stacks 03EL for `g`, followed by the mate on the tensor product of the
two pullbacks, carries a pair of sections to the sheafification-unit image of the pure tensor of
the images of the two units of Stacks 03CZ for `g` under the two components of the mate. -/
private lemma sectionsFunctor_map_pullbackTensorBottomPairing_comp_mateTensorSheafHom (V : X.Cᵒᵖ)
    (x : ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).val.obj V)
    (s : ((inverseImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G).val.obj V) :
    (Sheaf.sectionsFunctor X.J V).map
        (((pullbackTensorStep4 g F G (pullbackTensorTarget g F G)).symm
            (pullbackTensorBottomHom g F G)).1 ≫
          mateTensorSheafHom f g τ F G)
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} X.J V) x s) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf X.J X.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) (𝟙 _)).unit.app
          (((f.pullbackModules).obj F).val ⊗ ((f.pullbackModules).obj G).val)).app V
        ((((conjugateEquiv (pullbackAdjPushforwardModules f)
                  (pullbackAdjPushforwardModules g)).symm τ).app F).val.app V
            (((extendRestrictScalarsAdjunction X.J (fSharpCommRing g)
                  (inverseImageRingSheaf g.toToposHom
                      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
                ((inverseImageModules g.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)).val.app V x)
          ⊗ₜ[(ringPresheaf X.O.obj).obj V]
          (((conjugateEquiv (pullbackAdjPushforwardModules f)
                  (pullbackAdjPushforwardModules g)).symm τ).app G).val.app V
            (((extendRestrictScalarsAdjunction X.J (fSharpCommRing g)
                  (inverseImageRingSheaf g.toToposHom
                      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
                ((inverseImageModules g.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).val.app V s)) :=
  ((Sheaf.sectionsFunctor X.J V).map_comp_apply
      ((pullbackTensorStep4 g F G (pullbackTensorTarget g F G)).symm
        (pullbackTensorBottomHom g F G)).1 (mateTensorSheafHom f g τ F G) _).trans
    ((congrArg ((Sheaf.sectionsFunctor X.J V).map (mateTensorSheafHom f g τ F G))
        (pairingApp_pullbackTensorBottom g F G V x s)).trans
      ((sectionsFunctor_map_moduleSheafFunctor_map'
          (inverseImageRingSheaf g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((SheafOfModules.restrictScalars g.fSharpInverseImage).map
            (mateTensorHom f g τ F G)) V _).trans
        (mateTensorHom_val_app_unit_tmul f g τ F G V _ _)))

/-- **The pairing identity: the topos-level mates on the two tensor factors commute with the two
pairings at the bottom of the chain of Stacks 03EL and the module-level mate on the tensor
product of the two pullbacks.** -/
lemma prodMap_mate_comp_pullbackTensorBottomPairing
    (hτ : ∀ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map (τ.app N) =
        tt.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :
    prod.map
        (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
        (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
      ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1 =
    ((pullbackTensorStep4 g F G (pullbackTensorTarget g F G)).symm
        (pullbackTensorBottomHom g F G)).1 ≫
      mateTensorSheafHom f g τ F G :=
  hom_ext_prod' fun V x s ↦
    (sectionsFunctor_map_prodMap_comp_pullbackTensorBottomPairing f g tt F G V x s).trans
      ((congrArg (fun z ↦ ((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf X.J X.O.obj
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) (𝟙 _)).unit.app
              (((f.pullbackModules).obj F).val ⊗ ((f.pullbackModules).obj G).val)).app V z)
          (tmul_congr (mate_val_app_extendScalarsUnit f g tt τ F V hτ x).symm
            (mate_val_app_extendScalarsUnit f g tt τ G V hτ s).symm)).trans
        (sectionsFunctor_map_pullbackTensorBottomPairing_comp_mateTensorSheafHom f g τ F G
          V x s).symm)

/-- A composite with the image of an identity under two functors. -/
private lemma comp_map_map_id {A₁ B₁ E₁ : Type*} [Category A₁] [Category B₁] [Category E₁]
    (Φ : A₁ ⥤ B₁) (Ψ : B₁ ⥤ E₁) {N₁ : A₁} {P₁ : E₁} (q : P₁ ⟶ Ψ.obj (Φ.obj N₁)) :
    q ≫ Ψ.map (Φ.map (𝟙 N₁)) = q := by
  rw [Φ.map_id, Ψ.map_id, Category.comp_id]

/-- **The pairing identity with the product comparison of the inverse image in front.** -/
private lemma mate_comp_prodComparison_comp_pullbackTensorBottomPairing
    (hτ : ∀ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map (τ.app N) =
        tt.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :
    (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
          ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))) ≫
        (prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
          ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1 =
      (prodComparison g.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
        ((pullbackTensorStep4 g F G (pullbackTensorTarget g F G)).symm
        (pullbackTensorBottomHom g F G)).1 ≫ (mateTensorSheafHom f g τ F G) :=
  ((Category.assoc _ _ _).symm).trans
    ((congrArg (fun m ↦ m ≫ ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1)
        (prodComparison_naturality g.toToposHom.inverseImage f.toToposHom.inverseImage
          ((conjugateEquiv f.toToposHom.adj g.toToposHom.adj).symm tt)
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun m ↦ (prodComparison g.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫ m)
          (prodMap_mate_comp_pullbackTensorBottomPairing f g tt τ F G hτ))))

variable [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **The left-hand side of the transposed law on the unit image of a pure tensor.** The last
five steps of the chain of Stacks 03EL for `f`, traversed backwards from the identity and followed
by `τ`, carry the unit image of `a ⊗ₜ r` to the pair `(a, r)` pushed through the unit of
`f⁻¹ ⊣ f_*`, then through the direct image of the product comparison followed by the pairing at
the bottom, and finally through `τ`. -/
private lemma transposedComparison_comp_mate_val_app_unit_tmul (U : Y.Cᵒᵖ) (a : F.val.obj U)
    (r : G.val.obj U) :
    (((pullbackTensorStep2 f F G
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
        ((pullbackTensorStep3 f F G
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          ((pullbackTensorStep4 f F G
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
            ((pullbackTensorStep5 f F G
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
              ((pullbackTensorStep6 f F G
                  (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          (𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
                  ((f.pullbackModules).obj F, (f.pullbackModules).obj G)))))))) ≫
          τ.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf Y.J Y.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) (𝟙 _)).unit.app
          (F.val ⊗ G.val)).app U (a ⊗ₜ[(ringPresheaf Y.O.obj).obj U] r)) =
      (τ.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).val.app U
        ((Sheaf.sectionsFunctor Y.J U).map
          (f.toToposHom.pushforward.map
            ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
              ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1))
          ((Sheaf.sectionsFunctor Y.J U).map
            (f.toToposHom.adj.unit.app
                ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
            (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r))) :=
  (CategoryTheory.comp_apply _ _ _).trans
    ((congrArg (fun z ↦ (τ.app
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).val.app U z)
        (pullbackTensorStep2to6_symm_val_app_unit_tmul f F G
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))
          (𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))) U a r)).trans
      (congrArg (fun m ↦ (τ.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).val.app U
          ((Sheaf.sectionsFunctor Y.J U).map
            (f.toToposHom.pushforward.map
              ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫ m))
            ((Sheaf.sectionsFunctor Y.J U).map
              (f.toToposHom.adj.unit.app
                  ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
              (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r))))
        (comp_map_map_id (N₁ :=
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G)))
          (SheafOfModules.restrictScalars f.fSharpInverseImage)
          (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1)))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **`τ` on a section is `tt`, and `tt` is natural**: applying `τ` after the direct image along
`f` of a morphism upstairs is applying `tt` first and then the direct image along `g` of the same
morphism. -/
private lemma mate_val_app_sectionsFunctor_map_pushforward_map
    (hτ : ∀ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map (τ.app N) =
        tt.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))
    (U : Y.Cᵒᵖ)
    (y : (Sheaf.sectionsFunctor Y.J U).obj
      (f.toToposHom.pushforward.obj
        (f.toToposHom.inverseImage.obj
            ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))))) :
    (τ.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).val.app U
        ((Sheaf.sectionsFunctor Y.J U).map
          (f.toToposHom.pushforward.map
            ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
              ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1)) y) =
      (Sheaf.sectionsFunctor Y.J U).map
        (g.toToposHom.pushforward.map
          ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
            ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1))
        ((Sheaf.sectionsFunctor Y.J U).map
          (tt.app (f.toToposHom.inverseImage.obj
              ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))) y) :=
  ((sectionsFunctor_map_moduleSheafFunctor_map' (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        (τ.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))) U _).symm.trans
      (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m
          ((Sheaf.sectionsFunctor Y.J U).map
            (f.toToposHom.pushforward.map
              ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
                ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1)) y))
        (hτ (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))))).trans
    (((Sheaf.sectionsFunctor Y.J U).map_comp_apply
          (f.toToposHom.pushforward.map
            ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
              ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1))
          (tt.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G)))) y).symm.trans
      ((congrArg (fun n ↦ (Sheaf.sectionsFunctor Y.J U).map n y)
          (tt.naturality
            ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
              ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1))).trans
        ((Sheaf.sectionsFunctor Y.J U).map_comp_apply
          (tt.app (f.toToposHom.inverseImage.obj
              ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))))
          (g.toToposHom.pushforward.map
            ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
              ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1)) y)))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The topos-level mate identity on the pair of local sections.** The unit of `f⁻¹ ⊣ f_*`
followed by `tt` is the unit of `g⁻¹ ⊣ g_*` followed by the direct image of the topos-level mate,
on the pair `(a, r)`. -/
private lemma sectionsFunctor_map_toposMate_unit (U : Y.Cᵒᵖ) (a : F.val.obj U) (r : G.val.obj U) :
    (Sheaf.sectionsFunctor Y.J U).map
        (tt.app (f.toToposHom.inverseImage.obj
            ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))))
        ((Sheaf.sectionsFunctor Y.J U).map
          (f.toToposHom.adj.unit.app
              ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r)) =
      (Sheaf.sectionsFunctor Y.J U).map
        (g.toToposHom.pushforward.map (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
          ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))))
        ((Sheaf.sectionsFunctor Y.J U).map
          (g.toToposHom.adj.unit.app
              ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r)) :=
  ((Sheaf.sectionsFunctor Y.J U).map_comp_apply
        (f.toToposHom.adj.unit.app
            ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
        (tt.app (f.toToposHom.inverseImage.obj
            ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))))
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r)).symm.trans
    ((congrArg (fun n ↦ (Sheaf.sectionsFunctor Y.J U).map n
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r))
        (unit_conjugateEquiv_symm f.toToposHom.adj g.toToposHom.adj tt
          ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))).trans
      ((Sheaf.sectionsFunctor Y.J U).map_comp_apply
        (g.toToposHom.adj.unit.app
            ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
        (g.toToposHom.pushforward.map (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
          ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))))
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r)))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Two successive direct images along `g` of morphisms upstairs are the direct image of their
composite. -/
private lemma sectionsFunctor_map_pushforward_map_comp (U : Y.Cᵒᵖ) (a : F.val.obj U)
    (r : G.val.obj U) :
    (Sheaf.sectionsFunctor Y.J U).map
        (g.toToposHom.pushforward.map
          ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
            ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1))
        ((Sheaf.sectionsFunctor Y.J U).map
          (g.toToposHom.pushforward.map (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
          ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))))
          ((Sheaf.sectionsFunctor Y.J U).map
            (g.toToposHom.adj.unit.app
                ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
            (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r))) =
      (Sheaf.sectionsFunctor Y.J U).map
        (g.toToposHom.pushforward.map
          ((((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
          ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))) ≫
            (prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
              ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1))
        ((Sheaf.sectionsFunctor Y.J U).map
          (g.toToposHom.adj.unit.app
              ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r)) :=
  ((Sheaf.sectionsFunctor Y.J U).map_comp_apply
        (g.toToposHom.pushforward.map (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
          ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))))
        (g.toToposHom.pushforward.map
          ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
            ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1)) _).symm.trans
    (congrArg (fun n ↦ (Sheaf.sectionsFunctor Y.J U).map n
        ((Sheaf.sectionsFunctor Y.J U).map
          (g.toToposHom.adj.unit.app
              ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r)))
      (g.toToposHom.pushforward.map_comp (((conjugateEquiv f.toToposHom.adj
          g.toToposHom.adj).symm tt).app
          ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
        ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
          ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1)).symm)

/-- **The right-hand side of the transposed law on the unit image of a pure tensor**: the value of
the chain of Stacks 03EL for `g` at the mate on the tensor product of the two pullbacks, where the
morphism inside the direct image is the pairing at the bottom of the chain for `g` followed by
`Stacks.SheafOfModules.mateTensorSheafHom`. -/
private lemma transposedComparison_mateTensorHom_val_app_unit_tmul (U : Y.Cᵒᵖ)
    (a : F.val.obj U) (r : G.val.obj U) :
    (((pullbackTensorStep2 g F G
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
        ((pullbackTensorStep3 g F G
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          ((pullbackTensorStep4 g F G
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
            ((pullbackTensorStep5 g F G
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
              ((pullbackTensorStep6 g F G
                  (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          (mateTensorHom f g τ F G))))))).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf Y.J Y.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) (𝟙 _)).unit.app
          (F.val ⊗ G.val)).app U (a ⊗ₜ[(ringPresheaf Y.O.obj).obj U] r)) =
      (Sheaf.sectionsFunctor Y.J U).map
        (g.toToposHom.pushforward.map
          ((prodComparison g.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
            ((pullbackTensorStep4 g F G (pullbackTensorTarget g F G)).symm
        (pullbackTensorBottomHom g F G)).1 ≫ (mateTensorSheafHom f g τ F G)))
        ((Sheaf.sectionsFunctor Y.J U).map
          (g.toToposHom.adj.unit.app
              ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r)) :=
  pullbackTensorStep2to6_symm_val_app_unit_tmul g F G
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))
    (mateTensorHom f g τ F G) U a r

/-- **The law of Stacks 03EL for a mate, transposed to the target topos**: the last five steps of
the chain of Stacks 03EL for `f`, traversed backwards from the identity and followed by `τ`, are
the same five steps for `g` traversed backwards from the mate on the tensor product of the two
pullbacks. -/
private lemma transposedMateLaw
    (hτ : ∀ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map (τ.app N) =
        tt.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :
    ((pullbackTensorStep2 f F G
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
        ((pullbackTensorStep3 f F G
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          ((pullbackTensorStep4 f F G
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
            ((pullbackTensorStep5 f F G
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
              ((pullbackTensorStep6 f F G
                  (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          (𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G)))))))) ≫
        τ.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G)) =
      ((pullbackTensorStep2 g F G
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
        ((pullbackTensorStep3 g F G
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          ((pullbackTensorStep4 g F G
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
            ((pullbackTensorStep5 g F G
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
              ((pullbackTensorStep6 g F G
                  (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          (mateTensorHom f g τ F G)))))) := by
  refine tensorSheaf_hom_ext fun U a r ↦ ?_
  exact (transposedComparison_comp_mate_val_app_unit_tmul f g τ F G U a r).trans
    ((mate_val_app_sectionsFunctor_map_pushforward_map f g tt τ F G hτ U _).trans
      ((congrArg (fun z ↦ (Sheaf.sectionsFunctor Y.J U).map
            (g.toToposHom.pushforward.map
              ((prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) ≫
                ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)).1)) z)
          (sectionsFunctor_map_toposMate_unit f g tt F G U a r)).trans
        ((sectionsFunctor_map_pushforward_map_comp f g tt F G U a r).trans
          ((congrArg (fun n ↦ (Sheaf.sectionsFunctor Y.J U).map
                (g.toToposHom.pushforward.map n) ((Sheaf.sectionsFunctor Y.J U).map
          (g.toToposHom.adj.unit.app
              ((Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ⨯
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
          (B := (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) a r)))
              (mate_comp_prodComparison_comp_pullbackTensorBottomPairing f g tt τ F G hτ)).trans
            (transposedComparison_mateTensorHom_val_app_unit_tmul f g τ F G U a r).symm))))

/-- **The adjoint transpose of the comparison of Stacks 03EL followed by a morphism is the last five
steps of the chain traversed backwards from that morphism.** -/
private lemma homEquiv_pullbackTensorIso_hom_app_comp
    (k : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    {N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (ρ : (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((k.pullbackModules).obj F, (k.pullbackModules).obj G)) ⟶ N) :
    (pullbackAdjPushforwardModules k).homEquiv
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) N
        ((pullbackTensorIso k).hom.app (F, G) ≫ ρ) =
      (pullbackTensorStep2 k F G N).symm ((pullbackTensorStep3 k F G N).symm
        ((pullbackTensorStep4 k F G N).symm ((pullbackTensorStep5 k F G N).symm
          ((pullbackTensorStep6 k F G N).symm ρ)))) :=
  (congrArg ((pullbackAdjPushforwardModules k).homEquiv
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) N)
      (((congrArg (fun m ↦ m ≫ ρ) (pullbackTensorIso_hom_app k F G)).trans
          (pullbackTensorHomEquiv_symm_naturality k F G
            (𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
              ((k.pullbackModules).obj F, (k.pullbackModules).obj G))) ρ).symm).trans
        (congrArg (pullbackTensorHomEquiv k F G N).symm (Category.id_comp ρ)))).trans
    (Equiv.apply_symm_apply (pullbackTensorStep1 k F G N) _)

/-- **The adjoint transpose of the comparison of Stacks 03EL is the last five steps of the chain
traversed backwards from the identity.** -/
private lemma homEquiv_pullbackTensorIso_hom_app :
    (pullbackAdjPushforwardModules f).homEquiv
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G))
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))
        ((pullbackTensorIso f).hom.app (F, G)) =
      ((pullbackTensorStep2 f F G
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
        ((pullbackTensorStep3 f F G
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          ((pullbackTensorStep4 f F G
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
            ((pullbackTensorStep5 f F G
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
              ((pullbackTensorStep6 f F G
                  (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          (𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G)))))))) := by
  rw [← Category.comp_id ((pullbackTensorIso f).hom.app (F, G))]
  exact homEquiv_pullbackTensorIso_hom_app_comp F G f _

/-- **The adjoint transpose of the comparison of Stacks 03EL followed by the mate on the tensor
product of the two pullbacks** is the last five steps of the chain for `g`, traversed backwards
from that mate. -/
private lemma homEquiv_pullbackTensorIso_hom_app_comp_mateTensorHom :
    (pullbackAdjPushforwardModules g).homEquiv
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G))
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))
        ((pullbackTensorIso g).hom.app (F, G) ≫ mateTensorHom f g τ F G) =
      ((pullbackTensorStep2 g F G
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
        ((pullbackTensorStep3 g F G
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          ((pullbackTensorStep4 g F G
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
            ((pullbackTensorStep5 g F G
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
              ((pullbackTensorStep6 g F G
                  (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          (mateTensorHom f g τ F G)))))) :=
  homEquiv_pullbackTensorIso_hom_app_comp F G g (mateTensorHom f g τ F G)

/-- **The adjoint transpose of the left-hand side of the law**: the mate followed by the comparison
of Stacks 03EL for `f`, transposed along the adjunction of Stacks 03D7 for `g`, is the transpose of
the comparison for `f` followed by `τ`. -/
private lemma homEquiv_mate_comp_pullbackTensorIso_hom_app :
    (pullbackAdjPushforwardModules g).homEquiv
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G))
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))
        ((((conjugateEquiv (pullbackAdjPushforwardModules f)
        (pullbackAdjPushforwardModules g)).symm τ).app
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G))) ≫
          (pullbackTensorIso f).hom.app (F, G)) =
      ((pullbackTensorStep2 f F G
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
        ((pullbackTensorStep3 f F G
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          ((pullbackTensorStep4 f F G
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
            ((pullbackTensorStep5 f F G
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
              ((pullbackTensorStep6 f F G
                  (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).symm
          (𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G)))))))) ≫
        τ.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G)) :=
  ((Adjunction.homEquiv_unit (pullbackAdjPushforwardModules g)
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G))
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))
        ((((conjugateEquiv (pullbackAdjPushforwardModules f)
        (pullbackAdjPushforwardModules g)).symm τ).app
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G))) ≫
          (pullbackTensorIso f).hom.app (F, G))).trans
      ((congrArg (fun m ↦ (pullbackAdjPushforwardModules g).unit.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ≫ m)
          ((pushforwardModules g).map_comp (((conjugateEquiv (pullbackAdjPushforwardModules f)
        (pullbackAdjPushforwardModules g)).symm τ).app
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)))
            ((pullbackTensorIso f).hom.app (F, G)))).trans
        (((Category.assoc _ _ _).symm).trans
          (congrArg (fun m ↦ m ≫ (pushforwardModules g).map
              ((pullbackTensorIso f).hom.app (F, G)))
            (unit_conjugateEquiv_symm (pullbackAdjPushforwardModules f)
              (pullbackAdjPushforwardModules g) τ
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj
                  (F, G))).symm)))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ (pullbackAdjPushforwardModules f).unit.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ≫ m)
          (τ.naturality ((pullbackTensorIso f).hom.app (F, G))).symm).trans
        (((Category.assoc _ _ _).symm).trans
          (congrArg (fun m ↦ m ≫ τ.app
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G)))
            ((Adjunction.homEquiv_unit (pullbackAdjPushforwardModules f)
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G))
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))
                ((pullbackTensorIso f).hom.app (F, G))).symm.trans
              (homEquiv_pullbackTensorIso_hom_app f F G))))))

/-- **The comparison of Stacks 03EL is compatible with the mate of a transformation of direct
images.**

Let `f, g : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be two morphisms of ringed topoi with the same source and
target, let `τ : f_* ⟶ g_*` be a transformation of the direct images of sheaves of modules and let
`tt : f_* ⟶ g_*` be a transformation of the direct images of sheaves of sets which is `τ` on
underlying sheaves of sets (the hypothesis `hτ`). Write `β : g^* ⟶ f^*` for the mate of `τ` under
the two adjunctions of Stacks 03D7. Then for all sheaves of `O_D`-modules `F` and `G`

`β_{F ⊗ G} ≫ c_f = c_g ≫ (β_F ⊗ β_G)`,

where `c_h : h^*(F ⊗_{O_D} G) ⟶ h^*F ⊗_{O_C} h^*G` is the comparison of Stacks 03EL for `h`. That
is: **the comparison of Stacks 03EL is monoidal in the 2-morphism variable.** Neither `τ` nor `β`
is assumed invertible. -/
theorem pullbackTensorIso_hom_app_comp_mate
    (hτ : ∀ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map (τ.app N) =
        tt.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :
    ((conjugateEquiv (pullbackAdjPushforwardModules f)
          (pullbackAdjPushforwardModules g)).symm τ).app
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ≫
      (pullbackTensorIso f).hom.app (F, G) =
    (pullbackTensorIso g).hom.app (F, G) ≫ mateTensorHom f g τ F G := by
  refine ((pullbackAdjPushforwardModules g).homEquiv
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G))
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))).injective ?_
  exact (homEquiv_mate_comp_pullbackTensorIso_hom_app f g τ F G).trans
    ((transposedMateLaw f g tt τ F G hτ).trans
      (homEquiv_pullbackTensorIso_hom_app_comp_mateTensorHom f g τ F G).symm)

end Mate

end Stacks.SheafOfModules

end
