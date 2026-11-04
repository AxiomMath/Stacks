module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitOpenPullback

/-!
# The canonical morphism of Frobenius colimits of a nested pair of opens is a restriction

Let `p` be a prime, let `X` be a scheme in characteristic `p` and let `U ≤ V` be opens of `X`.
There are two morphisms of sheaves of rings in sight:

* the **canonical morphism of Frobenius colimits**
  `AlgebraicGeometry.frobeniusColimitStructureSheafHom` of the inclusion
  `AlgebraicGeometry.Scheme.homOfLE` of the two open subschemes, which is the morphism the
  transition functor of [Stacks, Tag 0EXE] between the two opens extends scalars along;
* the **restriction to `V` of the canonical morphism of the inclusion `U.ι`**, read through
  `AlgebraicGeometry.frobeniusColimitRingSheafRestrictIso`, which identifies `colim_F 𝒪_V` with
  the restriction of `colim_F 𝒪_X` to `V`.

`AlgebraicGeometry.nested_restrictIso_compat` identifies them. This is the compatibility of
`AlgebraicGeometry.frobeniusColimitRingSheafRestrictIso` with a *pair* of nested opens; the
existing `AlgebraicGeometry.frobeniusColimitι_comp_frobeniusColimitRingSheafRestrictIso_hom` is
its compatibility with the stage coprojections at a *single* open.

The second half of the file builds the **restriction functor of the nested pair** —
`AlgebraicGeometry.frobeniusColimitNestedSiteRestrict`, from `colim_F 𝒪_V`-modules to
`colim_F 𝒪_U`-modules — and identifies it with the transition functor of [Stacks, Tag 0EXE] of
the inclusion `U ⟶ V`. That identification is an **instantiation** of
`AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunctionOfIso`, the form at an arbitrary
morphism of schemes with an adjoint site functor, and re-derives nothing of the single-open case.

## Main definitions

* `AlgebraicGeometry.nestedOpenRingPushMap` and `AlgebraicGeometry.nestedOpenRingPushIso`: **the
  comparison of the two restrictions of a sheaf of rings on `X` to `U`** — directly, or through
  `V` — written out at a fixed sheaf of rings.
* `AlgebraicGeometry.frobeniusColimitRingSheafNestedRestrictIso`: **`colim_F 𝒪_V` restricted to
  the smaller open `U` is `colim_F 𝒪_U`**, the nested-opens form of
  `AlgebraicGeometry.frobeniusColimitRingSheafRestrictIso`.
* `AlgebraicGeometry.frobeniusColimitNestedSiteRestrict`: **restriction of a sheaf of modules
  over `colim_F 𝒪_V` to the smaller open `U`.**
* `AlgebraicGeometry.frobeniusColimitNestedSiteRestrictAdjunction`: **it is left adjoint to
  pushforward along the inclusion `U ⟶ V`.**
* `AlgebraicGeometry.frobeniusColimitNestedSiteRestrictIsoPullback`: **hence it is the transition
  functor of [Stacks, Tag 0EXE] of that inclusion.**

## Main results

* `AlgebraicGeometry.homOfLE_ringSheafOnOpensHom_comp_natTrans`: **the same statement for the
  structure sheaves themselves.** This is the only piece of content: both sides restrict a
  section over the image of an open of `V` to the image of its preimage in `U`, so both are
  `X.presheaf.map` of a morphism of opens, and morphisms of opens are unique.
* `AlgebraicGeometry.nested_restrictIso_compat`: **the statement for `colim_F 𝒪`.** Both sides
  are morphisms out of the sequential colimit `colim_F 𝒪_V`, so
  `CategoryTheory.Limits.endoColimit_hom_ext` reduces it to the structure-sheaf statement above,
  the stage formula of `AlgebraicGeometry.frobeniusColimitStructureSheafHom` at the two
  inclusions, and the single-open compatibility of the restriction identification.
* `AlgebraicGeometry.imF_homOfLE_image_eq`: for `U ≤ V`, **an open of `U` has the same image in
  `X` whether one takes it directly or through `V`** — the companion on images of the statement
  on preimages above.
* `AlgebraicGeometry.homOfLE_counit_whiskerRight_eq` and
  `AlgebraicGeometry.nestedOpenRingPushMap_comp_frobeniusColimitι`: **the two inputs the general
  adjunction asks of the nested pair**, respectively on the structure sheaves and on the stage
  coprojections.

## Implementation notes

**The two sides live over different presentations of one site functor.** The canonical morphism
of the inclusion `X.homOfLE h` pushes forward along `Opens.map (X.homOfLE h).base`, whereas
restricting to `V` and then to `U` pushes forward along
`TopCat.Presheaf.imF V ⋙ Opens.map U.ι.base`. The two functors agree —
`AlgebraicGeometry.nestedOpenSiteIso`, whose components are the equalities of opens of
`AlgebraicGeometry.homOfLE_preimage_eq_imF_comp_mapι` and whose naturality is automatic because
a category of opens is thin — and `CategoryTheory.Functor.sheafPushforwardContinuousNatTrans`
transports one pushforward to the other.

**Everything is proved in term mode.** The source site is spelled `Opens ↥(V.toScheme)` on the
one side and `Opens (Stacks.Topology.openSubspace V)` on the other; the two agree only at
default transparency, so a goal mentioning both is not type-correct at the transparency a
rewrite motive is built at, and `rw`, `simp` and `calc` all fail on it with
`Application type mismatch: TopCat.Presheaf.imF V`. Term-mode composition of equalities is
checked at default transparency and goes through. For the same reason the two continuity
instances below are restated at the `V.toScheme` spelling: instance resolution does not unfold
`Stacks.Topology.openSubspace`.

**Why the restriction of the nested pair is built upstream and not bridged here.** The
`colim_F 𝒪_U` of the open subscheme is typed at the `U.toScheme` spelling of the `U`-site, while
`ExtensionByZeroModules.jStar` and its neighbours are typed at the
`Stacks.Topology.openSubspace` spelling; the two agree only at default transparency, so every
rewriting tactic refuses on a goal mentioning both and the forced term-mode identification costs
more than the heartbeat budget allows. `AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunction`
is therefore **generalised at the source** to
`AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunctionOfIso`, which takes the comparison of
the two structure sheaves as a parameter; the nested case is then an instantiation of it at one
spelling throughout, and there is nothing to identify.

**Why the second morphism is `frobeniusColimitStructureSheafHom p U.ι` and not the
extension-by-zero restriction map.** `ExtensionByZeroModules.toPushRing` is the restriction map
at an arbitrary sheaf of rings, and the composite
`toPushRing U (colim_F 𝒪_X)` followed by the restriction identification of `U` is this
morphism; but `toPushRing` is typed at the `Stacks.Topology.openSubspace U` spelling of the
target site while `colim_F 𝒪_U` is typed at the `U.toScheme` one, and combining them inside a
single term exhausts the heartbeat budget in `isDefEq`. The canonical morphism of `U.ι` is the
same map at one spelling throughout.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ExtensionByZeroModules
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- Taking the image in `X` of an open of the open subscheme `V` is continuous for the
topologies of opens. This is `ExtensionByZeroModules.imF_isContinuous` at the spelling
`V.toScheme` of the subspace, which instance resolution does not unfold to
`Stacks.Topology.openSubspace V`. -/
instance imF_isContinuous_toScheme (X : Scheme.{u}) (V : X.Opens) :
    (TopCat.Presheaf.imF (V : Opens (X : TopCat))).IsContinuous
      (Opens.grothendieckTopology (V.toScheme : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) :=
  ExtensionByZeroModules.imF_isContinuous _

/-- Taking the image in `X` of an open of `V` and then its preimage in `U` is continuous for the
topologies of opens. -/
instance imF_comp_mapι_isContinuous (X : Scheme.{u}) (U V : X.Opens) :
    (TopCat.Presheaf.imF (V : Opens (X : TopCat)) ⋙ Opens.map U.ι.base).IsContinuous
      (Opens.grothendieckTopology (V.toScheme : TopCat))
      (Opens.grothendieckTopology (U.toScheme : TopCat)) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology (X : TopCat)) _

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)
  {U V : X.Opens} (h : U ≤ V) (hU : IsInCharacteristic U.toScheme p)
  (hV : IsInCharacteristic V.toScheme p)

/-- For `U ≤ V`, an open of `V` has the same preimage in `U` whether one takes it along the
inclusion `U ⟶ V` of open subschemes or along its image in `X`. -/
theorem homOfLE_preimage_eq_imF_comp_mapι (A : Opens ((V.toScheme : TopCat))) :
    (Opens.map (X.homOfLE h).base).obj A =
      (TopCat.Presheaf.imF (V : Opens (X : TopCat)) ⋙ Opens.map U.ι.base).obj A := by
  refine le_antisymm (fun x hx => ⟨X.homOfLE h x, hx, X.homOfLE_apply h x⟩) ?_
  rintro x ⟨y, hy, hxy⟩
  obtain rfl : y = X.homOfLE h x := Subtype.ext (hxy.trans (X.homOfLE_apply h x).symm)
  exact hy

/-- **The two presentations of the site functor of a nested pair of opens agree.** Taking the
preimage along the inclusion `U ⟶ V` of open subschemes is taking the image in `X` and then the
preimage in `U`. Naturality is automatic: a category of opens is thin. -/
def nestedOpenSiteIso : Opens.map (X.homOfLE h).base ≅
    TopCat.Presheaf.imF (V : Opens (X : TopCat)) ⋙ Opens.map U.ι.base :=
  NatIso.ofComponents (fun A => eqToIso (homOfLE_preimage_eq_imF_comp_mapι X h A))
    (fun _ => Subsingleton.elim _ _)

/-- In a thin category, the images under a presheaf of two composable morphisms compose to the
image of any morphism with the same source and target. -/
private theorem presheaf_map_op_comp_eq {C D : Type*} [Category C] [Category D]
    (P : Cᵒᵖ ⥤ D) {a b c : C} (f : a ⟶ b) (g : b ⟶ c) (k : a ⟶ c) [Subsingleton (a ⟶ c)] :
    P.map g.op ≫ P.map f.op = P.map k.op :=
  (P.map_comp _ _).symm.trans (congrArg (fun k => P.map (Quiver.Hom.op k)) (Subsingleton.elim _ _))

/-- **The nested-opens compatibility of the comorphisms of the structure sheaf.** For `U ≤ V`,
the comorphism of the inclusion `U ⟶ V` of open subschemes, read through
`AlgebraicGeometry.nestedOpenSiteIso`, is the restriction to `V` of the comorphism of the
inclusion `U.ι` of `U` into `X`.

Both sides send a section of `𝒪_X` over the image of an open `A` of `V` to its restriction to
the image of the preimage of `A` in `U`, so both are `X.presheaf.map` of a morphism of opens of
`X`; the two morphisms of opens agree because a hom set of opens is a subsingleton. -/
theorem homOfLE_ringSheafOnOpensHom_comp_natTrans :
    (X.homOfLE h).ringSheafOnOpensHom ≫
        (@Functor.sheafPushforwardContinuousNatTrans _ _ _ _ _ _ (nestedOpenSiteIso X h).inv
          RingCat.{u} _
          (Opens.grothendieckTopology (V.toScheme : TopCat))
          (Opens.grothendieckTopology (U.toScheme : TopCat))
          (imF_comp_mapι_isContinuous X U V) inferInstance).app
            U.toScheme.ringSheafOnOpens =
      ((TopCat.Presheaf.imF (V : Opens (X : TopCat))).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology (V.toScheme : TopCat))
          (Opens.grothendieckTopology (X : TopCat))).map U.ι.ringSheafOnOpensHom := by
  apply Sheaf.hom_ext
  ext A : 2
  show (Scheme.Hom.ringSheafOnOpensHom (X.homOfLE h)).hom.app A ≫
      U.toScheme.ringSheafOnOpens.obj.map ((nestedOpenSiteIso X h).inv.app A.unop).op =
    (Scheme.Hom.ringSheafOnOpensHom U.ι).hom.app
      (op ((TopCat.Presheaf.imF (V : Opens (X : TopCat))).obj A.unop))
  have hmath : (X.homOfLE h).app A.unop ≫
        X.presheaf.map ((Scheme.Hom.opensFunctor U.ι).map
          ((nestedOpenSiteIso X h).inv.app A.unop)).op =
      U.ι.app ((TopCat.Presheaf.imF (V : Opens (X : TopCat))).obj A.unop) :=
    (congrArg (fun t => t ≫ X.presheaf.map ((Scheme.Hom.opensFunctor U.ι).map
          ((nestedOpenSiteIso X h).inv.app A.unop)).op)
        (Scheme.homOfLE_app (X := X) h A.unop)).trans
      (presheaf_map_op_comp_eq X.presheaf _ _ _)
  have e1 : (Scheme.Hom.ringSheafOnOpensHom (X.homOfLE h)).hom.app A =
      (forget₂ CommRingCat RingCat.{u}).map ((X.homOfLE h).app A.unop) := rfl
  have e2 : (Scheme.Hom.ringSheafOnOpensHom U.ι).hom.app
        (op ((TopCat.Presheaf.imF (V : Opens (X : TopCat))).obj A.unop)) =
      (forget₂ CommRingCat RingCat.{u}).map
        (U.ι.app ((TopCat.Presheaf.imF (V : Opens (X : TopCat))).obj A.unop)) := rfl
  have e3 : U.toScheme.ringSheafOnOpens.obj.map
        ((nestedOpenSiteIso X h).inv.app A.unop).op =
      (forget₂ CommRingCat RingCat.{u}).map
        (X.presheaf.map ((Scheme.Hom.opensFunctor U.ι).map
          ((nestedOpenSiteIso X h).inv.app A.unop)).op) :=
    rfl
  exact e1 ▸ e2 ▸ e3 ▸
    (((forget₂ CommRingCat RingCat.{u}).map_comp _ _).symm.trans
      (congrArg (forget₂ CommRingCat RingCat.{u}).map hmath))

/-- **The nested-opens compatibility of
`AlgebraicGeometry.frobeniusColimitRingSheafRestrictIso`.** For `U ≤ V`, the canonical morphism
`colim_F 𝒪_V ⟶ (colim_F 𝒪_U)` of the inclusion `U ⟶ V` of open subschemes, read through
`AlgebraicGeometry.nestedOpenSiteIso`, is the restriction to `V` of the canonical morphism of
the inclusion `U.ι`, conjugated by the identification of `colim_F 𝒪_V` with the restriction of
`colim_F 𝒪_X` to `V`.

Both sides are morphisms out of the sequential colimit `colim_F 𝒪_V`, so neither can be checked
on sections; `CategoryTheory.Limits.endoColimit_hom_ext` reduces the statement to its stagewise
content, which is
`AlgebraicGeometry.homOfLE_ringSheafOnOpensHom_comp_natTrans` for the structure sheaves. -/
theorem nested_restrictIso_compat :
    frobeniusColimitStructureSheafHom p (X.homOfLE h) hU hV ≫
        (@Functor.sheafPushforwardContinuousNatTrans _ _ _ _ _ _ (nestedOpenSiteIso X h).inv
          RingCat.{u} _
          (Opens.grothendieckTopology (V.toScheme : TopCat))
          (Opens.grothendieckTopology (U.toScheme : TopCat))
          (imF_comp_mapι_isContinuous X U V) inferInstance).app
            (frobeniusColimitRingSheaf U.toScheme p hU) =
      (frobeniusColimitRingSheafRestrictIso X p hX V hV).inv ≫
        ((TopCat.Presheaf.imF (V : Opens (X : TopCat))).sheafPushforwardContinuous RingCat.{u}
            (Opens.grothendieckTopology (V.toScheme : TopCat))
            (Opens.grothendieckTopology (X : TopCat))).map
          (frobeniusColimitStructureSheafHom p U.ι hU hX) := by
  refine endoColimit_hom_ext (frobeniusRingSheafOnOpensHom V.toScheme p hV) fun n => ?_
  have hr : frobeniusColimitι V.toScheme p hV n ≫
      (frobeniusColimitRingSheafRestrictIso X p hX V hV).inv =
      ((TopCat.Presheaf.imF (V : Opens (X : TopCat))).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (V.toScheme : TopCat))
        (Opens.grothendieckTopology (X : TopCat))).map (frobeniusColimitι X p hX n) :=
    (Iso.comp_inv_eq _).mpr
      (frobeniusColimitι_comp_frobeniusColimitRingSheafRestrictIso_hom X p hX V hV n).symm
  have hnat := (@Functor.sheafPushforwardContinuousNatTrans _ _ _ _ _ _
      (nestedOpenSiteIso X h).inv RingCat.{u} _
      (Opens.grothendieckTopology (V.toScheme : TopCat))
      (Opens.grothendieckTopology (U.toScheme : TopCat))
      (imF_comp_mapι_isContinuous X U V) inferInstance).naturality
    (frobeniusColimitι U.toScheme p hU n)
  exact
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ _)
          (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p (X.homOfLE h)
            hU hV n)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => _ ≫ t) hnat).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun t => t ≫ _)
                (homOfLE_ringSheafOnOpensHom_comp_natTrans X h))))))).trans
      (((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ _) hr).trans
          (((Functor.map_comp _ _ _).symm.trans
              (congrArg _ (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p U.ι
                hU hX n))).trans
            (Functor.map_comp _ _ _)))).symm)


/-! ### The nested restriction functor and its adjunction -/

/-- Taking the image in `V` of an open of `U` is continuous for the topologies of opens. -/
instance homOfLE_isOpenMap_functor_isContinuous :
    (Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.functor.IsContinuous
      (Opens.grothendieckTopology (U.toScheme : TopCat))
      (Opens.grothendieckTopology (V.toScheme : TopCat)) :=
  (Scheme.Hom.isOpenEmbedding (X.homOfLE h)).functor_isContinuous

/-- For `U ≤ V`, an open of `U` has the same image in `X` whether one takes it directly or
through `V`. This is the companion on images of
`AlgebraicGeometry.homOfLE_preimage_eq_imF_comp_mapι`, which is the statement on preimages. -/
theorem imF_homOfLE_image_eq (A : Opens (U.toScheme : TopCat)) :
    (TopCat.Presheaf.imF (V : Opens (X : TopCat))).obj
        ((Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.functor.obj A) =
      (TopCat.Presheaf.imF (U : Opens (X : TopCat))).obj A := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨y, ⟨z, hz, hzy⟩, hyx⟩ := hx
    subst hzy
    refine ⟨z, hz, ?_⟩
    rw [← hyx]
    exact (X.homOfLE_apply h z).symm
  · obtain ⟨z, hz, hzx⟩ := hx
    refine ⟨X.homOfLE h z, ⟨z, hz, rfl⟩, ?_⟩
    rw [← hzx]
    exact X.homOfLE_apply h z

/-- **The comparison of the two ways of restricting a sheaf of rings on `X` to `U`**, for
`U ≤ V`: restricting directly, or restricting to `V` and then to `U`. Over an open `A` of `U` it
is the restriction map of `P` along the equality of opens of
`AlgebraicGeometry.imF_homOfLE_image_eq`; naturality is automatic because a category of opens is
thin.

This is the morphism `σ` that
`AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunctionOfIso` consumes at the inclusion of a
nested pair of opens. It is written out by hand rather than obtained from
`CategoryTheory.Functor.sheafPushforwardContinuousIso` for the composite of the two image
functors, because the composite's continuity is not available: the middle site is spelled
`Opens ↥(V.toScheme)` on one side and `Opens ↥V` on the other, the two agree only at default
transparency, and instance resolution does not unfold either into the other. At a fixed sheaf of
rings there is no composite to be continuous. -/
noncomputable def nestedOpenRingPushMap
    (P : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}) :
    ((TopCat.Presheaf.imF (U : Opens (X : TopCat))).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (U.toScheme : TopCat))
        (Opens.grothendieckTopology (X : TopCat))).obj P ⟶
      ((Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.functor.sheafPushforwardContinuous
          RingCat.{u} (Opens.grothendieckTopology (U.toScheme : TopCat))
          (Opens.grothendieckTopology (V.toScheme : TopCat))).obj
        (((TopCat.Presheaf.imF (V : Opens (X : TopCat))).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology (V.toScheme : TopCat))
          (Opens.grothendieckTopology (X : TopCat))).obj P) :=
  ⟨{ app := fun A => P.obj.map (eqToHom (imF_homOfLE_image_eq X h A.unop)).op,
     naturality := fun _ _ _ =>
       ((P.obj.map_comp _ _).symm.trans
         (congrArg (fun k => P.obj.map k) (Subsingleton.elim _ _))).trans
           (P.obj.map_comp _ _) }⟩

/-- **The comparison of the two restrictions is invertible.** Its inverse is the restriction map
along the same equality of opens read backwards, and both composites are `P.map` of a morphism of
opens from an open to itself, hence of the identity. -/
noncomputable def nestedOpenRingPushIso
    (P : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}) :
    ((TopCat.Presheaf.imF (U : Opens (X : TopCat))).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (U.toScheme : TopCat))
        (Opens.grothendieckTopology (X : TopCat))).obj P ≅
      ((Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.functor.sheafPushforwardContinuous
          RingCat.{u} (Opens.grothendieckTopology (U.toScheme : TopCat))
          (Opens.grothendieckTopology (V.toScheme : TopCat))).obj
        (((TopCat.Presheaf.imF (V : Opens (X : TopCat))).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology (V.toScheme : TopCat))
          (Opens.grothendieckTopology (X : TopCat))).obj P) where
  hom := nestedOpenRingPushMap X h P
  inv :=
    ⟨{ app := fun A => P.obj.map (eqToHom (imF_homOfLE_image_eq X h A.unop).symm).op,
       naturality := fun _ _ _ =>
         ((P.obj.map_comp _ _).symm.trans
           (congrArg (fun k => P.obj.map k) (Subsingleton.elim _ _))).trans
             (P.obj.map_comp _ _) }⟩
  hom_inv_id :=
    Sheaf.hom_ext (NatTrans.ext (funext fun _ =>
      ((P.obj.map_comp _ _).symm.trans
        (congrArg (fun k => P.obj.map k) (Subsingleton.elim _ (𝟙 _)))).trans
          (P.obj.map_id _)))
  inv_hom_id :=
    Sheaf.hom_ext (NatTrans.ext (funext fun _ =>
      ((P.obj.map_comp _ _).symm.trans
        (congrArg (fun k => P.obj.map k) (Subsingleton.elim _ (𝟙 _)))).trans
          (P.obj.map_id _)))

/-- **The comparison of the two restrictions is natural in the sheaf of rings.** This is the
content the stage compatibility of the nested restriction identification consumes: it is applied
at the stage coprojection `𝒪_X ⟶ colim_F 𝒪_X`, which is a morphism of sheaves of rings on `X`
and not a restriction map. -/
theorem nestedOpenRingPushMap_naturality
    {P Q : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}} (t : P ⟶ Q) :
    ((TopCat.Presheaf.imF (U : Opens (X : TopCat))).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology (U.toScheme : TopCat))
          (Opens.grothendieckTopology (X : TopCat))).map t ≫ nestedOpenRingPushMap X h Q =
      nestedOpenRingPushMap X h P ≫
        ((Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.functor.sheafPushforwardContinuous
          RingCat.{u} (Opens.grothendieckTopology (U.toScheme : TopCat))
          (Opens.grothendieckTopology (V.toScheme : TopCat))).map
          (((TopCat.Presheaf.imF (V : Opens (X : TopCat))).sheafPushforwardContinuous RingCat.{u}
            (Opens.grothendieckTopology (V.toScheme : TopCat))
            (Opens.grothendieckTopology (X : TopCat))).map t) :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ => (t.hom.naturality _).symm))

/-- **The comorphism of the inclusion `U ⟶ V` of open subschemes is the counit of the
image/preimage adjunction of that inclusion, read on `𝒪_V` and corrected by the comparison of the
two restrictions.**

This is the hypothesis `hstruct` of
`AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunctionOfIso` at the inclusion of a nested pair
of opens; for the open immersion `V.ι` the corresponding statement needs no correction and holds
by `rfl`.

Both sides send a section of `𝒪_X` over the image of an open `A` of `V` to its restriction to the
image of the preimage of `A` in `U`, so both are `X.presheaf.map` of a morphism of opens of `X`;
the two morphisms of opens agree because a hom set of opens is a subsingleton. -/
theorem homOfLE_counit_whiskerRight_eq :
    Functor.whiskerRight (NatTrans.op
        (Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.adjunction.counit)
        V.toScheme.ringSheafOnOpens.obj =
      (X.homOfLE h).ringSheafOnOpensHom.hom ≫
        (Opens.map (X.homOfLE h).base).op.whiskerLeft
          (nestedOpenRingPushMap X h X.ringSheafOnOpens).hom := by
  refine NatTrans.ext (funext fun A => ?_)
  have hmath : (X.homOfLE h).app A.unop ≫
        X.presheaf.map (eqToHom (imF_homOfLE_image_eq X h
          ((Opens.map (X.homOfLE h).base).obj A.unop))).op =
      X.presheaf.map ((TopCat.Presheaf.imF (V : Opens (X : TopCat))).map
        ((Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.adjunction.counit.app A.unop)).op :=
    (congrArg (fun t => t ≫ X.presheaf.map (eqToHom (imF_homOfLE_image_eq X h
          ((Opens.map (X.homOfLE h).base).obj A.unop))).op)
        (Scheme.homOfLE_app (X := X) h A.unop)).trans
      (presheaf_map_op_comp_eq X.presheaf _ _ _)
  exact (congrArg (forget₂ CommRingCat RingCat.{u}).map hmath).symm.trans
    ((forget₂ CommRingCat RingCat.{u}).map_comp _ _)

/-- **`colim_F 𝒪_V` restricted to the smaller open `U` is `colim_F 𝒪_U`.** This is the
nested-opens form of `AlgebraicGeometry.frobeniusColimitRingSheafRestrictIso`: it identifies
`colim_F 𝒪_U` with the restriction to `U` of `colim_F 𝒪_V`, where both opens are opens of an
ambient `X` and `U ≤ V`.

It is the restriction identification at `U` and at `V`, glued by
`AlgebraicGeometry.nestedOpenRingPushIso`; no new Frobenius content enters. -/
noncomputable def frobeniusColimitRingSheafNestedRestrictIso :
    frobeniusColimitRingSheaf U.toScheme p hU ≅
      ((Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.functor.sheafPushforwardContinuous
        RingCat.{u} (Opens.grothendieckTopology (U.toScheme : TopCat))
        (Opens.grothendieckTopology (V.toScheme : TopCat))).obj
        (frobeniusColimitRingSheaf V.toScheme p hV) := by
  refine Iso.trans (frobeniusColimitRingSheafRestrictIso X p hX U hU).symm
    (Iso.trans (nestedOpenRingPushIso X h (frobeniusColimitRingSheaf X p hX)) ?_)
  exact ((Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.functor.sheafPushforwardContinuous
    RingCat.{u} (Opens.grothendieckTopology (U.toScheme : TopCat))
    (Opens.grothendieckTopology (V.toScheme : TopCat))).mapIso
      (frobeniusColimitRingSheafRestrictIso X p hX V hV)

/-- The three factors of
`AlgebraicGeometry.frobeniusColimitRingSheafNestedRestrictIso`, named so that a computation with
it need not unfold the `CategoryTheory.Iso.trans`. -/
theorem frobeniusColimitRingSheafNestedRestrictIso_hom :
    (frobeniusColimitRingSheafNestedRestrictIso X p hX h hU hV).hom =
      (frobeniusColimitRingSheafRestrictIso X p hX U hU).inv ≫
        nestedOpenRingPushMap X h (frobeniusColimitRingSheaf X p hX) ≫
          ((Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.functor.sheafPushforwardContinuous
            RingCat.{u} (Opens.grothendieckTopology (U.toScheme : TopCat))
            (Opens.grothendieckTopology (V.toScheme : TopCat))).map
            (frobeniusColimitRingSheafRestrictIso X p hX V hV).hom :=
  rfl

/-- **The nested-opens restriction identification is compatible with the stage
coprojections.** Restricting the stage-`n` coprojection of `colim_F 𝒪_V` to `U` and transporting
along `AlgebraicGeometry.frobeniusColimitRingSheafNestedRestrictIso` gives the stage-`n`
coprojection of `colim_F 𝒪_U`, corrected by the comparison of the two restrictions.

This is the hypothesis `hk` of
`AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunctionOfIso` at the inclusion of a nested pair
of opens.  It is proved from the single-open compatibility
`AlgebraicGeometry.frobeniusColimitι_comp_frobeniusColimitRingSheafRestrictIso_hom` at `U` and at
`V`, and naturality of `AlgebraicGeometry.nestedOpenRingPushMap` at the stage coprojection of
`colim_F 𝒪_X`.

**The proof is in term mode.** The goal mentions the site of `U` in the spelling
`Opens ↥(U.toScheme)`, which `AlgebraicGeometry.nestedOpenRingPushMap` carries, and in the
spelling `Opens ↥U` that the image functor of `U.ι` carries; the two agree only at default
transparency, so the goal is not type-correct at the transparency a rewrite motive is built at
and `rw` fails on it. Composition of equalities is checked at default transparency. -/
theorem nestedOpenRingPushMap_comp_frobeniusColimitι (n : ℕ) :
    nestedOpenRingPushMap X h X.ringSheafOnOpens ≫
        ((Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.functor.sheafPushforwardContinuous
          RingCat.{u} (Opens.grothendieckTopology (U.toScheme : TopCat))
          (Opens.grothendieckTopology (V.toScheme : TopCat))).map
          (frobeniusColimitι V.toScheme p hV n) =
      frobeniusColimitι U.toScheme p hU n ≫
        (frobeniusColimitRingSheafNestedRestrictIso X p hX h hU hV).hom := by
  let G := (Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.functor.sheafPushforwardContinuous
    RingCat.{u} (Opens.grothendieckTopology (U.toScheme : TopCat))
    (Opens.grothendieckTopology (V.toScheme : TopCat))
  let α := (frobeniusColimitRingSheafRestrictIso X p hX V hV).hom
  let s₀ := nestedOpenRingPushMap X h X.ringSheafOnOpens
  let s₁ := nestedOpenRingPushMap X h (frobeniusColimitRingSheaf X p hX)
  exact (congrArg (fun t => s₀ ≫ G.map t)
      (frobeniusColimitι_comp_frobeniusColimitRingSheafRestrictIso_hom X p hX V hV n).symm).trans
    ((congrArg (fun t => s₀ ≫ t) (Functor.map_comp G _ _)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ G.map α)
            (nestedOpenRingPushMap_naturality X h (frobeniusColimitι X p hX n)).symm).trans
          ((congrArg (fun t => (t ≫ s₁) ≫ G.map α)
              ((Iso.comp_inv_eq _).mpr
                (frobeniusColimitι_comp_frobeniusColimitRingSheafRestrictIso_hom
                  X p hX U hU n).symm).symm).trans
            ((congrArg (fun t => t ≫ G.map α) (Category.assoc _ _ _)).trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun t => frobeniusColimitι U.toScheme p hU n ≫ t)
                  (Category.assoc _ _ _))))))))

/-- **Restriction of a sheaf of modules over `colim_F 𝒪_V` to the smaller open `U`**, realised as
pushforward along the image functor of the inclusion `U ⟶ V` of open subschemes, with
`AlgebraicGeometry.frobeniusColimitRingSheafNestedRestrictIso` as its morphism of sheaves of
rings.  This is the nested-opens form of
`AlgebraicGeometry.frobeniusColimitSiteRestrict`. -/
noncomputable def frobeniusColimitNestedSiteRestrict :
    _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf V.toScheme p hV) ⥤
      _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf U.toScheme p hU) :=
  _root_.SheafOfModules.pushforward.{u}
    (frobeniusColimitRingSheafNestedRestrictIso X p hX h hU hV).hom

/-- **Restriction to a smaller open is left adjoint to pushforward along the inclusion of open
subschemes**, for the Frobenius colimits of the structure sheaves.

This is `AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunctionOfIso` at the inclusion
`X.homOfLE h` and the image/preimage adjunction of that inclusion, its two inputs being
`AlgebraicGeometry.homOfLE_counit_whiskerRight_eq` and
`AlgebraicGeometry.nestedOpenRingPushMap_comp_frobeniusColimitι`.  Nothing of the single-open
adjunction is re-derived: the generality of the upstream statement is what makes this an
instantiation. -/
noncomputable def frobeniusColimitNestedSiteRestrictAdjunction :
    frobeniusColimitNestedSiteRestrict X p hX h hU hV ⊣
      _root_.SheafOfModules.pushforward.{u}
        (frobeniusColimitStructureSheafHom p (X.homOfLE h) hU hV) :=
  frobeniusColimitSiteRestrictAdjunctionOfIso p (X.homOfLE h) hU hV
    (Scheme.Hom.isOpenEmbedding (X.homOfLE h)).isOpenMap.adjunction
    (nestedOpenRingPushMap X h X.ringSheafOnOpens)
    (frobeniusColimitRingSheafNestedRestrictIso X p hX h hU hV)
    (homOfLE_counit_whiskerRight_eq X h)
    (nestedOpenRingPushMap_comp_frobeniusColimitι X p hX h hU hV)

/-- **The transition functor of [Stacks, Tag 0EXE] along the inclusion of a nested pair of opens
is restriction to the smaller open.**  This is the nested-opens form of
`AlgebraicGeometry.frobeniusColimitSiteRestrictIsoPullback`, by uniqueness of a left adjoint. -/
noncomputable def frobeniusColimitNestedSiteRestrictIsoPullback :
    frobeniusColimitNestedSiteRestrict X p hX h hU hV ≅
      _root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p (X.homOfLE h) hU hV) :=
  (frobeniusColimitNestedSiteRestrictAdjunction X p hX h hU hV).leftAdjointUniq
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} _)

end AlgebraicGeometry

end
