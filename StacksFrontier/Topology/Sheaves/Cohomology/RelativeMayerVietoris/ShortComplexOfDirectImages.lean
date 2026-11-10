module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Mayer--Vietoris short complex of direct-image functors

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `iU : U ⟶ X`, `iV : V ⟶ X` and
`iW : W ⟶ X` be open immersions with the image of `iW` contained in those of `iU` and `iV`.
Writing `a = iU ≫ f`, `b = iV ≫ f` and `c = iW ≫ f`, this file builds the short complex of
functors

`f_* ⟶ (a_* ∘ iU^*) ⊞ (b_* ∘ iV^*) ⟶ c_* ∘ iW^*`

of the relative Mayer--Vietoris sequence of Stacks 01EC, and computes its maps on sections.

## Main definitions

* `Stacks.Cohomology.RelativeMayerVietoris.mvToOpen`: for a single open immersion `i : Z ⟶ X`,
  the natural map `f_* ⟶ (i ≫ f)_* ∘ i^*` restricting a section to the open subspace.
* `Stacks.Cohomology.RelativeMayerVietoris.mvToCover`: the pair of those maps for `iU` and `iV`,
  landing in the biproduct.
* `Stacks.Cohomology.RelativeMayerVietoris.mvToIntersection`: the difference of the two further
  restrictions to the intersection.
* `Stacks.Cohomology.RelativeMayerVietoris.immRestrict`: restriction of sheaves of modules
  along an open immersion of ringed spaces, as a pushforward along the image functor on opens.
* `Stacks.Cohomology.RelativeMayerVietoris.immRestrictAdjunction`: `immRestrict i` is left
  adjoint to `i_*`.
* `Stacks.Cohomology.RelativeMayerVietoris.immRestrictIsoPullback`: the isomorphism of
  `immRestrict i` with the pullback `i^*`.

## Main results

* `Stacks.Cohomology.RelativeMayerVietoris.unit_comp_restrictMonadMap`: restricting to `U` and
  then to a subspace `W ⟶ U` is restricting to `W`.
* `Stacks.Cohomology.RelativeMayerVietoris.mvZero`: `mvToCover ≫ mvToIntersection = 0`.
* `Stacks.Cohomology.RelativeMayerVietoris.immRestrictAdjunction_unit_app_val_app`: the unit of
  `immRestrict i ⊣ i_*` is, on sections over an open `S` of `X`, the restriction map
  `M(S) ⟶ M(i(i⁻¹S))`.
* `Stacks.Cohomology.RelativeMayerVietoris.mvToOpen_eq`: `mvToOpen f i` is `mvToOpenModel f i`,
  the restriction map on sections pushed forward along `f`, followed by an isomorphism.

## References

* [Stacks Project, Tag 01EC](https://stacks.math.columbia.edu/tag/01EC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.RelativeMayerVietoris

variable {X Y Z U V W : RingedSpace.{u, u}}

/-- The pushforward of a composite of morphisms of ringed spaces is the composite of the
pushforwards. -/
@[ega "0 4.2.6"]
def pushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforward (f ≫ g) ≅ modulePushforward f ⋙ modulePushforward g :=
  pushforwardComp f g

/-- The pullback of a composite of morphisms of ringed spaces is the composite of the pullbacks,
in the reverse order. -/
def pullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback (f ≫ g) ≅ modulePullback g ⋙ modulePullback f :=
  pullbackComp f g

/-- The endofunctor `i^* ⋙ i_*` of `Mod(𝒪_X)` attached to a morphism `i : Z ⟶ X` of ringed
spaces, the monad of the adjunction `i^* ⊣ i_*`. -/
abbrev restrictMonad (i : Z ⟶ X) :
    SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing X) :=
  modulePullback i ⋙ modulePushforward i

/-- Restriction from an open subspace to a smaller one, as a map of the associated monads
`iU^* ⋙ (iU)_* ⟶ (g ≫ iU)^* ⋙ (g ≫ iU)_*`, given by the unit of `g^* ⊣ g_*`. -/
def restrictMonadMap (iU : U ⟶ X) (g : W ⟶ U) :
    restrictMonad iU ⟶ restrictMonad (g ≫ iU) :=
  Functor.whiskerLeft (modulePullback iU)
      (Functor.whiskerRight (modulePullbackPushforwardAdjunction g).unit
        (modulePushforward iU)) ≫
    Functor.whiskerRight (pullbackCompIso g iU).inv
      (modulePushforward g ⋙ modulePushforward iU) ≫
    Functor.whiskerLeft (modulePullback (g ≫ iU)) (pushforwardCompIso g iU).inv

/-- Restricting to the open subspace `U` and then further to `W` is restricting to `W`:
the unit of `iU^* ⊣ (iU)_*` followed by `restrictMonadMap iU g` is the unit of
`(g ≫ iU)^* ⊣ (g ≫ iU)_*`. -/
lemma unit_comp_restrictMonadMap (iU : U ⟶ X) (g : W ⟶ U) :
    (modulePullbackPushforwardAdjunction iU).unit ≫ restrictMonadMap iU g =
      (modulePullbackPushforwardAdjunction (g ≫ iU)).unit := by
  have hunit : (((modulePullbackPushforwardAdjunction iU).comp
        (modulePullbackPushforwardAdjunction g)).ofNatIsoRight
          (pushforwardCompIso g iU).symm).unit =
      ((modulePullbackPushforwardAdjunction iU).unit ≫
        Functor.whiskerLeft (modulePullback iU)
          (Functor.whiskerRight (modulePullbackPushforwardAdjunction g).unit
            (modulePushforward iU))) ≫
      Functor.whiskerLeft (modulePullback iU ⋙ modulePullback g)
        (pushforwardCompIso g iU).inv := by
    rw [Adjunction.ofNatIsoRight_unit]
    ext M
    simp [Adjunction.comp_unit_app]
  have key : (modulePullbackPushforwardAdjunction (g ≫ iU)).unit ≫
      Functor.whiskerRight (pullbackCompIso g iU).hom (modulePushforward (g ≫ iU)) =
      (((modulePullbackPushforwardAdjunction iU).comp
        (modulePullbackPushforwardAdjunction g)).ofNatIsoRight
          (pushforwardCompIso g iU).symm).unit :=
    Adjunction.unit_leftAdjointUniq_hom _ _
  dsimp only [restrictMonadMap]
  rw [← Functor.whiskerLeft_comp_whiskerRight]
  simp only [← Category.assoc]
  rw [← hunit, ← key, Category.assoc, ← Functor.whiskerRight_comp, Iso.hom_inv_id,
    Functor.whiskerRight_id', Category.comp_id]

/-- The monad `i^* ⋙ i_*` followed by `f_*` is the direct image along `i ≫ f` of the
restriction to the open subspace. -/
def restrictPushforwardIso (f : X ⟶ Y) (i : Z ⟶ X) :
    restrictMonad i ⋙ modulePushforward f ≅
      modulePullback i ⋙ modulePushforward (i ≫ f) :=
  Functor.isoWhiskerLeft (modulePullback i) (pushforwardCompIso i f).symm

/-- Restriction of a direct image to an open subspace of the source:
`f_* M ⟶ (i ≫ f)_* (i^* M)`, naturally in `M`, given by the unit of `i^* ⊣ i_*` pushed
forward along `f`. -/
def mvToOpen (f : X ⟶ Y) (i : Z ⟶ X) :
    modulePushforward f ⟶ modulePullback i ⋙ modulePushforward (i ≫ f) :=
  Functor.whiskerRight (modulePullbackPushforwardAdjunction i).unit (modulePushforward f) ≫
    (restrictPushforwardIso f i).hom

/-- `mvToOpen f i` followed by the inverse of `restrictPushforwardIso f i` is the unit of
`i^* ⊣ i_*` pushed forward along `f`. -/
lemma mvToOpen_comp_restrictPushforwardIso_inv (f : X ⟶ Y) (i : Z ⟶ X) :
    mvToOpen f i ≫ (restrictPushforwardIso f i).inv =
      Functor.whiskerRight (modulePullbackPushforwardAdjunction i).unit
        (modulePushforward f) := by
  dsimp only [mvToOpen]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Further restriction of a direct image, from the open subspace `U` to a subspace
`g : W ⟶ U` of it, stated for the composite `g ≫ iU`. -/
def restrictStep' (f : X ⟶ Y) (iU : U ⟶ X) (g : W ⟶ U) :
    modulePullback iU ⋙ modulePushforward (iU ≫ f) ⟶
      modulePullback (g ≫ iU) ⋙ modulePushforward ((g ≫ iU) ≫ f) :=
  (restrictPushforwardIso f iU).inv ≫
    Functor.whiskerRight (restrictMonadMap iU g) (modulePushforward f) ≫
    (restrictPushforwardIso f (g ≫ iU)).hom

/-- Restricting a direct image to `U` and then to `W` is restricting it to `W`. -/
lemma mvToOpen_comp_restrictStep' (f : X ⟶ Y) (iU : U ⟶ X) (g : W ⟶ U) :
    mvToOpen f iU ≫ restrictStep' f iU g = mvToOpen f (g ≫ iU) := by
  dsimp only [restrictStep']
  rw [← Category.assoc, ← Category.assoc, mvToOpen_comp_restrictPushforwardIso_inv,
    ← Functor.whiskerRight_comp, unit_comp_restrictMonadMap]
  rfl

/-- Further restriction of a direct image along a chosen factorisation `g` of the smaller open
immersion `iW` through the larger one `iU`. -/
def restrictStep (f : X ⟶ Y) (iU : U ⟶ X) (iW : W ⟶ X) (g : W ⟶ U) (hg : g ≫ iU = iW) :
    modulePullback iU ⋙ modulePushforward (iU ≫ f) ⟶
      modulePullback iW ⋙ modulePushforward (iW ≫ f) := by
  subst hg; exact restrictStep' f iU g

/-- Restricting a direct image to `U` and then, along a factorisation of `iW` through `iU`, to
`W` is restricting it to `W`. -/
lemma mvToOpen_comp_restrictStep (f : X ⟶ Y) (iU : U ⟶ X) (iW : W ⟶ X) (g : W ⟶ U)
    (hg : g ≫ iU = iW) : mvToOpen f iU ≫ restrictStep f iU iW g hg = mvToOpen f iW := by
  subst hg; exact mvToOpen_comp_restrictStep' f iU g

/-- The factorisation of a morphism of ringed spaces through an open immersion whose image
contains its image. -/
def factorThrough (iU : U ⟶ X) (iW : W ⟶ X) [SheafedSpace.IsOpenImmersion iU]
    (h : Set.range iW.hom.base ⊆ Set.range iU.hom.base) : W ⟶ U :=
  (SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).preimage
    (PresheafedSpace.IsOpenImmersion.lift
      ((SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map iU)
      ((SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map iW) h)

/-- `factorThrough iU iW h` followed by `iU` is `iW`. -/
lemma factorThrough_comp (iU : U ⟶ X) (iW : W ⟶ X) [SheafedSpace.IsOpenImmersion iU]
    (h : Set.range iW.hom.base ⊆ Set.range iU.hom.base) :
    factorThrough iU iW h ≫ iU = iW := by
  apply (SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map_injective
  dsimp only [factorThrough]
  rw [Functor.map_comp, Functor.map_preimage]
  exact PresheafedSpace.IsOpenImmersion.lift_fac _ _ h

/-- The first map of the Mayer--Vietoris short complex: restriction of a direct image to the
two members of the cover, `f_* ⟶ (a_* ∘ iU^*) ⊞ (b_* ∘ iV^*)`. -/
def mvToCover (f : X ⟶ Y) (iU : U ⟶ X) (iV : V ⟶ X) :
    modulePushforward f ⟶
      (modulePullback iU ⋙ modulePushforward (iU ≫ f)) ⊞
        (modulePullback iV ⋙ modulePushforward (iV ≫ f)) :=
  biprod.lift (mvToOpen f iU) (mvToOpen f iV)

/-- The second map of the Mayer--Vietoris short complex: the difference of the two further
restrictions to the intersection, `(a_* ∘ iU^*) ⊞ (b_* ∘ iV^*) ⟶ c_* ∘ iW^*`. -/
def mvToIntersection (f : X ⟶ Y) (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)
    [SheafedSpace.IsOpenImmersion iU] [SheafedSpace.IsOpenImmersion iV]
    (hU : Set.range iW.hom.base ⊆ Set.range iU.hom.base)
    (hV : Set.range iW.hom.base ⊆ Set.range iV.hom.base) :
    (modulePullback iU ⋙ modulePushforward (iU ≫ f)) ⊞
        (modulePullback iV ⋙ modulePushforward (iV ≫ f)) ⟶
      modulePullback iW ⋙ modulePushforward (iW ≫ f) :=
  biprod.desc (restrictStep f iU iW (factorThrough iU iW hU) (factorThrough_comp iU iW hU))
    (-restrictStep f iV iW (factorThrough iV iW hV) (factorThrough_comp iV iW hV))

/-- The two maps of the Mayer--Vietoris short complex compose to zero. -/
lemma mvZero (f : X ⟶ Y) (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)
    [SheafedSpace.IsOpenImmersion iU] [SheafedSpace.IsOpenImmersion iV]
    (hU : Set.range iW.hom.base ⊆ Set.range iU.hom.base)
    (hV : Set.range iW.hom.base ⊆ Set.range iV.hom.base) :
    mvToCover f iU iV ≫ mvToIntersection f iU iV iW hU hV = 0 := by
  dsimp only [mvToCover, mvToIntersection]
  rw [biprod.lift_desc, Preadditive.comp_neg, mvToOpen_comp_restrictStep,
    mvToOpen_comp_restrictStep, add_neg_cancel]

/-! ### Restriction along an open immersion, with computable sections -/

section ImmRestrict

variable (i : Z ⟶ X) [H : SheafedSpace.IsOpenImmersion i]

/-- The image of an open immersion of ringed spaces, as an open subset of the target. -/
def immImage : Opens (X : TopCat) :=
  ⟨Set.range i.hom.base, H.base_open.isOpen_range⟩

/-- The functor `Opens Z ⥤ Opens X` taking the image under an open immersion `i : Z ⟶ X`. -/
noncomputable abbrev immOpensFunctor : Opens (Z : TopCat) ⥤ Opens (X : TopCat) :=
  SheafedSpace.IsOpenImmersion.opensFunctor i

/-- The image functor of an open immersion is continuous for the open-set topologies. -/
noncomputable instance immOpensFunctor_isContinuous : (immOpensFunctor i).IsContinuous
    (Opens.grothendieckTopology (Z : TopCat)) (Opens.grothendieckTopology (X : TopCat)) :=
  H.base_open.functor_isContinuous

/-- The adjunction between taking images and taking preimages of opens along an open
immersion. -/
noncomputable abbrev immOpensAdjunction : immOpensFunctor i ⊣ opensMap i :=
  H.base_open.isOpenMap.adjunction

/-- The image of the preimage of an open `S` of `X` is `S` intersected with the image of the
open immersion. -/
lemma immOpensFunctor_obj_map (S : Opens (X : TopCat)) :
    (immOpensFunctor i).obj ((opensMap i).obj S) = S ⊓ immImage i := by
  ext z
  simp [immImage, Set.mem_image, Set.mem_range]
  aesop

/-- `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.invApp`, the isomorphism
`𝒪_Z(W) ≅ 𝒪_X(i(W))`, as a morphism of presheaves of commutative rings. -/
noncomputable def invAppNatTrans : Z.presheaf ⟶ (immOpensFunctor i).op ⋙ X.presheaf where
  app W := SheafedSpace.IsOpenImmersion.invApp i W.unop
  naturality _ _ ι := SheafedSpace.IsOpenImmersion.inv_naturality i ι

/-- The comparison of structure sheaves along the image functor of an open immersion. -/
noncomputable def immStructureSheafHom : structureSheafRing Z ⟶
    ((immOpensFunctor i).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (Z : TopCat))
      (Opens.grothendieckTopology (X : TopCat))).obj (structureSheafRing X) :=
  ObjectProperty.homMk (Functor.whiskerRight (invAppNatTrans i) (forget₂ CommRingCat RingCat))

/-- Restriction of sheaves of modules along an open immersion `i : Z ⟶ X`, as pushforward
along the image functor on opens.  Its sections over an open `W` of `Z` are the sections of the
original over `i(W)`. -/
noncomputable def immRestrict :
    SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Z) :=
  SheafOfModules.pushforward (immStructureSheafHom i)

/-- Restricting a section of `𝒪_X` to `i(i⁻¹S)` is applying `i^♯` and then the comparison
`immStructureSheafHom i`. -/
lemma immCounitCondition :
    Functor.whiskerRight (NatTrans.op (immOpensAdjunction i).counit) (structureSheafRing X).obj =
      (structureSheafHom i).hom ≫
        (opensMap i).op.whiskerLeft (immStructureSheafHom i).hom := by
  refine NatTrans.ext (funext fun V => ?_)
  change (forget₂ CommRingCat.{u} RingCat.{u}).map
      (X.presheaf.map ((immOpensAdjunction i).counit.app V.unop).op) = _
  rw [show ((immOpensAdjunction i).counit.app V.unop).op =
    (homOfLE (Set.image_preimage_subset i.hom.base V.unop.1)).op from
      congrArg Quiver.Hom.op (Subsingleton.elim _ _),
    ← SheafedSpace.IsOpenImmersion.app_invApp i V.unop, Functor.map_comp]
  rfl

/-- The comparison `immStructureSheafHom i` followed by `i^♯` and the restriction along
`W ≤ i⁻¹(i(W))` is the identity of `𝒪_Z`. -/
lemma immUnitCondition :
    (immStructureSheafHom i).hom ≫
        (immOpensFunctor i).op.whiskerLeft (structureSheafHom i).hom ≫
      Functor.whiskerRight (NatTrans.op (immOpensAdjunction i).unit) (structureSheafRing Z).obj =
        𝟙 (structureSheafRing Z).obj := by
  refine NatTrans.ext (funext fun W => ?_)
  change (forget₂ CommRingCat.{u} RingCat.{u}).map
        (SheafedSpace.IsOpenImmersion.invApp i W.unop) ≫
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        (i.hom.c.app (op ((immOpensFunctor i).obj W.unop))) ≫
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        (Z.presheaf.map ((immOpensAdjunction i).unit.app W.unop).op) = _
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
    SheafedSpace.IsOpenImmersion.invApp_app, ← Functor.map_comp]
  exact (congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map
    ((congrArg Z.presheaf.map (Subsingleton.elim _ (𝟙 (op W.unop)))).trans
      (Z.presheaf.map_id _))).trans ((forget₂ CommRingCat.{u} RingCat.{u}).map_id _)

/-- Restriction along an open immersion is left adjoint to pushforward along it. -/
noncomputable def immRestrictAdjunction : immRestrict i ⊣ modulePushforward i :=
  SheafOfModules.pushforwardPushforwardAdj (immOpensAdjunction i) (immStructureSheafHom i)
    (structureSheafHom i) (immCounitCondition i) (immUnitCondition i)

/-- The unit of `immRestrict i ⊣ i_*` over an open `S` of `X` is the restriction map
`M(S) ⟶ M(i(i⁻¹S))`. -/
lemma immRestrictAdjunction_unit_app_val_app (M : SheafOfModules.{u} (structureSheafRing X))
    (S : (Opens (X : TopCat))ᵒᵖ) (x : M.val.obj S) :
    ((immRestrictAdjunction i).unit.app M).val.app S x =
      M.val.map ((immOpensAdjunction i).counit.app S.unop).op x :=
  rfl

/-- Restriction along an open immersion is isomorphic to the pullback along it. -/
noncomputable def immRestrictIsoPullback : immRestrict i ≅ modulePullback i :=
  (immRestrictAdjunction i).leftAdjointUniq (modulePullbackPushforwardAdjunction i)

/-- `immRestrictIsoPullback` carries the unit of `immRestrict i ⊣ i_*` to the unit of
`i^* ⊣ i_*`. -/
lemma unit_immRestrictIsoPullback :
    (immRestrictAdjunction i).unit ≫
        Functor.whiskerRight (immRestrictIsoPullback i).hom (modulePushforward i) =
      (modulePullbackPushforwardAdjunction i).unit :=
  Adjunction.unit_leftAdjointUniq_hom _ _

/-- Restriction along an open immersion is a right adjoint. -/
instance immRestrict_isRightAdjoint : (immRestrict i).IsRightAdjoint :=
  have : (PresheafOfModules.pushforward (immStructureSheafHom i).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  SheafOfModules.instIsRightAdjointPushforward (immStructureSheafHom i)

/-- Restriction along an open immersion preserves finite limits. -/
instance immRestrict_preservesFiniteLimits : PreservesFiniteLimits (immRestrict i) :=
  inferInstance

/-- Restriction along an open immersion preserves finite colimits. -/
instance immRestrict_preservesFiniteColimits : PreservesFiniteColimits (immRestrict i) :=
  have : (immRestrict i).IsLeftAdjoint := ⟨_, ⟨immRestrictAdjunction i⟩⟩
  inferInstance

/-- Pullback along an open immersion preserves finite limits. -/
instance modulePullback_preservesFiniteLimits_of_isOpenImmersion :
    PreservesFiniteLimits (modulePullback i) :=
  preservesFiniteLimits_of_natIso (immRestrictIsoPullback i)

end ImmRestrict

/-! ### The Mayer--Vietoris maps on sections -/

section Sections

variable (f : X ⟶ Y) (i : Z ⟶ X) [SheafedSpace.IsOpenImmersion i]

/-- The concrete model of `mvToOpen f i`: the unit of `immRestrict i ⊣ i_*`, pushed forward
along `f`.  Over an open `T` of `Y` it is the restriction map
`M(f⁻¹T) ⟶ M(f⁻¹T ⊓ immImage i)`. -/
noncomputable def mvToOpenModel :
    modulePushforward f ⟶
      (immRestrict i ⋙ modulePushforward i) ⋙ modulePushforward f :=
  Functor.whiskerRight (immRestrictAdjunction i).unit (modulePushforward f)

/-- The isomorphism identifying the target of `mvToOpenModel` with that of `mvToOpen`. -/
noncomputable def mvToOpenModelIso :
    (immRestrict i ⋙ modulePushforward i) ⋙ modulePushforward f ≅
      modulePullback i ⋙ modulePushforward (i ≫ f) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (immRestrictIsoPullback i) (modulePushforward i))
      (modulePushforward f) ≪≫
    restrictPushforwardIso f i

/-- `mvToOpen f i` is `mvToOpenModel f i` followed by the isomorphism `mvToOpenModelIso`. -/
lemma mvToOpen_eq :
    mvToOpen f i = mvToOpenModel f i ≫ (mvToOpenModelIso f i).hom := by
  dsimp only [mvToOpen, mvToOpenModel, mvToOpenModelIso]
  rw [← unit_immRestrictIsoPullback i, Functor.whiskerRight_comp]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Category.assoc]

/-- `mvToOpenModel` on sections over an open `T` of `Y`: the restriction map of `M` from
`f⁻¹T` to `i(i⁻¹(f⁻¹T))`. -/
lemma mvToOpenModel_app_val_app (M : SheafOfModules.{u} (structureSheafRing X))
    (T : (Opens (Y : TopCat))ᵒᵖ)
    (x : ((modulePushforward f).obj M).val.obj T) :
    ((mvToOpenModel f i).app M).val.app T x =
      M.val.map ((immOpensAdjunction i).counit.app ((opensMap f).obj T.unop)).op x :=
  rfl

end Sections

end Stacks.Cohomology.RelativeMayerVietoris

end
