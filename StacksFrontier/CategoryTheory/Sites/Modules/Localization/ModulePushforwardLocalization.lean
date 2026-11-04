module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialSurjectivity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ModulePullback
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposMorphismLocalization
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The direct image of sheaves of modules along a localized morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi, let `G` be a sheaf of
sets on `D` and put `F = f⁻¹G`. Stacks 04IF asserts, among other things, that the square formed
by `f`, its localization `f'` and the two localization morphisms `j_F` and `j_G` commutes on
sheaves of **modules**: `f'_* j_F^* = j_G^* f_*`.

This file supplies that identification one sheaf of modules at a time. By Stacks 04IE part (2)
the pullback `j^*` of sheaves of modules along a localization morphism is restriction to the
site of elements, so the statement to prove is that restricting a sheaf of `O`-modules `M` to
the site of elements of `F` and pushing it forward along `f'` agrees with pushing `M` forward
along `f` and restricting to the site of elements of `G`.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.localizationCompPushforwardModulesIso`: the square itself,
  `j_F^* ⋙ f'_* ≅ f_* ⋙ j_G^*`, with both pullbacks the pullbacks of sheaves of modules along
  the localization morphisms, and
  `Stacks.Sheaves.RingedToposModules.elementRestrictionCompPushforwardModulesIso`: the same
  identification with each pullback read as restriction to the site of elements.
* `Stacks.Sheaves.RingedToposModules.localizedPushforwardElementRestrictionHom` and
  `.localizedPushforwardElementRestrictionIso`: the comparison morphism of sheaves of modules,
  and the isomorphism it is, at one sheaf of modules.
* `AlgebraicGeometry.RingedTopos.elementRestrictionModules`: restriction of sheaves of modules
  to the site of elements, named at the structure sheaf of the localized ringed topos.

## Main results

* `Stacks.Sheaves.ToposPullback.moduleAddObj_restrictionModules` and
  `.moduleSMulObj_restrictionModules`: the addition and the scalar action of the restriction of
  a sheaf of modules along a continuous functor of sites, read through a further
  finite-product-preserving functor to types, are those of the original module read through the
  restriction functor followed by it. These are the restriction-side companions of
  `Stacks.Sheaves.ToposPullback.moduleAdd_map_aux'` and `.moduleSMul_map_aux'`, which compare
  the operations of the *transported* inverse image instead.
* `AlgebraicGeometry.RingedTopos.moduleAddObj_elementRestriction` and
  `.moduleSMulObj_elementRestriction`: the same two facts for the restriction to the site of
  elements of a sheaf of sets, which is the pullback of Stacks 04IE part (2).
* `Stacks.Sheaves.RingedToposModules.localized_fSharpSet_comp`: the structure-map compatibility
  the comparison needs — the structure map of `f'`, followed by Stacks 04IF's comparison of
  direct images of sheaves of sets, is `j_G⁻¹` of the structure map of `f`.
* `AlgebraicGeometry.RingedTopos.moduleSheafFunctor_map_elementRestrictionModules_map`, and
  `moduleSheafFunctor_map_localizedPushforwardElementRestrictionHom` in
  `Stacks.Sheaves.RingedToposModules`: the underlying morphisms of sheaves of sets of
  restriction and of the comparison.
* `Stacks.Sheaves.RingedToposModules.elementRestrictionCompLocalizedPushforward_map`,
  `.pushforwardCompElementRestriction_map`,
  `.localizationCompLocalizedPushforwardSet_map` and `.pushforwardCompLocalizationSet_map`: the
  action on morphisms of the four composites of functors the square of 04IF compares, each named
  so that it can be rewritten without unfolding the composite.
* `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardCompElementRestriction_map`
  and `.moduleSheafFunctor_map_elementRestrictionCompLocalizedPushforward_map`: each side of the
  square acts on a morphism of sheaves of modules by the corresponding composite of functors of
  sheaves of sets, applied to the underlying morphism.
* `Stacks.Sheaves.RingedToposModules.localizedPushforwardElementRestriction_naturality`: the
  naturality square of the comparison, read on underlying sheaves of sets, where it is the
  naturality of the comparison of direct images of sheaves of sets.

## Implementation notes

A morphism of sheaves of modules cannot be transported along the set-level comparison
`AlgebraicGeometry.RingedToposHom.localizationCompPushforwardIso` directly, because
`CategoryTheory.Sheaf.moduleSheafFunctor` only reflects isomorphisms; what is available is
`Stacks.Sheaves.PushforwardEssentialImage.isoOfSheafHom`, which lifts an isomorphism of the
underlying sheaves of sets that is additive and semilinear on sections. Additivity and
semilinearity are checked by transporting the operations of `M` itself along each of the two
composites — `CategoryTheory.Sheaf.moduleAddObj` and `.moduleSMulObj` of `M` along the two
finite-product-preserving functors to sections — and then invoking
`CategoryTheory.Sheaf.moduleAddObj_naturality` and `.moduleSMulObj_naturality`. The scalars on
the two sides travel along the two structure maps, and matching them up is
`localized_fSharpSet_comp`.

Two spellings of the underlying sheaf of sets of the structure sheaf of `X` occur:
`CategoryTheory.Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)`, which is what the
transported scalar action is indexed by, and `X.forgetRing.obj X.O`, which is what
`AlgebraicGeometry.RingedToposHom.localized_fSharp_forget` names. They are the same sheaf, but
the comparison of inverse images applied to them is not recognizably the same *morphism* by the
elaborator: deciding that costs more than the heartbeat budget. The bridge is therefore made on
sections, where the two readings of the comparison are the same function on the nose, which is
`localizationCompPushforward_hom_app_apply`.

Naturality of the comparison is checked on underlying sheaves of sets, and is stated as a chain
of named steps rather than one proof.  Each step identifies a module-level spelling of an object
with its set-level spelling in a position on which the type of a morphism depends, and two such
identifications do not fit in the heartbeat budget of a single declaration; the composition of
the named steps costs nothing beyond the steps themselves.  For the same reason the two
congruences that paste a step into a composite are `CategoryTheory.eq_whisker` and
`.whisker_eq`, which take the other factor as an argument, rather than `congrArg` with that
factor inside a motive.

## References

* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback

universe t ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (p : C ⥤ D) [p.IsContinuous J K] (O : Sheaf K RingCat.{ww})
  (M : SheafOfModules.{ww} O)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The addition map of the restriction of a sheaf of modules along a continuous functor of
sites is the addition map of the transported inverse image: the two module structures on the
same restricted sheaf of sets agree. -/
lemma moduleAddHom_restrictionModules :
    Sheaf.moduleAddHom ((p.sheafPushforwardContinuous RingCat.{ww} J K).obj O)
        ((restrictionModules J K p O).obj M) =
      Sheaf.moduleAddHom
        (pullbackRingSheaf J (p.sheafPushforwardContinuous (Type ww) J K) O)
        (pullbackModuleObj J (p.sheafPushforwardContinuous (Type ww) J K) O M) :=
  Sheaf.hom_ext_sections fun V q ↦ by
  rw [← prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor J V) q,
    Sheaf.sectionsFunctor_map_moduleAddHom]
  exact ((moduleAddHom_pullback_apply J (p.sheafPushforwardContinuous (Type ww) J K) O M
    V _ _).trans (Sheaf.sectionsFunctor_map_moduleAddHom O M (p.op.obj V) _ _)).symm

/-- The scalar-action map of the restriction of a sheaf of modules along a continuous functor
of sites is the scalar-action map of the transported inverse image. -/
lemma moduleSMulHom_restrictionModules :
    Sheaf.moduleSMulHom ((p.sheafPushforwardContinuous RingCat.{ww} J K).obj O)
        ((restrictionModules J K p O).obj M) =
      Sheaf.moduleSMulHom
        (pullbackRingSheaf J (p.sheafPushforwardContinuous (Type ww) J K) O)
        (pullbackModuleObj J (p.sheafPushforwardContinuous (Type ww) J K) O M) :=
  Sheaf.hom_ext_sections fun V q ↦ by
  rw [← prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor J V) q,
    Sheaf.sectionsFunctor_map_moduleSMulHom]
  exact ((moduleSMulHom_pullback_apply J (p.sheafPushforwardContinuous (Type ww) J K) O M
    V _ _).trans (Sheaf.sectionsFunctor_map_moduleSMulHom O M (p.op.obj V) _ _)).symm

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The addition on the restriction of a sheaf of modules along a continuous functor of sites,
read through a finite-product-preserving functor `P` to types, is the addition on the original
module read through restriction followed by `P`. -/
lemma moduleAddObj_restrictionModules (P : Sheaf J (Type ww) ⥤ Type t)
    [PreservesFiniteProducts P]
    (x y : P.obj (Sheaf.moduleSheaf ((p.sheafPushforwardContinuous RingCat.{ww} J K).obj O)
      ((restrictionModules J K p O).obj M))) :
    Sheaf.moduleAddObj ((p.sheafPushforwardContinuous RingCat.{ww} J K).obj O)
        ((restrictionModules J K p O).obj M) P x y =
      Sheaf.moduleAddObj O M (p.sheafPushforwardContinuous (Type ww) J K ⋙ P) x y :=
  (congrArg (fun n ↦ P.map n (prodObjMk x y)) (moduleAddHom_restrictionModules J K p O M)).trans
    (moduleAddObj_pullbackModuleObj J (p.sheafPushforwardContinuous (Type ww) J K) O M P x y)

/-- The scalar action on the restriction of a sheaf of modules along a continuous functor of
sites, read through a finite-product-preserving functor `P` to types, is the action on the
original module read through restriction followed by `P`.  The scalar is unchanged: the sheaf of
rings of the restriction is the restriction of the sheaf of rings. -/
lemma moduleSMulObj_restrictionModules (P : Sheaf J (Type ww) ⥤ Type t)
    [PreservesFiniteProducts P]
    (r : P.obj (Sheaf.ringSheaf ((p.sheafPushforwardContinuous RingCat.{ww} J K).obj O)))
    (m : P.obj (Sheaf.moduleSheaf ((p.sheafPushforwardContinuous RingCat.{ww} J K).obj O)
      ((restrictionModules J K p O).obj M))) :
    Sheaf.moduleSMulObj ((p.sheafPushforwardContinuous RingCat.{ww} J K).obj O)
        ((restrictionModules J K p O).obj M) P r m =
      Sheaf.moduleSMulObj O M (p.sheafPushforwardContinuous (Type ww) J K ⋙ P) r m :=
  (congrArg (fun n ↦ P.map n (prodObjMk r m)) (moduleSMulHom_restrictionModules J K p O M)).trans
    (moduleSMulObj_pullbackModuleObj J (p.sheafPushforwardContinuous (Type ww) J K) O M P r m)

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})] in
/-- Restriction along a continuous functor of sites acts on a morphism of sheaves of modules by
the restriction of the underlying morphism of sheaves of sets. -/
lemma moduleSheafFunctor_map_restrictionModules_map {M' : SheafOfModules.{ww} O} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor ((p.sheafPushforwardContinuous RingCat.{ww} J K).obj O)).map
        ((restrictionModules J K p O).map φ) =
      (p.sheafPushforwardContinuous (Type ww) J K).map
        ((Sheaf.moduleSheafFunctor O).map φ) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedTopos

universe t u

variable (Z : RingedTopos.{u, u, u}) (H : Z.Topos)
  (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
  (P : Sheaf (Z.localizedRingedTopos H).J (Type u) ⥤ Type t)
  [hP : PreservesFiniteProducts P]

/-- The addition on the restriction of a sheaf of modules to the site of elements of `H`, read
through a finite-product-preserving functor `P` to types, is the addition on the original module
read through the inverse image of the localization morphism followed by `P`. -/
lemma moduleAddObj_elementRestriction
    (x y : P.obj ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Z.localizedRingedTopos H).O)).obj
      ((SheafOfModules.pushforward (elementModuleRingHom Z H)).obj N))) :
    Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf (Z.localizedRingedTopos H).O)
        ((SheafOfModules.pushforward (elementModuleRingHom Z H)).obj N) P x y =
      Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) N
        ((Z.localizationMorphism H).toToposHom.inverseImage ⋙ P) x y := by
  have : PreservesFiniteProducts
      (show Sheaf (elementTopology Z H) (Type u) ⥤ Type t from P) := hP
  exact moduleAddObj_restrictionModules (elementTopology Z H) Z.J (elementProjection Z H)
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) N P x y

/-- The scalar action on the restriction of a sheaf of modules to the site of elements of `H`,
read through a finite-product-preserving functor `P` to types, is the action on the original
module read through the inverse image of the localization morphism followed by `P`. -/
lemma moduleSMulObj_elementRestriction
    (r : P.obj ((sheafCompose (Z.localizedRingedTopos H).J (forget RingCat.{u})).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (Z.localizedRingedTopos H).O)))
    (m : P.obj ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Z.localizedRingedTopos H).O)).obj
      ((SheafOfModules.pushforward (elementModuleRingHom Z H)).obj N))) :
    Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf (Z.localizedRingedTopos H).O)
        ((SheafOfModules.pushforward (elementModuleRingHom Z H)).obj N) P r m =
      Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) N
        ((Z.localizationMorphism H).toToposHom.inverseImage ⋙ P) r m := by
  have : PreservesFiniteProducts
      (show Sheaf (elementTopology Z H) (Type u) ⥤ Type t from P) := hP
  exact moduleSMulObj_restrictionModules (elementTopology Z H) Z.J (elementProjection Z H)
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) N P r m

/-- Restriction to the site of elements of `H` acts on a morphism of sheaves of modules by the
inverse image, along the localization morphism, of the underlying morphism of sheaves of
sets. -/
lemma moduleSheafFunctor_map_elementRestriction_map
    {N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)} (φ : N ⟶ N') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Z.localizedRingedTopos H).O)).map
        ((SheafOfModules.pushforward (elementModuleRingHom Z H)).map φ) =
      (Z.localizationMorphism H).toToposHom.inverseImage.map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map φ) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- **Restriction of sheaves of modules to the site of elements of `H`**, named at the structure
sheaf of the localized ringed topos.

This is `CategoryTheory.SheafOfModules.pushforward` along the structure map
`elementModuleRingHom Z H` of the localization, whose target is indexed by
`AlgebraicGeometry.RingedTopos.localizedRingSheaf`; the sheaves of modules on the localized
ringed topos are indexed by `Stacks.SheafOfModules.Tensor.ringSheaf` of it
instead.  The two sheaves of rings are the same, but recognizing that is expensive, so it is
done once here and the name is used afterwards: a composite such as
`elementRestrictionModules Z H ⋙ pushforwardModules f` is then a composite of two functors whose
middle category is spelled the same way on both sides. -/
noncomputable def elementRestrictionModules :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (Z.localizedRingedTopos H).O) :=
  SheafOfModules.pushforward (F := elementProjection Z H) (J := elementTopology Z H) (K := Z.J)
    (elementModuleRingHom Z H)

/-- Restriction of sheaves of modules to the site of elements acts on a morphism by the inverse
image, along the localization morphism, of the underlying morphism of sheaves of sets.  This is
`moduleSheafFunctor_map_elementRestriction_map` read at `elementRestrictionModules`. -/
@[simp]
lemma moduleSheafFunctor_map_elementRestrictionModules_map
    {N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)} (φ : N ⟶ N') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Z.localizedRingedTopos H).O)).map
        ((elementRestrictionModules Z H).map φ) =
      (Z.localizationMorphism H).toToposHom.inverseImage.map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map φ) :=
  moduleSheafFunctor_map_elementRestriction_map Z H N φ

end AlgebraicGeometry.RingedTopos




namespace Stacks.Sheaves.RingedToposModules

open AlgebraicGeometry AlgebraicGeometry.RingedTopos

universe uu

variable {X Y : RingedTopos.{uu, uu, uu}} (f : AlgebraicGeometry.RingedToposHom X Y)
  (G : Y.Topos)

/-- The structure map of the localized morphism `f'`, followed by Stacks 04IF's comparison of
direct images of sheaves of sets at the structure sheaf of `X`, is the inverse image along `j_G`
of the structure map of `f`. -/
theorem localized_fSharpSet_comp :
    fSharpSet (f.localized G).toRingedToposModulesHom ≫
        (f.localizationCompPushforwardIso G).hom.app (X.forgetRing.obj X.O) =
      (Y.localizationMorphism G).toToposHom.inverseImage.map
        (fSharpSet f.toRingedToposModulesHom) :=
  (congrArg (fun z ↦ z ≫ (f.localizationCompPushforwardIso G).hom.app
        (X.forgetRing.obj X.O))
      ((AlgebraicGeometry.RingedToposHom.ringFsharp_forget (f.localized G)).trans
        (f.localized_fSharp_forget G))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ (Y.localizationMorphism G).toToposHom.inverseImage.map
            (Y.forgetRing.map f.fSharp) ≫ z)
          ((f.localizationCompPushforwardIso G).inv_hom_id_app
            (X.forgetRing.obj X.O))).trans
        ((Category.comp_id _).trans
          (congrArg (Y.localizationMorphism G).toToposHom.inverseImage.map
            (AlgebraicGeometry.RingedToposHom.ringFsharp_forget f).symm))))

variable (M : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The addition on the sections of "restrict `M` to the site of elements of `f^{-1}G`, then
push forward along `f'`" is the addition of `M` transported along that composite of functors of
sheaves of sets. -/
theorem addObj_localizedPushforward_elementRestriction
    (W : (Y.localizedRingedTopos G).Cᵒᵖ)
    (x y : (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).obj
      ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).obj
        ((pushforwardModules (f.localized G).toRingedToposModulesHom).obj
          ((SheafOfModules.pushforward
            (elementModuleRingHom X (f.toToposHom.inverseImage.obj G))).obj M)))) :
    Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)
        ((pushforwardModules (f.localized G).toRingedToposModulesHom).obj
          ((SheafOfModules.pushforward
            (elementModuleRingHom X (f.toToposHom.inverseImage.obj G))).obj M))
        (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) x y =
      Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage ⋙
          (f.localized G).toRingedToposModulesHom.toToposHom.pushforward ⋙
            Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) x y :=
  (moduleAddObj_pushforwardModules (f.localized G).toRingedToposModulesHom
      ((SheafOfModules.pushforward
        (elementModuleRingHom X (f.toToposHom.inverseImage.obj G))).obj M)
      (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) x y).trans
    (moduleAddObj_elementRestriction X (f.toToposHom.inverseImage.obj G) M
      ((f.localized G).toRingedToposModulesHom.toToposHom.pushforward ⋙
        Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) x y)

/-- The addition on the sections of "push `M` forward along `f`, then restrict to the site of
elements of `G`" is the addition of `M` transported along that composite of functors of sheaves
of sets. -/
theorem addObj_elementRestriction_pushforward
    (W : (Y.localizedRingedTopos G).Cᵒᵖ)
    (a b : (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).obj
      ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).obj
        ((SheafOfModules.pushforward (elementModuleRingHom Y G)).obj
          ((pushforwardModules f.toRingedToposModulesHom).obj M)))) :
    Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)
        ((SheafOfModules.pushforward (elementModuleRingHom Y G)).obj
          ((pushforwardModules f.toRingedToposModulesHom).obj M))
        (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) a b =
      Sheaf.moduleAddObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        (f.toToposHom.pushforward ⋙
          (Y.localizationMorphism G).toToposHom.inverseImage ⋙
            Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) a b :=
  (moduleAddObj_elementRestriction Y G
      ((pushforwardModules f.toRingedToposModulesHom).obj M)
      (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) a b).trans
    (moduleAddObj_pushforwardModules f.toRingedToposModulesHom M
      ((Y.localizationMorphism G).toToposHom.inverseImage ⋙
        Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) a b)

/-- The scalar action on the sections of "restrict `M` to the site of elements of `f^{-1}G`,
then push forward along `f'`" is the action of `M` transported along that composite, the scalar
travelling along the structure map of `f'`. -/
theorem smulObj_localizedPushforward_elementRestriction
    (W : (Y.localizedRingedTopos G).Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).obj
      ((sheafCompose (Y.localizedRingedTopos G).J (forget RingCat.{uu})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)))
    (x : (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).obj
      ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).obj
        ((pushforwardModules (f.localized G).toRingedToposModulesHom).obj
          ((SheafOfModules.pushforward
            (elementModuleRingHom X (f.toToposHom.inverseImage.obj G))).obj M)))) :
    Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)
        ((pushforwardModules (f.localized G).toRingedToposModulesHom).obj
          ((SheafOfModules.pushforward
            (elementModuleRingHom X (f.toToposHom.inverseImage.obj G))).obj M))
        (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) r x =
      Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage ⋙
          (f.localized G).toRingedToposModulesHom.toToposHom.pushforward ⋙
            Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W)
        ((Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).map
          (fSharpSet (f.localized G).toRingedToposModulesHom) r) x :=
  (moduleSMulObj_pushforwardModules_fSharpSet (f.localized G).toRingedToposModulesHom
      ((SheafOfModules.pushforward
        (elementModuleRingHom X (f.toToposHom.inverseImage.obj G))).obj M)
      (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) r x).trans
    (moduleSMulObj_elementRestriction X (f.toToposHom.inverseImage.obj G) M
      ((f.localized G).toRingedToposModulesHom.toToposHom.pushforward ⋙
        Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) _ x)

/-- The scalar action on the sections of "push `M` forward along `f`, then restrict to the site
of elements of `G`" is the action of `M` transported along that composite, the scalar travelling
along the structure map of `f`. -/
theorem smulObj_elementRestriction_pushforward
    (W : (Y.localizedRingedTopos G).Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).obj
      ((sheafCompose (Y.localizedRingedTopos G).J (forget RingCat.{uu})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)))
    (a : (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).obj
      ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).obj
        ((SheafOfModules.pushforward (elementModuleRingHom Y G)).obj
          ((pushforwardModules f.toRingedToposModulesHom).obj M)))) :
    Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)
        ((SheafOfModules.pushforward (elementModuleRingHom Y G)).obj
          ((pushforwardModules f.toRingedToposModulesHom).obj M))
        (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) r a =
      Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        (f.toToposHom.pushforward ⋙
          (Y.localizationMorphism G).toToposHom.inverseImage ⋙
            Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W)
        (((Y.localizationMorphism G).toToposHom.inverseImage ⋙
            Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).map
          (fSharpSet f.toRingedToposModulesHom) r) a :=
  (moduleSMulObj_elementRestriction Y G
      ((pushforwardModules f.toRingedToposModulesHom).obj M)
      (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) r a).trans
    (moduleSMulObj_pushforwardModules_fSharpSet f.toRingedToposModulesHom M
      ((Y.localizationMorphism G).toToposHom.inverseImage ⋙
        Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) r a)

/-- On sections, Stacks 04IF's comparison of direct images of sheaves of sets does not see which
of the two spellings of the underlying sheaf of sets of the structure sheaf of `X` it is read
at: the two readings are the same function.

This is the bridge between the spelling the transported scalar action is indexed by,
`CategoryTheory.Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)`, and the spelling
`AlgebraicGeometry.RingedToposHom.localized_fSharp_forget` names, `X.forgetRing.obj X.O`.  At
the level of morphisms of sheaves the elaborator cannot afford to identify the two; on sections
it is definitional. -/
theorem localizationCompPushforward_hom_app_apply
    (W : (Y.localizedRingedTopos G).Cᵒᵖ)
    (w : (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).obj
      ((f.localized G).toRingedToposModulesHom.toToposHom.pushforward.obj
        ((sheafCompose (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).J
            (forget RingCat.{uu})).obj
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).O)))) :
    (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).map
        ((f.localizationCompPushforwardIso G).hom.app
          ((sheafCompose X.J (forget RingCat.{uu})).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) w =
      (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).map
        ((f.localizationCompPushforwardIso G).hom.app (X.forgetRing.obj X.O)) w := rfl

/-- **The structure-map compatibility on sections.** Applying the structure map of `f'` to a
section of the localized structure sheaf and then Stacks 04IF's comparison of direct images is
applying `j_G^{-1}` of the structure map of `f`.  This is the semilinearity input of the
comparison of sheaves of modules below. -/
theorem localizationCompPushforward_fSharpSet_apply
    (W : (Y.localizedRingedTopos G).Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).obj
      ((sheafCompose (Y.localizedRingedTopos G).J (forget RingCat.{uu})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O))) :
    (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).map
        ((f.localizationCompPushforwardIso G).hom.app
          ((sheafCompose X.J (forget RingCat.{uu})).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        ((Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).map
          (fSharpSet (f.localized G).toRingedToposModulesHom) r) =
      ((Y.localizationMorphism G).toToposHom.inverseImage ⋙
          Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).map
        (fSharpSet f.toRingedToposModulesHom) r :=
  (localizationCompPushforward_hom_app_apply f G W _).trans
    (congrArg (fun m ↦ (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).map m r)
      (localized_fSharpSet_comp f G))


/-- The underlying morphism of sheaves of sets of the comparison of Stacks 04IF on sheaves of
modules: the comparison `f'_* j_F^{-1} = j_G^{-1} f_*` of direct images of sheaves of sets,
read at the underlying sheaf of sets of `M`. -/
noncomputable abbrev localizedPushforwardElementRestrictionSheafHom :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).obj
        ((pushforwardModules (f.localized G).toRingedToposModulesHom).obj
          ((SheafOfModules.pushforward
            (elementModuleRingHom X (f.toToposHom.inverseImage.obj G))).obj M)) ⟶
      (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).obj
        ((SheafOfModules.pushforward (elementModuleRingHom Y G)).obj
          ((pushforwardModules f.toRingedToposModulesHom).obj M)) :=
  (f.localizationCompPushforwardIso G).hom.app
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M)

/-- **The comparison of Stacks 04IF on sheaves of modules, at one module.** Restricting `M` to
the site of elements of `f^{-1}G` and then pushing forward along the localized morphism `f'`
maps to pushing `M` forward along `f` and then restricting to the site of elements of `G`.

Its underlying morphism of sheaves of sets is
`localizedPushforwardElementRestrictionSheafHom`; additivity is the transport of the addition of
`M` along both composites, and semilinearity is the structure-map compatibility
`localized_fSharpSet_comp`.

This is a named morphism rather than an inlined argument to
`Stacks.Sheaves.RingedToposModules.ofSheafHom` so that the semilinearity witness is hidden
behind the name: `moduleSheafFunctor_map_localizedPushforwardElementRestrictionHom` then gives
the underlying map without reopening it. -/
noncomputable def localizedPushforwardElementRestrictionHom :
    (pushforwardModules (f.localized G).toRingedToposModulesHom).obj
        ((SheafOfModules.pushforward
          (elementModuleRingHom X (f.toToposHom.inverseImage.obj G))).obj M) ⟶
      (SheafOfModules.pushforward (elementModuleRingHom Y G)).obj
        ((pushforwardModules f.toRingedToposModulesHom).obj M) := by
  refine ofSheafHom (R := Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)
    (localizedPushforwardElementRestrictionSheafHom f G M) ?_ ?_
  · intro W x y
    refine Eq.trans (congrArg ((Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).map
        (localizedPushforwardElementRestrictionSheafHom f G M))
      ((Sheaf.sectionsFunctor_map_moduleAddHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)
          ((pushforwardModules (f.localized G).toRingedToposModulesHom).obj
            ((SheafOfModules.pushforward
              (elementModuleRingHom X (f.toToposHom.inverseImage.obj G))).obj M))
          W x y).symm.trans
        (addObj_localizedPushforward_elementRestriction f G M W x y))) ?_
    refine Eq.trans (Sheaf.moduleAddObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
      (Functor.whiskerRight (f.localizationCompPushforwardIso G).hom
        (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W)) x y) ?_
    exact (addObj_elementRestriction_pushforward f G M W _ _).symm.trans
      (Sheaf.sectionsFunctor_map_moduleAddHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)
        ((SheafOfModules.pushforward (elementModuleRingHom Y G)).obj
          ((pushforwardModules f.toRingedToposModulesHom).obj M)) W _ _)
  · intro W r x
    refine Eq.trans (congrArg ((Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).map
        (localizedPushforwardElementRestrictionSheafHom f G M))
      ((Sheaf.sectionsFunctor_map_moduleSMulHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)
          ((pushforwardModules (f.localized G).toRingedToposModulesHom).obj
            ((SheafOfModules.pushforward
              (elementModuleRingHom X (f.toToposHom.inverseImage.obj G))).obj M))
          W r x).symm.trans
        (smulObj_localizedPushforward_elementRestriction f G M W r x))) ?_
    refine Eq.trans (Sheaf.moduleSMulObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
      (Functor.whiskerRight (f.localizationCompPushforwardIso G).hom
        (Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W)) _ x) ?_
    refine Eq.trans (congrArg (fun z ↦ Sheaf.moduleSMulObj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        (f.toToposHom.pushforward ⋙ (Y.localizationMorphism G).toToposHom.inverseImage ⋙
          Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W) z
        ((Sheaf.sectionsFunctor (Y.localizedRingedTopos G).J W).map
          (localizedPushforwardElementRestrictionSheafHom f G M) x))
      (localizationCompPushforward_fSharpSet_apply f G W r)) ?_
    exact (smulObj_elementRestriction_pushforward f G M W r _).symm.trans
      (Sheaf.sectionsFunctor_map_moduleSMulHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)
        ((SheafOfModules.pushforward (elementModuleRingHom Y G)).obj
          ((pushforwardModules f.toRingedToposModulesHom).obj M)) W r _)

/-- The comparison of sheaves of modules is Stacks 04IF's comparison of direct images of sheaves
of sets on the underlying sheaves of sets. -/
@[simp]
theorem moduleSheafFunctor_map_localizedPushforwardElementRestrictionHom :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        (localizedPushforwardElementRestrictionHom f G M) =
      (f.localizationCompPushforwardIso G).hom.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M) :=
  rfl

/-- **Stacks 04IF on sheaves of modules, at one module.** Restricting `M` to the site of
elements of `f^{-1}G` and then pushing forward along the localized morphism `f'` is pushing `M`
forward along `f` and then restricting to the site of elements of `G`.

The comparison is `localizedPushforwardElementRestrictionHom`, which is an isomorphism because
its underlying morphism of sheaves of sets is one and
`CategoryTheory.Sheaf.moduleSheafFunctor` reflects isomorphisms. -/
noncomputable def localizedPushforwardElementRestrictionIso :
    (pushforwardModules (f.localized G).toRingedToposModulesHom).obj
        ((SheafOfModules.pushforward
          (elementModuleRingHom X (f.toToposHom.inverseImage.obj G))).obj M) ≅
      (SheafOfModules.pushforward (elementModuleRingHom Y G)).obj
        ((pushforwardModules f.toRingedToposModulesHom).obj M) :=
  @asIso _ _ _ _ (localizedPushforwardElementRestrictionHom f G M)
    (Stacks.Sheaves.PushforwardEssentialImage.isIso_of_isIso_moduleSheafFunctor_map
      (localizedPushforwardElementRestrictionHom f G M) (by
        rw [moduleSheafFunctor_map_localizedPushforwardElementRestrictionHom]
        exact ((f.localizationCompPushforwardIso G).app
          ((Sheaf.moduleSheafFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M)).isIso_hom))

/-- The comparison isomorphism is `localizedPushforwardElementRestrictionHom`. -/
@[simp]
theorem localizedPushforwardElementRestrictionIso_hom :
    (localizedPushforwardElementRestrictionIso f G M).hom =
      localizedPushforwardElementRestrictionHom f G M :=
  rfl

/-- The comparison isomorphism of sheaves of modules is Stacks 04IF's comparison of direct
images of sheaves of sets on the underlying sheaves of sets. -/
@[simp]
theorem moduleSheafFunctor_map_localizedPushforwardElementRestrictionIso_hom :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        (localizedPushforwardElementRestrictionIso f G M).hom =
      (f.localizationCompPushforwardIso G).hom.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M) :=
  rfl

variable {M}

/-- Restricting to the site of elements of `f^{-1}G` and then pushing forward along `f'`, as a
composite of functors, acts on a morphism by the two functors in turn. -/
theorem elementRestrictionCompLocalizedPushforward_map
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (elementRestrictionModules X (f.toToposHom.inverseImage.obj G) ⋙
        pushforwardModules.{uu, uu, uu, uu, uu, uu}
          (f.localized G).toRingedToposModulesHom).map φ =
      (pushforwardModules.{uu, uu, uu, uu, uu, uu}
          (f.localized G).toRingedToposModulesHom).map
        ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G)).map φ) :=
  rfl

/-- Pushing forward along `f` and then restricting to the site of elements of `G`, as a
composite of functors, acts on a morphism by the two functors in turn. -/
theorem pushforwardCompElementRestriction_map
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom ⋙
        elementRestrictionModules Y G).map φ =
      (elementRestrictionModules Y G).map
        ((pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom).map φ) :=
  rfl

/-- The source of Stacks 04IF's comparison of direct images of sheaves of sets acts on a
morphism by the inverse image of `j_F` and then the direct image of `f'`. -/
theorem localizationCompLocalizedPushforwardSet_map {P Q : Sheaf X.J (Type uu)} (g : P ⟶ Q) :
    ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage ⋙
        (f.localized G).toRingedToposModulesHom.toToposHom.pushforward).map g =
      (f.localized G).toRingedToposModulesHom.toToposHom.pushforward.map
        ((X.localizationMorphism
          (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map g) :=
  rfl

/-- The target of Stacks 04IF's comparison of direct images of sheaves of sets acts on a
morphism by the direct image of `f` and then the inverse image of `j_G`. -/
theorem pushforwardCompLocalizationSet_map {P Q : Sheaf X.J (Type uu)} (g : P ⟶ Q) :
    (f.toRingedToposModulesHom.toToposHom.pushforward ⋙
        (Y.localizationMorphism G).toToposHom.inverseImage).map g =
      (Y.localizationMorphism G).toToposHom.inverseImage.map
        (f.toRingedToposModulesHom.toToposHom.pushforward.map g) :=
  rfl

/-- Under the underlying-sheaf-of-sets functor, "restrict to the site of elements of `f^{-1}G`,
then push forward along `f'`" acts on a morphism by its two factors in turn. -/
theorem moduleSheafFunctor_map_elementRestrictionCompLocalizedPushforward_map_factor
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G) ⋙
          pushforwardModules.{uu, uu, uu, uu, uu, uu}
            (f.localized G).toRingedToposModulesHom).map φ) =
      (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((pushforwardModules.{uu, uu, uu, uu, uu, uu}
            (f.localized G).toRingedToposModulesHom).map
          ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G)).map φ)) :=
  congrArg (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
    (elementRestrictionCompLocalizedPushforward_map f G φ)

/-- The underlying morphism of sheaves of sets of the direct image along `f'` of the restriction
of `φ` is the direct image along `f'` of that restriction's underlying morphism. -/
theorem moduleSheafFunctor_map_localizedPushforward_elementRestriction_map
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((pushforwardModules.{uu, uu, uu, uu, uu, uu}
            (f.localized G).toRingedToposModulesHom).map
          ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G)).map φ)) =
      (f.localized G).toRingedToposModulesHom.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).O)).map
          ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G)).map φ)) :=
  moduleSheafFunctor_map_pushforwardModules_map
    (f.localized G).toRingedToposModulesHom
    ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G)).map φ)

/-- The direct image along `f'` of the restriction crossing: restriction to the site of elements
of `f^{-1}G` is the inverse image along `j_F` on underlying sheaves of sets, and `f'_*` of that
identification is the step the square needs. -/
theorem localizedPushforward_map_moduleSheafFunctor_elementRestriction_map
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (f.localized G).toRingedToposModulesHom.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).O)).map
          ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G)).map φ)) =
      (f.localized G).toRingedToposModulesHom.toToposHom.pushforward.map
        ((X.localizationMorphism
            (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ)) :=
  congrArg (f.localized G).toRingedToposModulesHom.toToposHom.pushforward.map
    (moduleSheafFunctor_map_elementRestrictionModules_map X
      (f.toToposHom.inverseImage.obj G) M φ)

/-- **The source of the square, on underlying sheaves of sets.** Restricting to the site of
elements of `f^{-1}G` and pushing forward along `f'` acts on a morphism of sheaves of modules by
`f'_*` of `j_F^{-1}` of the underlying morphism of sheaves of sets.

This is the composite of the three preceding steps.  They are stated separately because each is
a defeq check between the module-level and the set-level spelling of the same object, and the
three together exceed the heartbeat budget of a single declaration. -/
theorem moduleSheafFunctor_map_elementRestrictionCompLocalizedPushforward_map
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G) ⋙
          pushforwardModules.{uu, uu, uu, uu, uu, uu}
            (f.localized G).toRingedToposModulesHom).map φ) =
      (f.localized G).toRingedToposModulesHom.toToposHom.pushforward.map
        ((X.localizationMorphism
            (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ)) :=
  (moduleSheafFunctor_map_elementRestrictionCompLocalizedPushforward_map_factor f G φ).trans
    ((moduleSheafFunctor_map_localizedPushforward_elementRestriction_map f G φ).trans
      (localizedPushforward_map_moduleSheafFunctor_elementRestriction_map f G φ))

/-- Under the underlying-sheaf-of-sets functor, "push forward along `f`, then restrict to the
site of elements of `G`" acts on a morphism by its two factors in turn. -/
theorem moduleSheafFunctor_map_pushforwardCompElementRestriction_map_factor
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom ⋙
          elementRestrictionModules Y G).map φ) =
      (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((elementRestrictionModules Y G).map
          ((pushforwardModules.{uu, uu, uu, uu, uu, uu}
            f.toRingedToposModulesHom).map φ)) :=
  congrArg (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
    (pushforwardCompElementRestriction_map f G φ)

/-- The restriction crossing at `G`: restriction to the site of elements of `G` is the inverse
image along `j_G` on underlying sheaves of sets, applied to the direct image of `φ`. -/
theorem moduleSheafFunctor_map_elementRestriction_pushforward_map
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((elementRestrictionModules Y G).map
          ((pushforwardModules.{uu, uu, uu, uu, uu, uu}
            f.toRingedToposModulesHom).map φ)) =
      (Y.localizationMorphism G).toToposHom.inverseImage.map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((pushforwardModules.{uu, uu, uu, uu, uu, uu}
            f.toRingedToposModulesHom).map φ)) :=
  moduleSheafFunctor_map_elementRestrictionModules_map Y G
    ((pushforwardModules f.toRingedToposModulesHom).obj M)
    ((pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom).map φ)

/-- The inverse image along `j_G` of the direct-image crossing: the underlying morphism of
`f_*φ` is `f_*` of the underlying morphism of `φ`. -/
theorem localizationInverseImage_map_moduleSheafFunctor_pushforward_map
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Y.localizationMorphism G).toToposHom.inverseImage.map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((pushforwardModules.{uu, uu, uu, uu, uu, uu}
            f.toRingedToposModulesHom).map φ)) =
      (Y.localizationMorphism G).toToposHom.inverseImage.map
        (f.toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ)) :=
  congrArg (Y.localizationMorphism G).toToposHom.inverseImage.map
    (moduleSheafFunctor_map_pushforwardModules_map f.toRingedToposModulesHom φ)

/-- **The target of the square, on underlying sheaves of sets.** Pushing forward along `f` and
restricting to the site of elements of `G` acts on a morphism of sheaves of modules by
`j_G^{-1}` of `f_*` of the underlying morphism of sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardCompElementRestriction_map
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom ⋙
          elementRestrictionModules Y G).map φ) =
      (Y.localizationMorphism G).toToposHom.inverseImage.map
        (f.toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ)) :=
  (moduleSheafFunctor_map_pushforwardCompElementRestriction_map_factor f G φ).trans
    ((moduleSheafFunctor_map_elementRestriction_pushforward_map f G φ).trans
      (localizationInverseImage_map_moduleSheafFunctor_pushforward_map f G φ))

/-- **Naturality of Stacks 04IF's comparison of direct images, with its object a bound
variable.** This is `CategoryTheory.NatTrans.naturality` of
`AlgebraicGeometry.RingedToposHom.localizationCompPushforwardIso`, restated with the two
composites applied factor by factor rather than as composites of functors.

Only this spelling can be used by the square below: there the two sides are obtained from
morphisms of sheaves of modules, where no composite of functors of sheaves of sets occurs, and a
statement about `(j_F^{-1} ⋙ f'_*).map` would have to be matched against one about
`f'_*.map (j_F^{-1}.map _)` underneath the comparison. -/
theorem localizationCompPushforward_hom_naturality
    {B B' : Sheaf X.J (Type uu)} (g : B ⟶ B') :
    (f.localized G).toRingedToposModulesHom.toToposHom.pushforward.map
          ((X.localizationMorphism
            (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map g) ≫
        (f.localizationCompPushforwardIso G).hom.app B' =
      (f.localizationCompPushforwardIso G).hom.app B ≫
        (Y.localizationMorphism G).toToposHom.inverseImage.map
          (f.toToposHom.pushforward.map g) :=
  (f.localizationCompPushforwardIso G).hom.naturality g

/-- The left-hand side of the naturality square, with the comparison replaced by Stacks 04IF's
comparison of direct images of sheaves of sets. -/
theorem localizedPushforwardElementRestriction_naturality_lhs_comparison
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G) ⋙
            pushforwardModules.{uu, uu, uu, uu, uu, uu}
              (f.localized G).toRingedToposModulesHom).map φ ≫
          (localizedPushforwardElementRestrictionIso f G M').hom) =
      (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
          ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G) ⋙
            pushforwardModules.{uu, uu, uu, uu, uu, uu}
              (f.localized G).toRingedToposModulesHom).map φ) ≫
        (f.localizationCompPushforwardIso G).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M') :=
  ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map_comp _ _).trans
    ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G) ⋙
          pushforwardModules.{uu, uu, uu, uu, uu, uu}
            (f.localized G).toRingedToposModulesHom).map φ) ≫=
      moduleSheafFunctor_map_localizedPushforwardElementRestrictionIso_hom f G M')

/-- The left-hand side of the naturality square, with its first factor crossed to the set
level. -/
theorem localizedPushforwardElementRestriction_naturality_lhs_crossing
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
          ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G) ⋙
            pushforwardModules.{uu, uu, uu, uu, uu, uu}
              (f.localized G).toRingedToposModulesHom).map φ) ≫
        (f.localizationCompPushforwardIso G).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M') =
      (f.localized G).toRingedToposModulesHom.toToposHom.pushforward.map
            ((X.localizationMorphism
              (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
              ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ)) ≫
        (f.localizationCompPushforwardIso G).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M') :=
  moduleSheafFunctor_map_elementRestrictionCompLocalizedPushforward_map f G φ =≫
    (f.localizationCompPushforwardIso G).hom.app
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M')

/-- **The left-hand side of the naturality square, computed.** -/
theorem localizedPushforwardElementRestriction_naturality_lhs
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G) ⋙
            pushforwardModules.{uu, uu, uu, uu, uu, uu}
              (f.localized G).toRingedToposModulesHom).map φ ≫
          (localizedPushforwardElementRestrictionIso f G M').hom) =
      (f.localized G).toRingedToposModulesHom.toToposHom.pushforward.map
            ((X.localizationMorphism
              (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
              ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ)) ≫
        (f.localizationCompPushforwardIso G).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M') :=
  (localizedPushforwardElementRestriction_naturality_lhs_comparison f G φ).trans
    (localizedPushforwardElementRestriction_naturality_lhs_crossing f G φ)

/-- The right-hand side of the naturality square, with Stacks 04IF's comparison of direct images
replaced by the comparison of sheaves of modules. -/
theorem localizedPushforwardElementRestriction_naturality_rhs_comparison
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (f.localizationCompPushforwardIso G).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M) ≫
        (Y.localizationMorphism G).toToposHom.inverseImage.map
          (f.toToposHom.pushforward.map
            ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ)) =
      (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
          (localizedPushforwardElementRestrictionIso f G M).hom ≫
        (Y.localizationMorphism G).toToposHom.inverseImage.map
          (f.toToposHom.pushforward.map
            ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ)) :=
  (moduleSheafFunctor_map_localizedPushforwardElementRestrictionIso_hom f G M).symm =≫
    (Y.localizationMorphism G).toToposHom.inverseImage.map
      (f.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ))

/-- The right-hand side of the naturality square, with its second factor crossed back to the
module level. -/
theorem localizedPushforwardElementRestriction_naturality_rhs_crossing
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
          (localizedPushforwardElementRestrictionIso f G M).hom ≫
        (Y.localizationMorphism G).toToposHom.inverseImage.map
          (f.toToposHom.pushforward.map
            ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ)) =
      (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
          (localizedPushforwardElementRestrictionIso f G M).hom ≫
        (Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
          ((pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom ⋙
            elementRestrictionModules Y G).map φ) :=
  (Sheaf.moduleSheafFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
      (localizedPushforwardElementRestrictionIso f G M).hom ≫=
    (moduleSheafFunctor_map_pushforwardCompElementRestriction_map f G φ).symm

/-- The right-hand side of the naturality square, collected into a single underlying
morphism. -/
theorem localizedPushforwardElementRestriction_naturality_rhs_comp
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
          (localizedPushforwardElementRestrictionIso f G M).hom ≫
        (Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
          ((pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom ⋙
            elementRestrictionModules Y G).map φ) =
      (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((localizedPushforwardElementRestrictionIso f G M).hom ≫
          (pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom ⋙
            elementRestrictionModules Y G).map φ) :=
  ((Sheaf.moduleSheafFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map_comp _ _).symm

/-- **The right-hand side of the naturality square, computed.** -/
theorem localizedPushforwardElementRestriction_naturality_rhs
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (f.localizationCompPushforwardIso G).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M) ≫
        (Y.localizationMorphism G).toToposHom.inverseImage.map
          (f.toToposHom.pushforward.map
            ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ)) =
      (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((localizedPushforwardElementRestrictionIso f G M).hom ≫
          (pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom ⋙
            elementRestrictionModules Y G).map φ) :=
  (localizedPushforwardElementRestriction_naturality_rhs_comparison f G φ).trans
    ((localizedPushforwardElementRestriction_naturality_rhs_crossing f G φ).trans
      (localizedPushforwardElementRestriction_naturality_rhs_comp f G φ))

/-- **The comparison of Stacks 04IF on sheaves of modules is natural**, read on underlying
sheaves of sets, where it is naturality of the comparison of direct images of sheaves of sets. -/
theorem localizedPushforwardElementRestriction_naturality
    {M' : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : M ⟶ M') :
    (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((elementRestrictionModules X (f.toToposHom.inverseImage.obj G) ⋙
            pushforwardModules.{uu, uu, uu, uu, uu, uu}
              (f.localized G).toRingedToposModulesHom).map φ ≫
          (localizedPushforwardElementRestrictionIso f G M').hom) =
      (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)).map
        ((localizedPushforwardElementRestrictionIso f G M).hom ≫
          (pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom ⋙
            elementRestrictionModules Y G).map φ) :=
  (localizedPushforwardElementRestriction_naturality_lhs f G φ).trans
    ((localizationCompPushforward_hom_naturality f G
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map φ)).trans
      (localizedPushforwardElementRestriction_naturality_rhs f G φ))

/-- **Stacks 04IF on sheaves of modules, in restricted form.** Restriction to the site of
elements of `f^{-1}G` followed by the direct image along the localized morphism `f'` is the
direct image along `f` followed by restriction to the site of elements of `G`, naturally in the
sheaf of modules.

The components are `localizedPushforwardElementRestrictionIso`, and naturality is
`localizedPushforwardElementRestriction_naturality`. -/
noncomputable def elementRestrictionCompPushforwardModulesIso :
    elementRestrictionModules X (f.toToposHom.inverseImage.obj G) ⋙
        pushforwardModules.{uu, uu, uu, uu, uu, uu}
          (f.localized G).toRingedToposModulesHom ≅
      pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom ⋙
        elementRestrictionModules Y G :=
  NatIso.ofComponents (fun M ↦ localizedPushforwardElementRestrictionIso f G M)
    (fun {M M'} φ ↦ hom_ext_moduleSheafFunctor
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos G).O)
      (localizedPushforwardElementRestriction_naturality f G φ))

/-- **Stacks 04IF, the clause `f'_* j_F^* = j_G^* f_*` on sheaves of modules.** For a morphism
of ringed topoi `f : (Sh(C), O) ⟶ (Sh(D), O')`, a sheaf of sets `G` on `D` and `F = f^{-1}G`,
pulling a sheaf of `O`-modules back along the localization `j_F` and pushing it forward along
the localized morphism `f'` is pushing it forward along `f` and pulling back along the
localization `j_G`, naturally in the sheaf of modules.

Both pullbacks are the pullbacks of sheaves of modules of Stacks 03D6 part (2) along the
localization morphisms, which Stacks 04IE part (2)
(`AlgebraicGeometry.RingedTopos.localizationModulePullbackIso`) identifies with restriction to
the site of elements; the comparison is therefore
`elementRestrictionCompPushforwardModulesIso` conjugated by those two identifications. -/
@[stacks 04IF "f'_* j_F^* = j_G^* f_*, on sheaves of modules"]
noncomputable def localizationCompPushforwardModulesIso :
    RingedToposHom.pullbackModules.{uu, uu, uu, uu, uu, uu}
          (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)) (Y := X)
          (X.localizationMorphism
            (f.toToposHom.inverseImage.obj G)).toRingedToposModulesHom ⋙
        pushforwardModules.{uu, uu, uu, uu, uu, uu}
          (f.localized G).toRingedToposModulesHom ≅
      pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom ⋙
        RingedToposHom.pullbackModules.{uu, uu, uu, uu, uu, uu}
          (X := Y.localizedRingedTopos G) (Y := Y)
          (Y.localizationMorphism G).toRingedToposModulesHom :=
  Functor.isoWhiskerRight
      (X.localizationModulePullbackIso (f.toToposHom.inverseImage.obj G))
      (pushforwardModules.{uu, uu, uu, uu, uu, uu}
        (f.localized G).toRingedToposModulesHom) ≪≫
    elementRestrictionCompPushforwardModulesIso f G ≪≫
    Functor.isoWhiskerLeft
      (pushforwardModules.{uu, uu, uu, uu, uu, uu} f.toRingedToposModulesHom)
      (Y.localizationModulePullbackIso G).symm

end Stacks.Sheaves.RingedToposModules

end
