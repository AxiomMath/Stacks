module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFullyFaithful.Basic
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Comparing the two constructions of the direct image of modules along a morphism of ringed topoi

Stacks 03D6 part (1) is formalized twice in this development, over the two structures that
Stacks 01D3 part (2) and the modules development call a morphism of ringed topoi:

* `Stacks.Sheaves.RingedToposModules.pushforwardModules`, which carries the `03D6 "part (1)"`
  attribute, is defined for the four-field
  `Stacks.Sheaves.RingedToposModules.RingedToposHom` as restriction of scalars along the
  inverse-image form of the structure map followed by the direct image of Stacks 03D3. It is the
  right adjoint of `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`, the
  Stacks 03D7 adjunction.
* `AlgebraicGeometry.RingedToposHom.pushforwardModules` is defined for the two-field
  `AlgebraicGeometry.RingedToposHom` as the direct image of Stacks 03D1 followed by restriction of
  scalars along the direct-image form of the structure map. It is the functor the Stacks 08M3
  results — full faithfulness and the essential-image criterion — are stated for.

This file identifies the two, so that the Stacks 03D7 adjunction becomes available with the second
functor as its right adjoint. Nothing here restates either construction: the comparison is an
isomorphism of functors, and the adjunction is obtained from the existing one by transport along
it.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackRestrictScalarsIso`: for a finite-product-preserving
  functor `Φ` of categories of sheaves of sets, the inverse image of sheaves of modules of
  Stacks 03D2 commutes with restriction of scalars.
* `AlgebraicGeometry.RingedToposHom.pushforwardModulesIso`: the comparison of the two
  formalizations of Stacks 03D6 part (1).
* `AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModulesViaComparison`: **Stacks 03D7**
  for the
  two-field morphism of ringed topoi of Stacks 01D3 part (2).

## Main results

* `AlgebraicGeometry.RingedToposHom.ringFsharp_eq_structureRingMap`: the two ring-level
  direct-image forms of the structure map of a morphism of ringed topoi agree — the one obtained
  from the inverse-image form through the adjunction `f⁻¹ ⊣ f_*` for sheaves of rings, and the
  image of `f♯` under `forget₂ CommRingCat RingCat`.

## Implementation notes

The comparison is assembled from three facts, in increasing depth.

Restriction of scalars composes contravariantly *on the nose*:
`restrictScalars (g ≫ h) = restrictScalars h ⋙ restrictScalars g` holds by `rfl`, because the
module structure obtained by restricting twice is the one obtained by restricting along the
composite. So the two functors differ only by the order in which the direct image of Stacks 03D1
and a restriction of scalars are applied, and by which morphism of sheaves of rings is restricted
along.

Swapping the order is `pullbackRestrictScalarsIso`. Both functors send a sheaf of modules to a
sheaf whose underlying sheaf of sets, addition map, negation and zero are the same object and the
same morphisms — restriction of scalars changes none of them, and the Stacks 03D1 construction
reads them off the underlying sheaf. Only the scalar-multiplication maps differ, and
`moduleSMulHom_pullbackModuleObj_restrictScalars` identifies them: transporting the restricted
action along `Φ` is the transported action restricted along `Φ` of the morphism of sheaves of
rings. That identity is proved by composing with the product comparison of `Φ`, which is an
isomorphism, where `Stacks.Sheaves.ToposPullback.moduleSMul_map_aux'` expresses both sides in terms
of `Φ.map (moduleSMulHom _ _)` and `Limits.prodComparison_natural` moves the restriction across.

Which morphism of sheaves of rings is restricted along is `ringFsharp_eq_structureRingMap`. One
side is the adjunct of the inverse-image form under the ring-level adjunction, the other the image
of `f♯` under `forget₂ CommRingCat RingCat`; the two are *not* definitionally equal, not even on
sections. They agree because forgetting commutativity carries the adjunction for sheaves of
commutative rings to the adjunction for sheaves of rings, which is
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`, and because
`sheafCompose _ (forget RingCat)` is faithful.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

namespace Stacks.Sheaves.ToposPullback

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  {S R : Sheaf K RingCat.{w'}} (α : S ⟶ R)

/-- The scalar-multiplication map of the inverse image of a restriction of scalars is the scalar
multiplication of the inverse image, restricted along the inverse image of the morphism of sheaves
of rings. -/
theorem moduleSMulHom_pullbackModuleObj_restrictScalars (M : SheafOfModules.{w'} R) :
    Sheaf.moduleSMulHom (pullbackRingSheaf J Φ S)
        (pullbackModuleObj J Φ S ((SheafOfModules.restrictScalars α).obj M)) =
      Limits.prod.map ((sheafCompose J (forget RingCat.{w})).map (pullbackRingSheafMap J Φ α))
          (𝟙 (Φ.obj (Sheaf.moduleSheaf R M))) ≫
        Sheaf.moduleSMulHom (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) := by
  have hsrc : Φ.map (Sheaf.moduleSMulHom S ((SheafOfModules.restrictScalars α).obj M)) =
      prodComparison Φ (Sheaf.ringSheaf S) (Sheaf.moduleSheaf R M) ≫
        Sheaf.moduleSMulHom (pullbackRingSheaf J Φ S)
          (pullbackModuleObj J Φ S ((SheafOfModules.restrictScalars α).obj M)) :=
    moduleSMul_map_aux' J Φ S ((SheafOfModules.restrictScalars α).obj M)
  have htgt : Φ.map (Sheaf.moduleSMulHom R M) =
      prodComparison Φ (Sheaf.ringSheaf R) (Sheaf.moduleSheaf R M) ≫
        Sheaf.moduleSMulHom (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) :=
    moduleSMul_map_aux' J Φ R M
  have hres : Sheaf.moduleSMulHom S ((SheafOfModules.restrictScalars α).obj M) =
      Limits.prod.map ((sheafCompose K (forget RingCat.{w'})).map α)
          (𝟙 (Sheaf.moduleSheaf S ((SheafOfModules.restrictScalars α).obj M))) ≫
        Sheaf.moduleSMulHom R M := moduleSMulHom_restrictScalars α M
  have hnat : Φ.map (Limits.prod.map ((sheafCompose K (forget RingCat.{w'})).map α)
        (𝟙 (Sheaf.moduleSheaf R M))) ≫
        prodComparison Φ (Sheaf.ringSheaf R) (Sheaf.moduleSheaf R M) =
      prodComparison Φ (Sheaf.ringSheaf S) (Sheaf.moduleSheaf R M) ≫
        Limits.prod.map ((sheafCompose J (forget RingCat.{w})).map (pullbackRingSheafMap J Φ α))
          (𝟙 (Φ.obj (Sheaf.moduleSheaf R M))) := by
    rw [prodComparison_natural, ringSheafMap_pullbackRingSheafMap,
      CategoryTheory.Functor.map_id]
    rfl
  refine (cancel_epi (prodComparison Φ (Sheaf.ringSheaf S) (Sheaf.moduleSheaf R M))).mp ?_
  refine hsrc.symm.trans ?_
  refine ((congrArg Φ.map hres).trans (Φ.map_comp _ _)).trans ?_
  refine (congrArg (fun m => Φ.map (Limits.prod.map
    ((sheafCompose K (forget RingCat.{w'})).map α)
    (𝟙 (Sheaf.moduleSheaf R M))) ≫ m) htgt).trans ?_
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun m => m ≫ Sheaf.moduleSMulHom (pullbackRingSheaf J Φ R)
      (pullbackModuleObj J Φ R M)) hnat)).trans (Category.assoc _ _ _)

/-- The comparison of the inverse image of a restriction of scalars with the restriction of
scalars of the inverse image, on one sheaf of modules: the identity of the underlying sheaf of
sets, read as a morphism of sheaves of modules. -/
noncomputable def pullbackRestrictScalarsHom (M : SheafOfModules.{w'} R) :
    (pullbackModuleFunctor J Φ S).obj ((SheafOfModules.restrictScalars α).obj M) ⟶
      (SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α)).obj
        ((pullbackModuleFunctor J Φ R).obj M) :=
  homEquivSubtype.symm ⟨𝟙 (Φ.obj (Sheaf.moduleSheaf R M)),
    (Category.comp_id (Sheaf.moduleAddHom (pullbackRingSheaf J Φ S)
        (pullbackModuleObj J Φ S ((SheafOfModules.restrictScalars α).obj M)))).trans
      ((Category.id_comp (Sheaf.moduleAddHom (pullbackRingSheaf J Φ S)
            ((SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α)).obj
              (pullbackModuleObj J Φ R M)))).symm.trans
        (congrArg (fun m => m ≫ Sheaf.moduleAddHom (pullbackRingSheaf J Φ S)
            ((SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α)).obj
              (pullbackModuleObj J Φ R M)))
          (Limits.prod.map_id_id (X := Φ.obj (Sheaf.moduleSheaf R M))
            (Y := Φ.obj (Sheaf.moduleSheaf R M))).symm)),
    (Category.comp_id (Sheaf.moduleSMulHom (pullbackRingSheaf J Φ S)
        (pullbackModuleObj J Φ S ((SheafOfModules.restrictScalars α).obj M)))).trans
      ((moduleSMulHom_pullbackModuleObj_restrictScalars Φ α M).trans
        (prodMap_moduleSMulHom_restrictScalars
          (M := pullbackModuleObj J Φ S ((SheafOfModules.restrictScalars α).obj M))
          (N' := pullbackModuleObj J Φ R M) (pullbackRingSheafMap J Φ α)
          (𝟙 (Φ.obj (Sheaf.moduleSheaf R M)))).symm)⟩

/-- The comparison is an isomorphism: its underlying morphism of sheaves of sets is the identity,
and the underlying-sheaf functor on sheaves of modules reflects isomorphisms. -/
instance isIso_pullbackRestrictScalarsHom (M : SheafOfModules.{w'} R) :
    IsIso (pullbackRestrictScalarsHom Φ α M) := by
  have h : IsIso ((Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ S)).map
      (pullbackRestrictScalarsHom Φ α M)) := by
    have hid : (Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ S)).map
        (pullbackRestrictScalarsHom Φ α M) = 𝟙 (Φ.obj (Sheaf.moduleSheaf R M)) := rfl
    rw [hid]
    exact IsIso.id _
  exact isIso_of_reflects_iso (pullbackRestrictScalarsHom Φ α M)
    (Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ S))

/-- **The inverse image of sheaves of modules commutes with restriction of scalars.** The two
functors agree on underlying sheaves of sets, on addition, on negation and on the zero section;
the comparison of the scalar actions is
`Stacks.Sheaves.ToposPullback.moduleSMulHom_pullbackModuleObj_restrictScalars`. -/
noncomputable def pullbackRestrictScalarsIso :
    SheafOfModules.restrictScalars α ⋙ pullbackModuleFunctor J Φ S ≅
      pullbackModuleFunctor J Φ R ⋙
        SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α) :=
  NatIso.ofComponents (fun M => asIso (pullbackRestrictScalarsHom Φ α M))
    (fun {_M _N} _φ => hom_ext_moduleSheafFunctor
      ((((Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ S)).map_comp _ _).trans
        (Category.comp_id _)).trans
        ((Category.id_comp _).trans
          (((Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ S)).map_comp _ _).symm))))

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y)

/-- **The two ring-level direct-image forms of the structure map agree.** One is the adjunct, under
the adjunction `f⁻¹ ⊣ f_*` for sheaves of rings, of the inverse-image form of the structure map;
the other is the image of `f♯` under `forget₂ CommRingCat RingCat`. They agree because forgetting
commutativity carries the adjunction for sheaves of commutative rings to the one for sheaves of
rings.

This is not a definitional identity, not even on sections. -/
theorem ringFsharp_eq_structureRingMap : f.ringFsharp = f.structureRingMap := by
  refine (sheafCompose Y.J (forget RingCat.{w'})).map_injective ?_
  have hadjunct : f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O) (X.forgetRing.obj X.O)
      ((sheafCompose X.J (forget RingCat.{w})).map f.ringFsharpInverseImage) =
      Y.forgetRing.map f.fSharp :=
    (congrArg (f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O) (X.forgetRing.obj X.O))
      (fSharpInverseImage_forget_homEquiv f)).trans (Equiv.apply_symm_apply _ _)
  exact (ringSheafMap_ringFsharp f).trans hadjunct

/-- The composite of the unit `O_D ⟶ f_*f⁻¹O_D` with the direct image of the inverse-image form
of the structure map is the direct-image form of the structure map, at the level of sheaves of
rings. -/
theorem ringUnit_comp_pullbackRingSheafMap_ringFsharpInverseImage :
    ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≫
        pullbackRingSheafMap Y.J f.toToposHom.pushforward f.ringFsharpInverseImage =
      f.structureRingMap :=
  (ringImageAdjunction_homEquiv_apply f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      f.ringFsharpInverseImage).symm.trans f.ringFsharp_eq_structureRingMap

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The direct image of Stacks 03D1 followed by restriction of scalars first along the direct
image of the inverse-image form of the structure map and then along the unit `O_D ⟶ f_*f⁻¹O_D` is
`AlgebraicGeometry.RingedToposHom.pushforwardModules`: restriction of scalars composes
contravariantly on the nose, and the composite of the two morphisms of sheaves of rings is the
structure map. -/
theorem pushforwardModules_eq :
    (pullbackModuleFunctor Y.J f.toToposHom.pushforward
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
          SheafOfModules.restrictScalars
            (pullbackRingSheafMap Y.J f.toToposHom.pushforward f.ringFsharpInverseImage)) ⋙
        SheafOfModules.restrictScalars
          (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) =
      f.pushforwardModules := by
  change pullbackModuleFunctor Y.J f.toToposHom.pushforward
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      SheafOfModules.restrictScalars
        (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≫
          pullbackRingSheafMap Y.J f.toToposHom.pushforward f.ringFsharpInverseImage) =
    f.pushforwardModules
  exact congrArg
    (fun φ => pullbackModuleFunctor Y.J f.toToposHom.pushforward
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      SheafOfModules.restrictScalars φ)
    f.ringUnit_comp_pullbackRingSheafMap_ringFsharpInverseImage

/-- **The comparison of the two formalizations of Stacks 03D6 part (1).** The direct image on
sheaves of modules built for the four-field morphism of ringed topoi of the modules development is
isomorphic to the one built for the two-field morphism of Stacks 01D3 part (2). -/
noncomputable def pushforwardModulesIso :
    Stacks.Sheaves.RingedToposModules.pushforwardModules f.toRingedToposModulesHom ≅
      f.pushforwardModules :=
  CategoryTheory.Functor.isoWhiskerRight
      (pullbackRestrictScalarsIso f.toToposHom.pushforward f.ringFsharpInverseImage)
      (SheafOfModules.restrictScalars
        (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≪≫
    eqToIso f.pushforwardModules_eq

/-- **Stacks 03D7** for a morphism of ringed topoi in the sense of Stacks 01D3 part (2): pullback
of sheaves of modules is left adjoint to the direct image
`AlgebraicGeometry.RingedToposHom.pushforwardModules`.

The adjunction is the one of the modules development, transported along
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIso`.

This states 03D7 through the *four*-field hom `toRingedToposModulesHom`, where
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` states it through the two-field
`toModulesHom`. The two are provably but not definitionally equal, so they are kept as separate
declarations rather than identified by a bridging lemma. -/
noncomputable def pullbackAdjPushforwardModulesViaComparison
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    f.toRingedToposModulesHom.pullbackModules ⊣
      f.pushforwardModules :=
  Adjunction.ofNatIsoRight
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      f.toRingedToposModulesHom)
    f.pushforwardModulesIso

end AlgebraicGeometry.RingedToposHom

end
