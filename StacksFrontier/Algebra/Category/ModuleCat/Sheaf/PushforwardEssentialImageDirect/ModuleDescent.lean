module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.AdjunctionBinaryOp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjointPullPush

/-!
# Essential surjectivity of the direct image of modules along a closed immersion of topoi

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi whose direct image `f_*` on sheaves of sets is
fully faithful, and let `O` be a sheaf of rings on `C`. The direct image of modules of Stacks
03D1, `Stacks.Sheaves.ToposPushforward.pushforwardModuleFunctor f O : Mod(O) ⥤ Mod(f_*O)`, is
then essentially surjective onto those sheaves of `f_*O`-modules whose underlying sheaf of sets
lies in the essential image of `f_*`.

This is the input that the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardEssentialImage.lean` record as missing
for the converse half of Stacks 08M3 — "the reconstruction of a sheaf of modules from an internal
module object". It is obtained here without any internal module object: the module over `O` is the
inverse image of `H` with its scalars restricted along the structure map `O ⟶ f⁻¹f_*O`, the
inverse of the ring counit, which is an isomorphism because `f_*` is fully faithful; and the
isomorphism between `f_*` of it and `H` is the unit of `f⁻¹ ⊣ f_*`, which is a morphism of sheaves
of modules by `CategoryTheory.Adjunction.binaryOp_comp_unit`.

## Main definitions

* `Stacks.Sheaves.PushforwardEssentialImage.sourceScalarMap`: the inverse of the ring counit
  `f⁻¹f_*O ⟶ O`, a morphism of sheaves of rings `O ⟶ f⁻¹f_*O`.
* `Stacks.Sheaves.PushforwardEssentialImage.inverseImageModuleOverSource`: for a sheaf of
  `f_*O`-modules `H`, the sheaf of `O`-modules `f⁻¹H` with its scalars restricted along
  `sourceScalarMap`.
* `Stacks.Sheaves.PushforwardEssentialImage.unitModuleHom`: the unit of `f⁻¹ ⊣ f_*` at the
  underlying sheaf of sets of `H`, read as a morphism of sheaves of `f_*O`-modules
  `H ⟶ f_*(inverseImageModuleOverSource H)`.

## Main results

* `Stacks.Sheaves.PushforwardEssentialImage.isIso_ringCounit`: the ring counit `f⁻¹f_*O ⟶ O` is an
  isomorphism when `f_*` is fully faithful.
* `Stacks.Sheaves.PushforwardEssentialImage.moduleAddHom_comp_unit` and
  `.moduleSMulHom_comp_unit`: the two squares making the unit a morphism of sheaves of modules.
* `Stacks.Sheaves.PushforwardEssentialImage.moduleSheafFunctor_map_unitModuleHom`: the underlying
  morphism of sheaves of sets of `unitModuleHom` is the unit of `f⁻¹ ⊣ f_*`.
* `Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModuleFunctor`: a sheaf of
  `f_*O`-modules whose underlying sheaf of sets is in the essential image of `f_*` is in the
  essential image of the direct image on sheaves of modules.

## Implementation notes

Everything rests on three identifications that hold by `rfl` in this library, so that no transport
isomorphism appears anywhere below: the underlying sheaf of sets of a pulled-back module is the
inverse image of the underlying sheaf of sets, the same for the direct image, and restriction of
scalars leaves the underlying sheaf of sets and the additive structure untouched. The first two are
the `moduleIso := Iso.refl _` fields of `Stacks.Sheaves.ToposPullback.pullbackModule` and of
`Stacks.Sheaves.ToposPushforward.pushforwardModule`, read off rather than quoted.

That the unit is a morphism of sheaves of modules is two instances of one categorical fact,
`CategoryTheory.Adjunction.binaryOp_comp_unit`: additivity is its case `a = 𝟙`, and compatibility
with scalars is the general case with `a` the underlying map of the ring counit. There the
hypothesis of the lemma is the `action_map` of `pullbackModule` composed with
`Stacks.Sheaves.RingedToposModules.moduleSMulHom_restrictScalars`, and the first component of its
conclusion collapses to an identity by the triangle identity of `f⁻¹ ⊣ f_*`.

Both `Stacks.Sheaves.ToposPullback.moduleAdd_map_aux'` and `.moduleSMul_map_aux'` are stated for an
arbitrary finite-product-preserving functor of sheaves of sets, so the same two lemmas serve for
the inverse image and for the direct image, and no separate direct-image version is needed.

The long spellings of the morphisms below are deliberate and the proofs are written as chains of
`congrArg` and `Eq.trans` rather than as rewrites: the two sides of each equation are spellings of
one morphism that agree only up to unfolding semireducible definitions of `ToposPullback`, so
`rw` cannot abstract over them and reports its lemmas as unused rather than as failing, while
`exact` and `refine` check at default transparency and go through unchanged.

The rings are `RingCat`-valued, not `CommRingCat`-valued: no commutativity is used. The section
universe is the same on both sides, as it is for `pushforwardModuleFunctor`.

## References

* [Stacks Project, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe w v u v' u'

namespace Stacks.Sheaves.PushforwardEssentialImage

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))) (O : Sheaf J RingCat.{w})

/-- The composite `f_*O ⟶ f_*f⁻¹f_*O ⟶ f_*O` of the unit of `f⁻¹ ⊣ f_*` with the direct image of
the underlying map of the ring counit is the identity: this is the triangle identity of
`f⁻¹ ⊣ f_*`, the underlying map of the ring counit being the counit. -/
theorem unit_comp_pushforward_map_ringCounit :
    f.adj.unit.app (Sheaf.ringSheaf (pushforwardRingSheaf f O)) ≫
      f.pushforward.map ((sheafCompose J (forget RingCat.{w})).map (ringCounit f O)) = 𝟙 _ := by
  rw [show (sheafCompose J (forget RingCat.{w})).map (ringCounit f O) =
    f.adj.counit.app (Sheaf.ringSheaf O) from ringSheafMap_ringCounit f O]
  exact f.adj.right_triangle_components (Sheaf.ringSheaf O)

/-- **The ring counit of a closed immersion is an isomorphism.** If the direct image of sheaves of
sets along `f` is fully faithful then the canonical map `f⁻¹f_*O ⟶ O` of sheaves of rings is an
isomorphism: its underlying map of sheaves of sets is the counit of `f⁻¹ ⊣ f_*`, an isomorphism
because the right adjoint is fully faithful, and `sheafCompose J (forget RingCat)` reflects
isomorphisms. -/
theorem isIso_ringCounit [f.pushforward.Full] [f.pushforward.Faithful] :
    IsIso (ringCounit f O) := by
  have hc : IsIso f.adj.counit := Adjunction.counit_isIso_of_R_fully_faithful f.adj
  have : IsIso ((sheafCompose J (forget RingCat.{w})).map (ringCounit f O)) := by
    rw [ringSheafMap_ringCounit]
    exact NatIso.isIso_app_of_isIso _ _
  exact isIso_of_reflects_iso _ (sheafCompose J (forget RingCat.{w}))

variable [f.pushforward.Full] [f.pushforward.Faithful]

/-- The structure map `O ⟶ f⁻¹f_*O` of sheaves of rings: the inverse of the ring counit, which is
an isomorphism because `f_*` is fully faithful. Restriction of scalars along it turns a sheaf of
`f⁻¹f_*O`-modules into a sheaf of `O`-modules. -/
noncomputable def sourceScalarMap : O ⟶ inverseImageRingSheaf f (pushforwardRingSheaf f O) :=
  letI := isIso_ringCounit f O
  inv (ringCounit f O)

/-- The ring counit followed by `sourceScalarMap` is the identity. -/
theorem ringCounit_comp_sourceScalarMap : ringCounit f O ≫ sourceScalarMap f O = 𝟙 _ := by
  let := isIso_ringCounit f O
  exact IsIso.hom_inv_id _

/-- On underlying sheaves of sets, the ring counit followed by `sourceScalarMap` is the
identity. -/
theorem ringSheafMap_ringCounit_comp_sourceScalarMap :
    (sheafCompose J (forget RingCat.{w})).map (ringCounit f O) ≫
      (sheafCompose J (forget RingCat.{w})).map (sourceScalarMap f O) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, ringCounit_comp_sourceScalarMap,
    CategoryTheory.Functor.map_id]

/-- The sheaf of `O`-modules attached to a sheaf of `f_*O`-modules `H`: the inverse image of `H` in
the sense of Stacks 03D2, with its scalars restricted along `sourceScalarMap`. Its underlying sheaf
of sets is `f⁻¹` of the underlying sheaf of sets of `H`, by `rfl`. -/
noncomputable def inverseImageModuleOverSource
    (H : SheafOfModules.{w} (pushforwardRingSheaf f O)) : SheafOfModules.{w} O :=
  (SheafOfModules.restrictScalars (sourceScalarMap f O)).obj
    ((pullbackModuleFunctor J f.inverseImage (pushforwardRingSheaf f O)).obj H)

variable {f O} (H : SheafOfModules.{w} (pushforwardRingSheaf f O))

/-- The underlying sheaf of sets of `inverseImageModuleOverSource` is the inverse image of the
underlying sheaf of sets. -/
theorem moduleSheaf_inverseImageModuleOverSource :
    Sheaf.moduleSheaf O (inverseImageModuleOverSource f O H) =
      f.inverseImage.obj (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H) :=
  rfl

/-- The unit of `f⁻¹ ⊣ f_*` is additive for the module structures of `H` and of the direct image of
`inverseImageModuleOverSource H`. This is the additivity square of a morphism of sheaves of
modules. -/
theorem moduleAddHom_comp_unit :
    Sheaf.moduleAddHom (pushforwardRingSheaf f O) H ≫
        f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H) =
      prod.map (f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H))
          (f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H)) ≫
        Sheaf.moduleAddHom (pushforwardRingSheaf f O)
          ((pushforwardModuleFunctor f O).obj (inverseImageModuleOverSource f O H)) := by
  have : PreservesLimits f.pushforward := f.adj.rightAdjoint_preservesLimits
  have key := f.adj.binaryOp_comp_unit_id
    (Sheaf.moduleAddHom (pushforwardRingSheaf f O) H)
    (Sheaf.moduleAddHom (pullbackRingSheaf J f.inverseImage (pushforwardRingSheaf f O))
      (pullbackModuleObj J f.inverseImage (pushforwardRingSheaf f O) H))
    (moduleAdd_map_aux' J f.inverseImage (pushforwardRingSheaf f O) H)
  have htarget := (IsIso.inv_comp_eq _).mpr
    (moduleAdd_map_aux' K f.pushforward O (inverseImageModuleOverSource f O H))
  exact key.trans (congrArg (fun m ↦ prod.map
    (f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H))
    (f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H)) ≫ m) htarget)

/-- The scalar multiplication of `inverseImageModuleOverSource H`, precomposed with the underlying
map of the ring counit in the ring variable, is the scalar multiplication of the inverse image of
`H` over the inverse-image ring: restriction of scalars along `sourceScalarMap` undoes the counit.
This is the hypothesis that `CategoryTheory.Adjunction.binaryOp_comp_unit` needs for the scalar
multiplication. -/
theorem prodMap_ringCounit_comp_moduleSMulHom :
    prod.map ((sheafCompose J (forget RingCat.{w})).map (ringCounit f O))
        (𝟙 (f.inverseImage.obj (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H))) ≫
      Sheaf.moduleSMulHom O (inverseImageModuleOverSource f O H) =
        Sheaf.moduleSMulHom (pullbackRingSheaf J f.inverseImage (pushforwardRingSheaf f O))
          (pullbackModuleObj J f.inverseImage (pushforwardRingSheaf f O) H) := by
  have hrs : Sheaf.moduleSMulHom O (inverseImageModuleOverSource f O H) =
      prod.map ((sheafCompose J (forget RingCat.{w})).map (sourceScalarMap f O))
          (𝟙 (f.inverseImage.obj (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H))) ≫
        Sheaf.moduleSMulHom (pullbackRingSheaf J f.inverseImage (pushforwardRingSheaf f O))
          (pullbackModuleObj J f.inverseImage (pushforwardRingSheaf f O) H) :=
    moduleSMulHom_restrictScalars _ _
  have e : prod.map ((sheafCompose J (forget RingCat.{w})).map (ringCounit f O))
        (𝟙 (f.inverseImage.obj (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H))) ≫
      prod.map ((sheafCompose J (forget RingCat.{w})).map (sourceScalarMap f O))
        (𝟙 (f.inverseImage.obj (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H))) = 𝟙 _ := by
    rw [prod.map_map, ringSheafMap_ringCounit_comp_sourceScalarMap, Category.comp_id,
      prod.map_id_id]
  refine (congrArg (fun m ↦ prod.map ((sheafCompose J (forget RingCat.{w})).map (ringCounit f O))
    (𝟙 (f.inverseImage.obj (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H))) ≫ m) hrs).trans ?_
  refine (Category.assoc
    (prod.map ((sheafCompose J (forget RingCat.{w})).map (ringCounit f O))
      (𝟙 (f.inverseImage.obj (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H))))
    (prod.map ((sheafCompose J (forget RingCat.{w})).map (sourceScalarMap f O))
      (𝟙 (f.inverseImage.obj (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H))))
    (Sheaf.moduleSMulHom (pullbackRingSheaf J f.inverseImage (pushforwardRingSheaf f O))
      (pullbackModuleObj J f.inverseImage (pushforwardRingSheaf f O) H))).symm.trans ?_
  refine (congrArg (fun m ↦ m ≫
    Sheaf.moduleSMulHom (pullbackRingSheaf J f.inverseImage (pushforwardRingSheaf f O))
      (pullbackModuleObj J f.inverseImage (pushforwardRingSheaf f O) H)) e).trans ?_
  exact Category.id_comp _

/-- The unit of `f⁻¹ ⊣ f_*` is compatible with the scalar multiplications of `H` and of the direct
image of `inverseImageModuleOverSource H`. This is the scalar square of a morphism of sheaves of
modules. -/
theorem moduleSMulHom_comp_unit :
    Sheaf.moduleSMulHom (pushforwardRingSheaf f O) H ≫
        f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H) =
      prod.map (𝟙 (Sheaf.ringSheaf (pushforwardRingSheaf f O)))
          (f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H)) ≫
        Sheaf.moduleSMulHom (pushforwardRingSheaf f O)
          ((pushforwardModuleFunctor f O).obj (inverseImageModuleOverSource f O H)) := by
  have : PreservesLimits f.pushforward := f.adj.rightAdjoint_preservesLimits
  have key := f.adj.binaryOp_comp_unit
    ((sheafCompose J (forget RingCat.{w})).map (ringCounit f O))
    (Sheaf.moduleSMulHom (pushforwardRingSheaf f O) H)
    (Sheaf.moduleSMulHom O (inverseImageModuleOverSource f O H))
    ((moduleSMul_map_aux' J f.inverseImage (pushforwardRingSheaf f O) H).trans
      (congrArg (fun m ↦ prodComparison f.inverseImage
        (Sheaf.ringSheaf (pushforwardRingSheaf f O))
        (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H) ≫ m)
        (prodMap_ringCounit_comp_moduleSMulHom H).symm))
  rw [unit_comp_pushforward_map_ringCounit] at key
  have htarget := (IsIso.inv_comp_eq _).mpr
    (moduleSMul_map_aux' K f.pushforward O (inverseImageModuleOverSource f O H))
  exact key.trans (congrArg (fun m ↦ prod.map
    (𝟙 (Sheaf.ringSheaf (pushforwardRingSheaf f O)))
    (f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H)) ≫ m) htarget)

/-- The unit of `f⁻¹ ⊣ f_*` at the underlying sheaf of sets of `H`, read as a morphism of sheaves
of `f_*O`-modules `H ⟶ f_*(f⁻¹H)`. -/
noncomputable def unitModuleHom :
    H ⟶ (pushforwardModuleFunctor f O).obj (inverseImageModuleOverSource f O H) :=
  homEquivSubtype.symm ⟨f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H),
    moduleAddHom_comp_unit H, moduleSMulHom_comp_unit H⟩

/-- The underlying morphism of sheaves of sets of `unitModuleHom` is the unit of `f⁻¹ ⊣ f_*`. -/
@[simp]
theorem moduleSheafFunctor_map_unitModuleHom :
    (Sheaf.moduleSheafFunctor (pushforwardRingSheaf f O)).map (unitModuleHom H) =
      f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H) :=
  rfl

/-- **Essential surjectivity of the direct image on sheaves of modules.** If the underlying sheaf
of sets of a sheaf of `f_*O`-modules `H` lies in the essential image of the direct image `f_*` on
sheaves of sets, then `H` lies in the essential image of the direct image on sheaves of modules of
Stacks 03D1.

The module over `O` is `inverseImageModuleOverSource H` and the isomorphism is `unitModuleHom H`:
it is an isomorphism because its underlying morphism of sheaves of sets is the unit of
`f⁻¹ ⊣ f_*`, which is an isomorphism exactly on the essential image of `f_*`. -/
theorem essImage_pushforwardModuleFunctor
    (hH : f.pushforward.essImage (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H)) :
    (pushforwardModuleFunctor f O).essImage H := by
  have hunit : IsIso (f.adj.unit.app (Sheaf.moduleSheaf (pushforwardRingSheaf f O) H)) :=
    f.adj.isIso_unit_app_iff_mem_essImage.mpr hH
  have : IsIso ((Sheaf.moduleSheafFunctor (pushforwardRingSheaf f O)).map (unitModuleHom H)) := by
    rw [moduleSheafFunctor_map_unitModuleHom]
    exact hunit
  have := isIso_of_reflects_iso (unitModuleHom H)
    (Sheaf.moduleSheafFunctor (pushforwardRingSheaf f O))
  exact ⟨inverseImageModuleOverSource f O H, ⟨(asIso (unitModuleHom H)).symm⟩⟩

end Stacks.Sheaves.PushforwardEssentialImage

end
