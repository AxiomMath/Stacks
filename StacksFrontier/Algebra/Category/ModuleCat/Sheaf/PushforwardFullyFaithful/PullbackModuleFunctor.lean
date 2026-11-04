module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules

/-!
# Full faithfulness of the transport of sheaves of modules along a fully faithful functor

Let `Φ : Sh(D, K) ⥤ Sh(C, J)` be a finite-product-preserving functor between categories of
sheaves of sets and let `O` be a sheaf of rings on `(D, K)`. Transport along `Φ` carries sheaves
of `O`-modules to sheaves of modules over the transported sheaf of rings
`Stacks.Sheaves.ToposPullback.pullbackRingSheaf J Φ O`, by
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor`. This file shows that this transport
inherits faithfulness and fullness from `Φ`.

Both statements are formal consequences of the fact that the underlying sheaf of sets of a
transported sheaf of modules is, on the nose, the `Φ`-image of the underlying sheaf of sets of
the original. Faithfulness is then immediate. For fullness, a morphism `g` of transported
modules is in particular a morphism of the underlying sheaves of sets, so it is `Φ` of a
morphism `h` of the underlying sheaves of sets upstairs; the content is that `h` is again
additive and `O`-linear, and that is proved by transporting the two commuting squares that
express those properties back along `Φ`, which is legitimate because `Φ` is faithful and
preserves the binary products the squares are stated with.

## Main results

* `Stacks.Sheaves.ToposPullback.moduleAddHom_comp_of_map_eq` and
  `Stacks.Sheaves.ToposPullback.moduleSMulHom_comp_of_map_eq`: a morphism of the underlying
  sheaves of sets whose `Φ`-image is the underlying morphism of a morphism of transported
  sheaves of modules is additive, respectively `O`-linear.
* `Stacks.Sheaves.ToposPullback.faithful_pullbackModuleFunctor`,
  `Stacks.Sheaves.ToposPullback.full_pullbackModuleFunctor` and
  `Stacks.Sheaves.ToposPullback.fullyFaithfulPullbackModuleFunctor`: the transport of sheaves
  of modules along a fully faithful `Φ` is fully faithful.
* `Stacks.Sheaves.ToposPushforward.fullyFaithfulPushforwardModuleFunctor`: the special case of
  the direct image along a morphism of topoi whose direct image on sheaves of sets is fully
  faithful, which is the situation of a closed immersion of topoi.

## Implementation notes

The additivity and linearity of a morphism of the underlying sheaves of sets are expressed by
the commuting squares against `CategoryTheory.Sheaf.moduleAddHom` and
`CategoryTheory.Sheaf.moduleSMulHom` that `Stacks.Sheaves.RingedToposModules.homEquivSubtype`
already isolates, so no new description of a morphism of sheaves of modules is introduced here:
the reconstruction of the module morphism from the sheaf morphism is that equivalence.

Transporting a square back along `Φ` is done with `Φ.map_injective` and the compatibility of
`Φ` with the two operation maps, which main already records as
`Stacks.Sheaves.ToposPullback.moduleAdd_map_aux'` and `moduleSMul_map_aux'`. The chains are
written as `congrArg`/`Eq.trans` terms rather than with `rw`, because the goals mention the
underlying sheaf of a transported module both as `Φ.obj (O.moduleSheaf G)` and as
`(pullbackRingSheaf J Φ O).moduleSheaf (pullbackModuleObj J Φ O G)`; those agree definitionally
but not at `implicit` transparency, so `rw` reports the target as not type-correct while `exact`
checks the step at default transparency.

The two sites and the two universes of sections are independent throughout, exactly as in the
transport itself.

## References

* [Stacks Project, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Functor
open Stacks.Sheaves.RingedToposModules

universe ww ww' vv uu vv' uu'

namespace Stacks.Sheaves.ToposPullback

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'}) {G G' : SheafOfModules.{ww'} O}

/-- A square upstairs commutes if its `F`-image does, once both sides are rewritten through
comparison maps `c`, `c'` and a square `key` downstairs, for faithful `F`. -/
private theorem comp_eq_of_map_comp_eq {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    [F.Faithful] {X Y X' Y' : A} {a : X ⟶ Y} {a' : X' ⟶ Y'} {p : X ⟶ X'} {h : Y ⟶ Y'}
    {Z Z' : B} {c : F.obj X ⟶ Z} {c' : F.obj X' ⟶ Z'} {α : Z ⟶ F.obj Y} {α' : Z' ⟶ F.obj Y'}
    {q : Z ⟶ Z'} (hα : F.map a = c ≫ α) (hα' : F.map a' = c' ≫ α')
    (nat : F.map p ≫ c' = c ≫ q) (key : α ≫ F.map h = q ≫ α') : a ≫ h = p ≫ a' := by
  apply F.map_injective
  rw [F.map_comp, F.map_comp, hα, hα', Category.assoc, key, ← Category.assoc, ← nat,
    Category.assoc]

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- A morphism of the underlying sheaves of sets of two sheaves of `O`-modules whose `Φ`-image
is the underlying morphism of a morphism of the transported sheaves of modules is additive.

The square is transported back along `Φ`, which is faithful; the `Φ`-image of the addition map
is the addition map of the transported module read through the product comparison, which is
`moduleAdd_map_aux'`. -/
lemma moduleAddHom_comp_of_map_eq [Φ.Faithful]
    (g : (pullbackModuleFunctor J Φ O).obj G ⟶ (pullbackModuleFunctor J Φ O).obj G')
    (h : moduleSheaf O G ⟶ moduleSheaf O G')
    (hmap : Φ.map h = (moduleSheafFunctor (pullbackRingSheaf J Φ O)).map g) :
    moduleAddHom O G ≫ h = Limits.prod.map h h ≫ moduleAddHom O G' := by
  have key : moduleAddHom (pullbackRingSheaf J Φ O) ((pullbackModuleFunctor J Φ O).obj G) ≫
      Φ.map h = Limits.prod.map (Φ.map h) (Φ.map h) ≫
        moduleAddHom (pullbackRingSheaf J Φ O) ((pullbackModuleFunctor J Φ O).obj G') := by
    rw [hmap]
    exact moduleAddHom_comp_moduleSheafFunctor_map g
  exact comp_eq_of_map_comp_eq Φ (moduleAdd_map_aux' J Φ O G) (moduleAdd_map_aux' J Φ O G')
    (Limits.prodComparison_natural Φ h h) key

/-- A morphism of the underlying sheaves of sets of two sheaves of `O`-modules whose `Φ`-image
is the underlying morphism of a morphism of the transported sheaves of modules is compatible
with scalar multiplication.

The argument is that of `moduleAddHom_comp_of_map_eq`, with `moduleSMul_map_aux'` in place of
`moduleAdd_map_aux'` and the identity of the sheaf of rings in the first factor of the
product. -/
lemma moduleSMulHom_comp_of_map_eq [Φ.Faithful]
    (g : (pullbackModuleFunctor J Φ O).obj G ⟶ (pullbackModuleFunctor J Φ O).obj G')
    (h : moduleSheaf O G ⟶ moduleSheaf O G')
    (hmap : Φ.map h = (moduleSheafFunctor (pullbackRingSheaf J Φ O)).map g) :
    moduleSMulHom O G ≫ h =
      Limits.prod.map (𝟙 (Sheaf.ringSheaf O)) h ≫ moduleSMulHom O G' := by
  have key := ((congrArg (fun t ↦ moduleSMulHom (pullbackRingSheaf J Φ O)
      ((pullbackModuleFunctor J Φ O).obj G) ≫ t) hmap).trans
    (moduleSMulHom_comp_moduleSheafFunctor_map g)).trans
      (congrArg (fun t ↦ Limits.prod.map (𝟙 (Sheaf.ringSheaf (pullbackRingSheaf J Φ O))) t ≫
        moduleSMulHom (pullbackRingSheaf J Φ O) ((pullbackModuleFunctor J Φ O).obj G'))
        hmap.symm)
  have nat : Φ.map (Limits.prod.map (𝟙 (Sheaf.ringSheaf O)) h) ≫
        Limits.prodComparison Φ (Sheaf.ringSheaf O) (moduleSheaf O G') =
      Limits.prodComparison Φ (Sheaf.ringSheaf O) (moduleSheaf O G) ≫
        Limits.prod.map (𝟙 (Φ.obj (Sheaf.ringSheaf O))) (Φ.map h) :=
    (Limits.prodComparison_natural Φ (𝟙 (Sheaf.ringSheaf O)) h).trans
      (congrArg (fun t ↦ Limits.prodComparison Φ (Sheaf.ringSheaf O) (moduleSheaf O G) ≫
        Limits.prod.map t (Φ.map h)) (Φ.map_id (Sheaf.ringSheaf O)))
  exact comp_eq_of_map_comp_eq Φ (moduleSMul_map_aux' J Φ O G) (moduleSMul_map_aux' J Φ O G')
    nat key

/-- Transport of sheaves of modules along a faithful functor is faithful: the underlying sheaf
of sets of a transported sheaf of modules is the `Φ`-image of the underlying sheaf of sets of
the original one, so the composite with the forgetful functor to sheaves of sets is
`moduleSheafFunctor O ⋙ Φ`. -/
instance faithful_pullbackModuleFunctor [Φ.Faithful] :
    (pullbackModuleFunctor J Φ O).Faithful := by
  have h : (pullbackModuleFunctor J Φ O ⋙
      moduleSheafFunctor (pullbackRingSheaf J Φ O)).Faithful := by
    rw [show pullbackModuleFunctor J Φ O ⋙ moduleSheafFunctor (pullbackRingSheaf J Φ O) =
      moduleSheafFunctor O ⋙ Φ from rfl]
    infer_instance
  exact Functor.Faithful.of_comp (pullbackModuleFunctor J Φ O)
    (moduleSheafFunctor (pullbackRingSheaf J Φ O))

/-- Transport of sheaves of modules along a fully faithful functor is full. A morphism of
transported sheaves of modules is a morphism of the `Φ`-images of the underlying sheaves of
sets, hence `Φ` of a morphism `h` upstairs; `moduleAddHom_comp_of_map_eq` and
`moduleSMulHom_comp_of_map_eq` say that `h` is additive and `O`-linear, so it is the underlying
morphism of a morphism of sheaves of `O`-modules. -/
instance full_pullbackModuleFunctor [Φ.Full] [Φ.Faithful] :
    (pullbackModuleFunctor J Φ O).Full where
  map_surjective {G G'} g := by
    refine ⟨homEquivSubtype.symm
      ⟨Φ.preimage ((moduleSheafFunctor (pullbackRingSheaf J Φ O)).map g),
        moduleAddHom_comp_of_map_eq Φ O g _ (Φ.map_preimage _),
        moduleSMulHom_comp_of_map_eq Φ O g _ (Φ.map_preimage _)⟩, ?_⟩
    exact hom_ext_moduleSheafFunctor (Φ.map_preimage _)

/-- **The transport half of Stacks 08M3.** Transport of sheaves of modules along a fully
faithful, finite-product-preserving functor between categories of sheaves of sets is fully
faithful. -/
noncomputable def fullyFaithfulPullbackModuleFunctor [Φ.Full] [Φ.Faithful] :
    (pullbackModuleFunctor J Φ O).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPushforward

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww'))) (O : Sheaf J RingCat.{ww})

/-- The direct image of sheaves of modules along a morphism of topoi whose direct image on
sheaves of sets is faithful is faithful. -/
instance faithful_pushforwardModuleFunctor [f.pushforward.Faithful] :
    (pushforwardModuleFunctor f O).Faithful :=
  Stacks.Sheaves.ToposPullback.faithful_pullbackModuleFunctor f.pushforward O

/-- The direct image of sheaves of modules along a morphism of topoi whose direct image on
sheaves of sets is fully faithful is full. -/
instance full_pushforwardModuleFunctor [f.pushforward.Full] [f.pushforward.Faithful] :
    (pushforwardModuleFunctor f O).Full :=
  Stacks.Sheaves.ToposPullback.full_pullbackModuleFunctor f.pushforward O

/-- **The Stacks 03D1 direct image is fully faithful for an embedding of topoi.** If the direct
image of sheaves of sets along `f` is fully faithful, then so is the direct image of sheaves of
modules. This is the half of Stacks 08M3 that concerns the direct image proper, before
restriction of scalars along the structure map. -/
noncomputable def fullyFaithfulPushforwardModuleFunctor
    [f.pushforward.Full] [f.pushforward.Faithful] :
    (pushforwardModuleFunctor f O).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

end Stacks.Sheaves.ToposPushforward

end
