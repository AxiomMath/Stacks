module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupEssentiallySmall

/-!
# Naturality of `H¹(C, 𝒪^*) = Pic(𝒪)` along a map of structure sheaves

Let `(C, 𝒪)` be a ringed site and `φ : 𝒪 ⟶ 𝒪'` a map of sheaves of rings on the same site. If
`L` is an invertible `𝒪`-module, `L'` an invertible `𝒪'`-module, and `α : L ⟶ L'` a map of
sheaves that is `φ`-semilinear on units and carries local generators of `L` to local generators
of `L'`, then the map `H¹(C, 𝒪^*) ⟶ H¹(C, 𝒪'^*)` induced by `φ` carries the class of `L` to the
class of `L'`, under the identification of Tag 040E.

This is what identifies a map of Picard groups defined through first cohomology of the units
with a map defined on invertible modules: `α` is typically the unit `L ⟶ i_* i^* L` of an
adjunction, and the statement then says that the cohomological map is `L ↦ i^* L`.

## Main results

All in the namespace `Stacks.Cohomology.Torsors.Generators`:

* `sheafH_map_torsorClass_of_generatorMap`: the statement for two generator torsors over a
  ringed site with equal universes.
* `hAddEquiv_h1UnitsAddEquivPicardGroupOfEssentiallySmall_symm_classOf`: on an essentially
  small ringed site, the class of an invertible module, read on the small model, is the class of
  the generator torsor of its restriction.
* `sheafH_map_h1UnitsAddEquivPicardGroupOfEssentiallySmall_symm`: the naturality statement on
  an essentially small ringed site.

## Implementation notes

The map of structure sheaves enters only through the induced map of unit sheaves, which is taken
as a morphism `ψ` together with its formula on sections; this avoids fixing one construction of
the units functor on morphisms, and is satisfied by `rfl` for the units maps of the library.

The second ringed site is `{ X with O := O' }`, with the underlying site of `X`; a ringed site
with these fields, such as a dense restriction of another ringed site along a functor into the
site of `X`, is that structure up to definitional eta.

## References

* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe a w u u₁ v₁

namespace Stacks.Cohomology.Torsors.Generators

/-! ### Generator torsors over a ringed site with equal universes -/

section Small

variable (X : RingedSite.{u, u, u}) (O' : Sheaf X.J CommRingCat.{u})
  [HasSheafify X.J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf X.J AddCommGrpCat.{u})]

/-- **Generator-preserving semilinear maps induce the map on first cohomology of the units.**
Let `φ : 𝒪 ⟶ 𝒪'` be a map of structure sheaves on the site of `X`, `ψ` the induced map of unit
sheaves, and `α` a natural family of maps from the sections of an `𝒪`-module `L` to those of an
`𝒪'`-module `L'` that is `φ`-semilinear for units and carries local generators to local
generators. Then `ψ` carries the cohomology class of a generator torsor of `L` to that of a
generator torsor of `L'`. -/
theorem sheafH_map_torsorClass_of_generatorMap
    (φ : X.O ⟶ O')
    (ψ : unitsAddSheaf X ⟶ unitsAddSheaf { X with O := O' })
    (hψ : ∀ (U : X.Cᵒᵖ) (v : (X.O.obj.obj U : Type u)ˣ),
      Additive.toMul (ψ.hom.app U (Additive.ofMul v)) =
        Units.map (φ.hom.app U).hom.toMonoidHom v)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (L' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (T : GeneratorTorsor X L) (T' : GeneratorTorsor { X with O := O' } L')
    (α : ∀ U : X.Cᵒᵖ, L.val.obj U → L'.val.obj U)
    (hα_restrict : ∀ {U V : X.Cᵒᵖ} (f : U ⟶ V) (s : L.val.obj U),
      α V (L.val.restrictₛₗ f s) = L'.val.restrictₛₗ f (α U s))
    (hα_smul : ∀ (U : X.Cᵒᵖ) (v : (X.O.obj.obj U : Type u)ˣ) (s : L.val.obj U),
      α U (@SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (L.val.obj U) _
          v.val s) =
        @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U) (L'.val.obj U) _
          (Units.map (φ.hom.app U).hom.toMonoidHom v).val (α U s))
    (hα_gen : ∀ (U : X.Cᵒᵖ) (s : GeneratorSections X L U.unop) (V : X.C) (f : V ⟶ U.unop),
      Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj (op V) =>
        r • L'.val.restrictₛₗ f.op (α U s.val))) :
    Sheaf.H.map ψ 1 (torsorIsoClassesEquivH1 (unitsAddSheaf X)
        (Quotient.mk (torsorSetoid (unitsAddSheaf X)) T.torsor)) =
      torsorIsoClassesEquivH1 (unitsAddSheaf { X with O := O' })
        (Quotient.mk (torsorSetoid (unitsAddSheaf { X with O := O' })) T'.torsor) := by
  let g (U : X.Cᵒᵖ) (s : T.torsor.1.presheaf.obj U) : T'.torsor.1.presheaf.obj U :=
    (T'.sectionsEquiv U).symm ⟨α U (T.sectionsEquiv U s).val, hα_gen U (T.sectionsEquiv U s)⟩
  have hg (U : X.Cᵒᵖ) (s : T.torsor.1.presheaf.obj U) :
      (T'.sectionsEquiv U (g U s)).val = α U (T.sectionsEquiv U s).val := by
    simp only [g, Equiv.apply_symm_apply]
  refine torsorIsoClassesEquivH1_naturality ψ T.torsor T'.torsor
    { app := fun U => ↾(g U)
      naturality := ?_ } ?_
  · intro U V f
    ext s
    apply (T'.sectionsEquiv V).injective
    apply Subtype.ext
    change (T'.sectionsEquiv V (g V (T.torsor.1.presheaf.map f s))).val =
      (T'.sectionsEquiv V (T'.torsor.1.presheaf.map f (g U s))).val
    rw [hg, T'.sectionsEquiv_restrict, T.sectionsEquiv_restrict, hα_restrict, hg]
  · intro U h s
    apply (T'.sectionsEquiv U).injective
    apply Subtype.ext
    change (T'.sectionsEquiv U (g U (T.torsor.1.act U (Multiplicative.ofAdd h) s))).val =
      (T'.sectionsEquiv U (T'.torsor.1.act U
        (Multiplicative.ofAdd (ψ.hom.app U h)) (g U s))).val
    have hψh : ψ.hom.app U h = Additive.ofMul
        (Units.map (φ.hom.app U).hom.toMonoidHom (Additive.toMul h)) := by
      rw [← hψ]
      rfl
    rw [hψh]
    refine ((hg U _).trans ((congrArg (α U) (T.sectionsEquiv_smul U (Additive.toMul h) s)).trans
      ((hα_smul U (Additive.toMul h) _).trans ?_))).trans
        (T'.sectionsEquiv_smul U (Units.map (φ.hom.app U).hom.toMonoidHom (Additive.toMul h))
          (g U s)).symm
    rw [hg]

end Small

/-! ### Local generators along an isomorphism -/

/-- **Being a local generator is invariant under restriction along an isomorphism.** If
multiplication by a section `t` over `U` is bijective, so is multiplication by its restriction
along an isomorphism `U ⟶ V` of the opposite site. -/
theorem bijective_smul_map_of_isIso {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    (M : PresheafOfModules.{w} R) {U V : Cᵒᵖ} (g : U ⟶ V) [IsIso g] (t : M.obj U)
    (ht : Function.Bijective (fun r : R.obj U => r • t)) :
    Function.Bijective (fun r : R.obj V => r • M.map g t) := by
  have hR : Function.Bijective (R.map g) := ConcreteCategory.bijective_of_isIso (R.map g)
  have hM : Function.Bijective (fun x : M.obj U => M.map g x) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨fun y => M.map (inv g) y,
      fun x => ?_, fun y => ?_⟩
    · change M.map (inv g) (M.map g x) = x
      rw [← M.map_comp_apply, IsIso.hom_inv_id, M.map_id]
      rfl
    · refine (M.map_comp_apply (inv g) g y).symm.trans ?_
      rw [IsIso.inv_hom_id, M.map_id]
      rfl
  have hcomp : (fun r : R.obj V => r • M.map g t) ∘ (R.map g) =
      (fun x : M.obj U => M.map g x) ∘ (fun r : R.obj U => r • t) := by
    funext r
    exact (M.map_smul g r t).symm
  exact (Function.Bijective.of_comp_iff _ hR).mp (hcomp ▸ hM.comp ht)

/-! ### Essentially small ringed sites -/

section EssentiallySmall

variable (X : RingedSite.{u₁, v₁, w}) [EssentiallySmall.{w} X.C]

/-- **Local generators can be tested on the small model.** If multiplication by the restriction
of a section `s` over `U` is bijective over every arrow into `U` from the image of the small
model, it is bijective over every arrow into `U`. -/
theorem bijective_smul_restrict_of_forall_smallFunctor
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : L.val.obj (op U))
    (hs : ∀ (V : SmallModel.{w} X.C) (f : (RingedSite.smallFunctor X).obj V ⟶ U),
      Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj
          (op ((RingedSite.smallFunctor X).obj V)) => r • L.val.restrictₛₗ f.op s))
    (V : X.C) (f : V ⟶ U) :
    Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
      r • L.val.restrictₛₗ f.op s) := by
  let e := (equivSmallModel.{w} X.C).unitIso.app V
  have h := bijective_smul_map_of_isIso L.val e.hom.op _
    (hs ((equivSmallModel.{w} X.C).functor.obj V) (e.inv ≫ f))
  have hf : L.val.map e.hom.op (L.val.restrictₛₗ (e.inv ≫ f).op s) = L.val.restrictₛₗ f.op s := by
    rw [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.restrictₛₗ_apply,
      ← PresheafOfModules.map_comp_apply]
    exact L.val.congr_map_apply (by rw [← op_comp, ← Category.assoc, e.hom_inv_id,
      Category.id_comp]) s
  rwa [hf] at h

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasExt.{a} (Sheaf X.J AddCommGrpCat.{w})]
  [hE : HasExt.{a} (Sheaf (RingedSite.smallTopology X) AddCommGrpCat.{w})]

/-- **The class of an invertible module, read on the small model.** On an essentially small
locally ringed site, the cohomology class attached to an invertible module `L` by Tag 040E is
carried, by restriction to the small model, to the class of the generator torsor of the
restriction of `L`. -/
theorem hAddEquiv_h1UnitsAddEquivPicardGroupOfEssentiallySmall_symm_classOf
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L) :
    haveI := RingedSite.isEquivalence_sheafPushforward_smallFunctor X
    haveI : HasExt.{a} (Sheaf (smallModelRingedSite X).J AddCommGrpCat.{w}) := hE
    Stacks.Cohomology.DenseSubsite.hAddEquiv (RingedSite.smallTopology X) X.J
        (RingedSite.smallFunctor X) (unitsAddSheaf X) 1
        ((h1UnitsAddEquivPicardGroupOfEssentiallySmall X hX).symm
          (Stacks.SheafOfModules.Picard.classOf X.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L hL)) =
      torsorIsoClassesEquivH1 (unitsAddSheaf (smallModelRingedSite X))
        (Quotient.mk (torsorSetoid (unitsAddSheaf (smallModelRingedSite X)))
          (generatorTorsor (smallModelRingedSite X)
            (RingedSite.isLocallyRinged_denseRestrict (RingedSite.smallTopology X) X
              (RingedSite.smallFunctor X) hX)
            ((RingedSite.denseRestrictModules (RingedSite.smallTopology X) X
              (RingedSite.smallFunctor X)).obj L)
            (RingedSite.isInvertible_denseRestrictModules_obj
              (RingedSite.smallTopology X) X (RingedSite.smallFunctor X) L hL)).torsor) := by
  have := RingedSite.isEquivalence_sheafPushforward_smallFunctor X
  have : HasExt.{a} (Sheaf (smallModelRingedSite X).J AddCommGrpCat.{w}) := hE
  have hX' := RingedSite.isLocallyRinged_denseRestrict (RingedSite.smallTopology X) X
    (RingedSite.smallFunctor X) hX
  have hx := (h1UnitsAddEquivPicardGroupOfEssentiallySmall X hX).apply_symm_apply
    (Stacks.SheafOfModules.Picard.classOf X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L hL)
  change (RingedSite.picardGroupDenseRestrictAddEquiv (RingedSite.smallTopology X) X
      (RingedSite.smallFunctor X)).symm ((h1UnitsAddEquivPicardGroup (smallModelRingedSite X) hX')
        (Stacks.Cohomology.DenseSubsite.hAddEquiv (RingedSite.smallTopology X) X.J
          (RingedSite.smallFunctor X) (unitsAddSheaf X) 1
          ((h1UnitsAddEquivPicardGroupOfEssentiallySmall X hX).symm
            (Stacks.SheafOfModules.Picard.classOf X.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L hL)))) = _ at hx
  rw [AddEquiv.symm_apply_eq] at hx
  have hx2 := hx.trans (RingedSite.picardGroupDenseRestrictAddEquiv_classOf
    (RingedSite.smallTopology X) X (RingedSite.smallFunctor X) L hL)
  exact ((AddEquiv.symm_apply_eq _).mpr hx2.symm).symm.trans
    (h1UnitsAddEquivPicardGroup_symm_classOf (smallModelRingedSite X) hX' _ _)

/-- **Naturality of Tag 040E along a map of structure sheaves, on an essentially small site.**
Let `φ : 𝒪 ⟶ 𝒪'` be a map of structure sheaves on an essentially small site, `ψ` the induced map
of unit sheaves, `L` an invertible `𝒪`-module and `L'` an invertible `𝒪'`-module, and `α` a
natural family of maps from the sections of `L` to those of `L'` that is `φ`-semilinear for units
and carries local generators to local generators. Then `ψ` carries the class of `L` in
`H¹(C, 𝒪^*)` to the class of `L'` in `H¹(C, 𝒪'^*)`. -/
theorem sheafH_map_h1UnitsAddEquivPicardGroupOfEssentiallySmall_symm
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X) (O' : Sheaf X.J CommRingCat.{w})
    (hY : AlgebraicGeometry.RingedSite.IsLocallyRinged { X with O := O' })
    (φ : X.O ⟶ O')
    (ψ : unitsAddSheaf X ⟶ unitsAddSheaf { X with O := O' })
    (hψ : ∀ (U : X.Cᵒᵖ) (v : (X.O.obj.obj U : Type w)ˣ),
      Additive.toMul (ψ.hom.app U (Additive.ofMul v)) =
        Units.map (φ.hom.app U).hom.toMonoidHom v)
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L)
    (L' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hL' : Stacks.SheafOfModules.IsInvertible O'.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf O').2 L')
    (α : ∀ U : X.Cᵒᵖ, L.val.obj U → L'.val.obj U)
    (hα_restrict : ∀ {U V : X.Cᵒᵖ} (f : U ⟶ V) (s : L.val.obj U),
      α V (L.val.restrictₛₗ f s) = L'.val.restrictₛₗ f (α U s))
    (hα_smul : ∀ (U : X.Cᵒᵖ) (v : (X.O.obj.obj U : Type w)ˣ) (s : L.val.obj U),
      α U (@SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (L.val.obj U) _
          v.val s) =
        @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U) (L'.val.obj U) _
          (Units.map (φ.hom.app U).hom.toMonoidHom v).val (α U s))
    (hα_gen : ∀ (U : X.Cᵒᵖ) (s : L.val.obj U),
      (∀ (V : X.C) (f : V ⟶ U.unop),
        Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
          r • L.val.restrictₛₗ f.op s)) →
      ∀ (V : X.C) (f : V ⟶ U.unop),
        Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj (op V) =>
          r • L'.val.restrictₛₗ f.op (α U s))) :
    letI := picardGroupAddCommGroup { X with O := O' }
    Sheaf.H.map ψ 1 ((h1UnitsAddEquivPicardGroupOfEssentiallySmall X hX).symm
        (Stacks.SheafOfModules.Picard.classOf X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L hL)) =
      (h1UnitsAddEquivPicardGroupOfEssentiallySmall { X with O := O' } hY).symm
        (Stacks.SheafOfModules.Picard.classOf O'.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf O').2 L' hL') := by
  have := RingedSite.isEquivalence_sheafPushforward_smallFunctor X
  have : HasExt.{a} (Sheaf (smallModelRingedSite X).J AddCommGrpCat.{w}) := hE
  let G := RingedSite.smallFunctor X
  apply (Stacks.Cohomology.DenseSubsite.hAddEquiv (RingedSite.smallTopology X) X.J G
    (unitsAddSheaf { X with O := O' }) 1).injective
  rw [Stacks.Cohomology.DenseSubsite.hAddEquiv_map]
  refine ((congrArg _ (hAddEquiv_h1UnitsAddEquivPicardGroupOfEssentiallySmall_symm_classOf
    X hX L hL)).trans ?_).trans
      (hAddEquiv_h1UnitsAddEquivPicardGroupOfEssentiallySmall_symm_classOf
        { X with O := O' } hY L' hL').symm
  refine sheafH_map_torsorClass_of_generatorMap (smallModelRingedSite X)
    (smallModelRingedSite { X with O := O' }).O
    ((G.sheafPushforwardContinuous CommRingCat.{w} (RingedSite.smallTopology X) X.J).map φ)
    ((G.sheafPushforwardContinuous AddCommGrpCat.{w} (RingedSite.smallTopology X) X.J).map ψ)
    (fun U v => hψ (G.op.obj U) v) _ _ _ _ (fun U => α (G.op.obj U))
    (fun f s => hα_restrict (G.op.map f) s) (fun U v s => hα_smul (G.op.obj U) v s) ?_
  intro U s V f
  have hs : ∀ (W : X.C) (g : W ⟶ G.obj U.unop),
      Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W) =>
        r • L.val.restrictₛₗ g.op s.val) := by
    refine bijective_smul_restrict_of_forall_smallFunctor X L (G.obj U.unop) s.val fun W g => ?_
    rw [← G.map_preimage g]
    exact s.property W (G.preimage g)
  exact hα_gen (G.op.obj U) s.val hs (G.obj V) (G.map f)

end EssentiallySmall

end Stacks.Cohomology.Torsors.Generators

end
