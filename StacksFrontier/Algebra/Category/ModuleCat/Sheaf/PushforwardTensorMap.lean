module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialSurjectivity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAnnihilation
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Modules.ProjectionFormula
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical map `F ⊗ f_*G ⟶ f_*(f^*F ⊗ G)` for a morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, let `F` be a sheaf of
`O_D`-modules and let `G` be a sheaf of `O_C`-modules. There is a canonical morphism

`F ⊗_{O_D} f_*G ⟶ f_*(f^*F ⊗_{O_C} G)`

of sheaves of `O_D`-modules, namely the adjoint transpose of

`f^*(F ⊗_{O_D} f_*G) = f^*F ⊗_{O_C} f^*f_*G ⟶ f^*F ⊗_{O_C} G`,

where the equality is the comparison of Stacks 03EL and the second map is the identity of `f^*F`
tensored with the counit `f^*f_*G ⟶ G` of the adjunction of Stacks 03D7.

This file builds that morphism and records when it is invertible: it is the unit of the
adjunction at `F ⊗_{O_D} f_*G` followed by the direct image of an isomorphism, so it is an
isomorphism as soon as the counit is invertible at `G` and the unit is invertible at
`F ⊗_{O_D} f_*G`. Both conditions hold for every `F` and `G` when `f` is a closed immersion of
topoi with locally surjective structure map, which is the situation of Stacks 04G0.

## Main definitions

* `Stacks.ProjectionFormula.adjunctionTensorMapSnd`: the abstract construction, for an adjunction
  `L ⊣ R` between categories equipped with bifunctors `A` and `B` and an oplax comparison
  `α : A ⋙ L ⟶ L.prod L ⋙ B`; it is `CategoryTheory.adjunctionTensorMap` with the
  counit in the *second* tensor factor rather than the first.
* `Stacks.SheafOfModules.pushforwardTensorMap`: the morphism displayed above, for a morphism of
  ringed topoi.

## Main results

* `Stacks.ProjectionFormula.adjunctionTensorMapSnd_natural` and
  `Stacks.SheafOfModules.pushforwardTensorMap_natural`: naturality in both module arguments.
* `Stacks.ProjectionFormula.adjunctionTensorMapSnd_unit` and
  `Stacks.SheafOfModules.pushforwardTensorMap_unit`: tensoring the adjunction unit on the left and
  then applying the map is the adjoint transpose of the comparison `α`. This identity pins the
  construction down.
* `Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd` and
  `Stacks.SheafOfModules.isIso_pushforwardTensorMap`: the map is an isomorphism as soon as the
  comparison, the counit at `G` and the unit at the source are.
* `Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isClosedImmersion`: the map is an
  isomorphism for *every* `F` and `G` when the underlying morphism of topoi is a closed immersion
  in the sense of Stacks 08M0 and the structure map is locally surjective.

## Implementation notes

`CategoryTheory.adjunctionTensorMap`, already in this repository, is the same
construction with the two tensor factors interchanged: it produces
`R G ⊗ H ⟶ R (G ⊗ L H)`, which is the shape of the projection formula of Stacks 0FZE. The shape
needed here is `H ⊗ R G ⟶ R (L H ⊗ G)`, which is the shape in which Stacks 04G0 and the
closed-immersion lemmas state their canonical map. The two differ by the braiding of the tensor
product and are *not* the same morphism between the same objects, so the second one is
constructed rather than obtained from the first; its three identities are proved by the same
arguments, with the two factors exchanged.

Only the oplax direction of the Stacks 03EL comparison is used in the construction, so
`pushforwardTensorMap` would exist for any natural transformation
`α : (- ⊗ -) ⋙ f^* ⟶ (f^* × f^*) ⋙ (- ⊗ -)`; that the comparison of Stacks 03EL is invertible
enters only in the isomorphism criterion.

The closed-immersion statement is proved over the *two*-field morphism of ringed topoi of
Stacks 01D3 part (2), `AlgebraicGeometry.RingedToposHom`, rather than over the four-field datum
that the canonical map itself is built from. Both inputs it needs — the full-faithfulness half of
Stacks 08M3 (`Stacks.ToposBridge.fullyFaithfulPushforwardModules`) and its essential-image half
(`Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_isClosedImmersion`)
— are stated for `AlgebraicGeometry.RingedToposHom.pushforwardModules`, the direct image of
Stacks 03D1 followed by restriction of scalars along the direct-image form of the structure map;
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIso` carries them over to the direct image the
Stacks 03D7 adjunction is the adjunction of. The two forms of the structure map being adjunct, a
four-field datum is no more general, and `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`
is how a statement about one becomes a statement about the other.

The hypothesis of Stacks 08M0 forces the sections of the two topoi into the same universe, so the
closed-immersion section works at a single section universe, where the rest of the file keeps the
two independent.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 08M0](https://stacks.math.columbia.edu/tag/08M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open scoped CategoryTheory.Prod

namespace Stacks.ProjectionFormula

section Abstract

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- The projection-formula map of an adjunction `L ⊣ R` together with bifunctors `A` on `C`,
`B` on `D` and a comparison `α : A ⋙ L ⟶ L.prod L ⋙ B`, with the counit in the *second* tensor
factor: the adjoint transpose of

`L (A (H, R G)) ⟶ B (L H, L R G) ⟶ B (L H, G)`,

the first map being `α` and the second the identity of `L H` tensored with the counit at `G`.

`CategoryTheory.adjunctionTensorMap` is the same construction with the counit in the
first factor. -/
def adjunctionTensorMapSnd (H : C) (G : D) :
    A.obj (H, R.obj G) ⟶ R.obj (B.obj (L.obj H, G)) :=
  adj.homEquiv _ _ (α.app (H, R.obj G) ≫ B.map (𝟙 (L.obj H) ×ₘ adj.counit.app G))

/-- Transposing back a map `A (a, b) ≫ adjunctionTensorMapSnd` gives `α` followed by `B (L a, b♭)`,
where `b♭` is the transpose of `b`. -/
private lemma homEquiv_symm_map_comp_adjunctionTensorMapSnd {H H' : C} {X : C} {G' : D}
    (a : H ⟶ H') (b : X ⟶ R.obj G') :
    (adj.homEquiv _ _).symm (A.map (a ×ₘ b) ≫ adjunctionTensorMapSnd adj A B α H' G') =
      α.app (H, X) ≫ B.map (L.map a ×ₘ (adj.homEquiv _ _).symm b) := by
  unfold adjunctionTensorMapSnd
  rw [Adjunction.homEquiv_naturality_left_symm]
  simp only [Functor.comp_obj, Functor.prod_obj, Equiv.symm_apply_apply]
  have ha := α.naturality (a ×ₘ b)
  change L.map (A.map (a ×ₘ b)) ≫ α.app (H', R.obj G') =
    α.app (H, X) ≫ B.map (L.map a ×ₘ L.map b) at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp, Adjunction.homEquiv_counit]
  congr 2
  ext <;> simp

/-- The projection-formula map with the counit in the second factor is natural in both
arguments. -/
lemma adjunctionTensorMapSnd_natural {H H' : C} {G G' : D} (k : H ⟶ H') (g : G ⟶ G') :
    A.map (k ×ₘ R.map g) ≫ adjunctionTensorMapSnd adj A B α H' G' =
      adjunctionTensorMapSnd adj A B α H G ≫ R.map (B.map (L.map k ×ₘ g)) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_symm_map_comp_adjunctionTensorMapSnd, Adjunction.homEquiv_naturality_right_symm]
  unfold adjunctionTensorMapSnd
  simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Category.assoc,
    ← Functor.map_comp]
  congr 2
  ext
  · simp
  · exact adj.counit.naturality g

/-- Tensoring the unit of the adjunction on the left and then applying the projection-formula map
with the counit in the second factor is the adjoint transpose of the comparison `α`. This identity
pins the construction down. -/
lemma adjunctionTensorMapSnd_unit (H G : C) :
    A.map (𝟙 H ×ₘ adj.unit.app G) ≫ adjunctionTensorMapSnd adj A B α H (L.obj G) =
      adj.homEquiv _ _ (α.app (H, G)) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_symm_map_comp_adjunctionTensorMapSnd]
  simp [← CategoryTheory.prod_id]

/-- **The projection-formula map with the counit in the second factor is an isomorphism** as soon
as the comparison `α` is invertible at `(H, R G)`, the counit is invertible at `G` and the unit is
invertible at `A (H, R G)`.

Indeed the map is, by `CategoryTheory.Adjunction.homEquiv_unit`, the unit at `A (H, R G)` followed
by `R` applied to the composite of `α` with the counit in the second factor. -/
lemma isIso_adjunctionTensorMapSnd (H : C) (G : D)
    (hα : IsIso (α.app (H, R.obj G))) (hε : IsIso (adj.counit.app G))
    (hη : IsIso (adj.unit.app (A.obj (H, R.obj G)))) :
    IsIso (adjunctionTensorMapSnd adj A B α H G) := by
  have := hα
  have := hη
  have := hε
  have : IsIso (𝟙 (L.obj H) ×ₘ adj.counit.app G) := by
    refine ⟨⟨𝟙 (L.obj H) ×ₘ inv (adj.counit.app G), ?_, ?_⟩⟩ <;> ext <;> simp
  rw [adjunctionTensorMapSnd, Adjunction.homEquiv_unit]
  infer_instance

end Abstract

end Stacks.ProjectionFormula

namespace Stacks.SheafOfModules

universe w w' v u v' u'

section RingedTopos

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : _root_.Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **The canonical morphism `F ⊗_{O_D} f_*G ⟶ f_*(f^*F ⊗_{O_C} G)`** for a morphism of ringed
topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)`, a sheaf of `O_D`-modules `F` and a sheaf of
`O_C`-modules `G`.

It is the adjoint transpose, along the adjunction `f^* ⊣ f_*` of Stacks 03D7, of the comparison
`f^*(F ⊗ f_*G) ⟶ f^*F ⊗ f^*f_*G` of Stacks 03EL followed by the identity of `f^*F` tensored with
the counit `f^*f_*G ⟶ G`. -/
def pushforwardTensorMap (F : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj F).obj ((pushforwardModules f).obj G) ⟶
      (pushforwardModules f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj ((f.pullbackModules).obj F)).obj G) :=
  Stacks.ProjectionFormula.adjunctionTensorMapSnd (pullbackAdjPushforwardModules f)
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))) ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O)))
    (pullbackTensorIso f).hom F G

/-- The canonical morphism `F ⊗ f_*G ⟶ f_*(f^*F ⊗ G)` is the abstract projection-formula map of
the adjunction of Stacks 03D7 and the comparison of Stacks 03EL. -/
lemma pushforwardTensorMap_eq (F : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    pushforwardTensorMap f F G =
      Stacks.ProjectionFormula.adjunctionTensorMapSnd (pullbackAdjPushforwardModules f)
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))) ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O)))
        (pullbackTensorIso f).hom F G :=
  rfl

/-- The canonical morphism `F ⊗ f_*G ⟶ f_*(f^*F ⊗ G)` is natural in both module arguments. -/
@[reassoc]
lemma pushforwardTensorMap_natural
    {F F' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    {G G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (k : F ⟶ F') (g : G ⟶ G') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map (k ×ₘ (pushforwardModules f).map g).1).app
        _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj _).map (k ×ₘ (pushforwardModules f).map
          g).2) ≫
        pushforwardTensorMap f F' G' =
      pushforwardTensorMap f F G ≫ (pushforwardModules f).map
        ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map ((f.pullbackModules).map k ×ₘ
            g).1).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj _).map ((f.pullbackModules).map k ×ₘ
          g).2)) :=
  Stacks.ProjectionFormula.adjunctionTensorMapSnd_natural (pullbackAdjPushforwardModules f)
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))) ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O)))
    (pullbackTensorIso f).hom k g

/-- Tensoring the unit `G ⟶ f_*f^*G` of the adjunction of Stacks 03D7 on the left and then
applying the canonical morphism is the adjoint transpose of the comparison of Stacks 03EL. -/
@[reassoc]
lemma pushforwardTensorMap_unit
    (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map (𝟙 F ×ₘ (pullbackAdjPushforwardModules
        f).unit.app G).1).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj _).map (𝟙 F ×ₘ
          (pullbackAdjPushforwardModules f).unit.app G).2) ≫
        pushforwardTensorMap f F ((f.pullbackModules).obj G) =
      (pullbackAdjPushforwardModules f).homEquiv _ _ ((pullbackTensorIso f).hom.app (F, G)) :=
  Stacks.ProjectionFormula.adjunctionTensorMapSnd_unit (pullbackAdjPushforwardModules f)
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))) ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O)))
    (pullbackTensorIso f).hom F G

/-- **The canonical morphism `F ⊗ f_*G ⟶ f_*(f^*F ⊗ G)` is an isomorphism** as soon as the counit
of the adjunction of Stacks 03D7 is invertible at `G` and its unit is invertible at `F ⊗ f_*G`.

The comparison of Stacks 03EL is invertible, so these are the only two conditions: the canonical
morphism is the unit at `F ⊗ f_*G` followed by the direct image of an isomorphism. -/
theorem isIso_pushforwardTensorMap
    (F : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hε : IsIso ((pullbackAdjPushforwardModules f).counit.app G))
    (hη : IsIso ((pullbackAdjPushforwardModules f).unit.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj F).obj ((pushforwardModules f).obj G))))
          :
    IsIso (pushforwardTensorMap f F G) :=
  Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd (pullbackAdjPushforwardModules f)
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))) ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O)))
    (pullbackTensorIso f).hom F G
    (NatIso.isIso_app_of_isIso (pullbackTensorIso f).hom (F, (pushforwardModules f).obj G)) hε hη

end RingedTopos

section ClosedImmersion

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  (f : _root_.AlgebraicGeometry.RingedToposHom X Y)

/-- The structure map of a morphism of ringed topoi stays locally surjective after commutativity
is forgotten: local surjectivity of a morphism of sheaves valued in a concrete category is that of
the underlying morphism of sheaves of sets, and the two maps have the same underlying morphism. -/
theorem isLocallySurjective_structureRingMap (hφ : Sheaf.IsLocallySurjective f.fSharp) :
    Sheaf.IsLocallySurjective f.structureRingMap := by
  have h : Presheaf.IsLocallySurjective Y.J f.fSharp.hom := hφ
  rw [Presheaf.isLocallySurjective_iff_whisker_forget] at h
  change Presheaf.IsLocallySurjective _ _
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  exact h

/-- The sectionwise kernel of the structure map is a sheaf of ideals: a section of `O_D` over `U`
killed by `f♯` stays killed by `f♯` after restriction along any `U ⟶ V`. -/
theorem map_mem_ker_structureRingMap {V W : Y.Cᵒᵖ} (g : V ⟶ W)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V)
    (ha : a ∈ RingHom.ker (f.structureRingMap.hom.app V).hom) :
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g a ∈
      RingHom.ker (f.structureRingMap.hom.app W).hom := by
  rw [RingHom.mem_ker] at ha ⊢
  have hnat := ConcreteCategory.congr_hom (f.structureRingMap.hom.naturality g) a
  simp only [CategoryTheory.comp_apply] at hnat
  rw [hnat, ha, map_zero]

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- **The kernel of the structure map annihilates a direct image.** The scalars of `f_*G` act
through `f♯`, so a section of `O_D` over `U` that `f♯` kills annihilates every section of `f_*G`
over `U`.

This is the forward half of Stacks 08M3, read for the direct image of
`Stacks.Sheaves.RingedToposModules.pushforwardModules`, which restricts scalars along the
inverse-image form of the structure map before pushing forward rather than after. -/
theorem smul_pushforwardModules_eq_zero
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (V : Y.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V)
    (ha : a ∈ RingHom.ker (f.structureRingMap.hom.app V).hom)
    (m : ((pushforwardModules f.toRingedToposModulesHom).obj G).val.obj V) :
    a • m = 0 :=
  Stacks.Sheaves.PushforwardEssentialImage.smul_eq_zero_of_iso
    (f.pushforwardModulesIso.symm.app G) V a
    (fun x => Stacks.Sheaves.PushforwardEssentialImage.smul_restrictScalars_eq_zero
      f.structureRingMap _ V a ha x) m

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The full-faithfulness half of Stacks 08M3** for the direct image of modules that the
Stacks 03D7 adjunction is the adjunction of: it is fully faithful as soon as the direct image on
sheaves of sets is and the structure map is locally surjective.

`Stacks.ToposBridge.fullyFaithfulPushforwardModules` is the statement for
`AlgebraicGeometry.RingedToposHom.pushforwardModules`; full faithfulness transfers along
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIso`. -/
def fullyFaithfulPushforwardModulesOfIsEmbedding
    (hemb : MorphismOfTopoi.IsEmbedding f.toToposHom)
    (hφ : Sheaf.IsLocallySurjective f.fSharp) :
    (pushforwardModules f.toRingedToposModulesHom).FullyFaithful :=
  (Stacks.ToposBridge.fullyFaithfulPushforwardModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f.structureRingMap hemb.fullyFaithful
      (isLocallySurjective_structureRingMap f hφ)).ofIso f.pushforwardModulesIso.symm

/-- **The unit of the Stacks 03D7 adjunction is invertible at `F ⊗_{O_D} f_*G`** when the
underlying morphism of topoi is a closed immersion and the structure map is locally surjective.

The unit is invertible exactly where its source lies in the essential image of the direct image of
modules, and by the essential-image half of Stacks 08M3 that happens exactly where the kernel of
`f♯` annihilates the source. It annihilates `f_*G` over every object, by
`smul_pushforwardModules_eq_zero` and `map_mem_ker_structureRingMap`, hence it annihilates the
tensor product `F ⊗_{O_D} f_*G` by `Stacks.SheafOfModules.smul_tensorSheafBifunctor_eq_zero`. -/
theorem isIso_unit_app_tensorPushforward
    (hfc : MorphismOfTopoi.IsClosedImmersion f.toToposHom)
    (hφ : Sheaf.IsLocallySurjective f.fSharp)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsIso ((pullbackAdjPushforwardModules f.toRingedToposModulesHom).unit.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj F).obj ((pushforwardModules
          f.toRingedToposModulesHom).obj G))) := by
  have hls := isLocallySurjective_structureRingMap f hφ
  have hff := fullyFaithfulPushforwardModulesOfIsEmbedding f hfc.1 hφ
  have := hff.full
  have := hff.faithful
  refine (pullbackAdjPushforwardModules
    f.toRingedToposModulesHom).isIso_unit_app_iff_mem_essImage.mpr ?_
  refine Functor.essImage.ofNatIso f.pushforwardModulesIso.symm
    ((Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_isClosedImmersion
      f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) hfc f.structureRingMap _).mpr ?_)
  intro V a ha m
  exact smul_tensorSheafBifunctor_eq_zero Y.J F
    ((pushforwardModules f.toRingedToposModulesHom).obj G) V a
    (fun g y => smul_pushforwardModules_eq_zero f G _ _
      (map_mem_ker_structureRingMap f g a ha) y) m

/-- **The canonical morphism `F ⊗ f_*G ⟶ f_*(f^*F ⊗ G)` is an isomorphism for every `F` and `G`**
when the underlying morphism of topoi is a closed immersion in the sense of Stacks 08M0 and the
structure map `f♯` is locally surjective. No hypothesis on `F` or `G` enters.

Both conditions of `Stacks.SheafOfModules.isIso_pushforwardTensorMap` come from Stacks 08M3: the
counit is invertible because the direct image of modules is fully faithful, and the unit is
invertible at `F ⊗_{O_D} f_*G` because the kernel of `f♯` annihilates that tensor product. -/
@[sga "4 V 1.3.2" "special case"]
theorem isIso_pushforwardTensorMap_of_isClosedImmersion
    (hfc : MorphismOfTopoi.IsClosedImmersion f.toToposHom)
    (hφ : Sheaf.IsLocallySurjective f.fSharp)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsIso (pushforwardTensorMap f.toRingedToposModulesHom F G) :=
  have hff := fullyFaithfulPushforwardModulesOfIsEmbedding f hfc.1 hφ
  have := hff.full
  have := hff.faithful
  isIso_pushforwardTensorMap f.toRingedToposModulesHom F G inferInstance
    (isIso_unit_app_tensorPushforward f hfc hφ F G)

end ClosedImmersion

end Stacks.SheafOfModules

end
