module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageAdjunction

/-!
# Direct image of sheaves of modules versus restriction of scalars

For a morphism of topoi `f` and a morphism `c : O' ⟶ O` of sheaves of rings on the target,
taking the direct image over `O` and restricting scalars along `c` agrees with restricting
scalars along `f⁻¹c` and then taking the direct image over `O'`. The comparison is the
identity on underlying sheaves of sets.

## Main results

* `Stacks.Sheaves.ToposPushforward.ringUnit_naturality`: naturality of the unit
  `O ⟶ f_*f⁻¹O` in the sheaf of rings.
* `Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso`: inverse image
  commutes with restriction of scalars.
* `Stacks.Sheaves.RingedToposModules.directImageModulesCompRestrictScalarsIso`: direct image
  commutes with restriction of scalars.
* `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_restrictScalars_map`: restriction of
  scalars acts on a morphism by the same morphism of underlying sheaves of sets.
* `moduleSheafFunctor_map_directImageModulesRestrictScalarsIso_hom`: the comparison
  `directImageModulesRestrictScalarsIso` is the identity on underlying sheaves of sets.

## Implementation notes

The two module structures are propositionally but not definitionally equal: the pushforward's
scalar action pushes a different morphism, so `moduleSMulObj_restrictScalars` is a genuine
rewrite. The underlying-sheaf equality is therefore assembled from instantiations of abstract
`rfl` lemmas, which the kernel checks cheaply; inlining it at the concrete instance exceeds
the kernel's budget.
-/

@[expose] public section
open CategoryTheory Limits Functor Opposite


/-! ## Naturality of the unit `O ⟶ f_*f⁻¹O` -/

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Sheaf Functor Opposite Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))

/-- The inverse image of a morphism of sheaves of rings along a morphism of topoi. -/
noncomputable abbrev inverseImageRingMap {O O' : Sheaf K RingCat.{ww'}} (c : O ⟶ O') :
    inverseImageRingSheaf f O ⟶ inverseImageRingSheaf f O' :=
  pullbackRingSheafMap J f.inverseImage c

/-- The direct image of a morphism of sheaves of rings along a morphism of topoi. -/
noncomputable def pushforwardRingMap {S S' : Sheaf J RingCat.{ww}} (a : S ⟶ S') :
    pushforwardRingSheaf f S ⟶ pushforwardRingSheaf f S' :=
  pullbackRingSheafMap K f.pushforward a

variable {O O' : Sheaf K RingCat.{ww'}} (c : O ⟶ O')

/-- Naturality of the unit `O ⟶ f_*f⁻¹O` in the sheaf of rings `O`: a morphism of sheaves of
rings followed by the unit of its target is the unit of its source followed by the direct image
of the inverse image of the morphism. -/
lemma ringUnit_naturality :
    c ≫ ringUnit f O' = ringUnit f O ≫ pushforwardRingMap f (inverseImageRingMap f c) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun X ↦ ?_))
  refine RingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  exact congrArg (fun m ↦ (Sheaf.sectionsFunctor K X).map m x)
    (f.adj.unit.naturality ((sheafCompose K (forget RingCat.{ww'})).map c))

end Stacks.Sheaves.ToposPushforward

/-! ## Direct image of sheaves of modules versus restriction of scalars -/

namespace Stacks.Sheaves.RingedToposModules

open CategoryTheory Limits Functor Opposite
open CategoryTheory.Functor CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

section PullbackRestrictScalars

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{ww'})]

/-- Restricting scalars twice is restricting scalars along the composite. -/
lemma restrictScalars_comp {R₁ R₂ R₃ : Sheaf J RingCat.{ww}} (a : R₁ ⟶ R₂) (b : R₂ ⟶ R₃) :
    SheafOfModules.restrictScalars.{ww} b ⋙ SheafOfModules.restrictScalars.{ww} a =
      SheafOfModules.restrictScalars.{ww} (a ≫ b) := rfl

variable [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]

/-- Restriction of scalars does not change the underlying sheaf of sets. -/
lemma moduleSheaf_restrictScalars {R R' : Sheaf J RingCat.{ww}} (a : R ⟶ R')
    (N : SheafOfModules.{ww} R') :
    Sheaf.moduleSheaf R ((SheafOfModules.restrictScalars a).obj N) = Sheaf.moduleSheaf R' N :=
  rfl

variable [J.HasSheafCompose (forget RingCat.{ww})]
  (J) (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {S S' : Sheaf K RingCat.{ww'}} (α : S' ⟶ S) (G : SheafOfModules.{ww'} S)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The inverse image of a sheaf of modules has the same underlying sheaf of sets before and
after restriction of scalars on the source. -/
lemma moduleSheaf_pullbackModuleObj_restrictScalars :
    Sheaf.moduleSheaf (pullbackRingSheaf J Φ S')
        (pullbackModuleObj J Φ S' ((SheafOfModules.restrictScalars α).obj G)) =
      Sheaf.moduleSheaf (pullbackRingSheaf J Φ S) (pullbackModuleObj J Φ S G) := rfl

/-- The identity of the underlying sheaf of sets, read as a morphism from the inverse image of
`G` with its scalars restricted along the inverse image of `α` to the inverse image of `G`
with its scalars restricted along `α`. -/
noncomputable def pullbackModuleObjRestrictScalarsHom :
    (SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α)).obj (pullbackModuleObj J Φ S G) ⟶
      pullbackModuleObj J Φ S' ((SheafOfModules.restrictScalars α).obj G) := by
  refine ofSheafHom (𝟙 _) ?_ ?_
  · intro X x y
    rfl
  · intro X r x
    exact (moduleSMulObj_restrictScalars α G (Φ ⋙ sectionsFunctor J X) r x).symm

/-- The identity of the underlying sheaf of sets, read in the other direction. -/
noncomputable def pullbackModuleObjRestrictScalarsInv :
    pullbackModuleObj J Φ S' ((SheafOfModules.restrictScalars α).obj G) ⟶
      (SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α)).obj
        (pullbackModuleObj J Φ S G) := by
  refine ofSheafHom (𝟙 _) ?_ ?_
  · intro X x y
    rfl
  · intro X r x
    exact moduleSMulObj_restrictScalars α G (Φ ⋙ sectionsFunctor J X) r x

/-- On underlying sheaves of sets, `pullbackModuleObjRestrictScalarsHom` is the identity. -/
@[simp]
lemma moduleSheafFunctor_map_pullbackModuleObjRestrictScalarsHom :
    (Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ S')).map
      (pullbackModuleObjRestrictScalarsHom J Φ α G) = 𝟙 _ := rfl

/-- On underlying sheaves of sets, `pullbackModuleObjRestrictScalarsInv` is the identity. -/
@[simp]
lemma moduleSheafFunctor_map_pullbackModuleObjRestrictScalarsInv :
    (Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ S')).map
      (pullbackModuleObjRestrictScalarsInv J Φ α G) = 𝟙 _ := rfl

/-- **Inverse image commutes with restriction of scalars.** Restricting the scalars of the
inverse image of `G` along the inverse image of `α : S' ⟶ S` gives the inverse image of `G`
whose scalars were restricted along `α`, by an isomorphism which is the identity on underlying
sheaves of sets. -/
noncomputable def pullbackModuleObjRestrictScalarsIso :
    (SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α)).obj (pullbackModuleObj J Φ S G) ≅
      pullbackModuleObj J Φ S' ((SheafOfModules.restrictScalars α).obj G) where
  hom := pullbackModuleObjRestrictScalarsHom J Φ α G
  inv := pullbackModuleObjRestrictScalarsInv J Φ α G
  hom_inv_id := hom_ext_moduleSheafFunctor (Sheaf.hom_ext_sections fun _ _ ↦ rfl)
  inv_hom_id := hom_ext_moduleSheafFunctor (Sheaf.hom_ext_sections fun _ _ ↦ rfl)

/-- The forward morphism of `pullbackModuleObjRestrictScalarsIso` is
`pullbackModuleObjRestrictScalarsHom`. -/
@[simp]
lemma pullbackModuleObjRestrictScalarsIso_hom :
    (pullbackModuleObjRestrictScalarsIso J Φ α G).hom =
      pullbackModuleObjRestrictScalarsHom J Φ α G := rfl

/-- **Inverse image commutes with restriction of scalars**, naturally in the sheaf of
modules. -/
noncomputable def pullbackModuleFunctorRestrictScalarsIso :
    pullbackModuleFunctor J Φ S ⋙
        SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α) ≅
      SheafOfModules.restrictScalars α ⋙ pullbackModuleFunctor J Φ S' :=
  NatIso.ofComponents (fun G ↦ pullbackModuleObjRestrictScalarsIso J Φ α G)
    (fun _ ↦ hom_ext_moduleSheafFunctor (Sheaf.hom_ext_sections fun _ _ ↦ rfl))

/-- The component at `G` of the forward natural transformation of
`pullbackModuleFunctorRestrictScalarsIso` is `pullbackModuleObjRestrictScalarsHom`. -/
@[simp]
lemma pullbackModuleFunctorRestrictScalarsIso_hom_app :
    (pullbackModuleFunctorRestrictScalarsIso J Φ α).hom.app G =
      pullbackModuleObjRestrictScalarsHom J Φ α G :=
  rfl

end PullbackRestrictScalars

section DirectImageRestrictScalars

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  {O O' : Sheaf K RingCat.{w'}} (c : O' ⟶ O)

/-- **Direct image of sheaves of modules commutes with restriction of scalars.** For a
morphism `c : O' ⟶ O` of sheaves of rings on the target, taking the direct image over `O` and
then restricting scalars along `c` agrees with restricting scalars along `f⁻¹c` and then taking
the direct image over `O'`. -/
noncomputable def directImageModulesCompRestrictScalarsIso :
    directImageModules f O ⋙ SheafOfModules.restrictScalars c ≅
      SheafOfModules.restrictScalars (inverseImageRingMap f c) ⋙ directImageModules f O' :=
  eqToIso (((congrArg (fun F ↦ pushforwardModuleFunctor f (inverseImageRingSheaf f O) ⋙ F)
            (restrictScalars_comp c (ringUnit f O))).trans
        (congrArg (fun u ↦ pushforwardModuleFunctor f (inverseImageRingSheaf f O) ⋙
          SheafOfModules.restrictScalars u) (ringUnit_naturality f c))).trans
      (congrArg (fun F ↦ pushforwardModuleFunctor f (inverseImageRingSheaf f O) ⋙ F)
        (restrictScalars_comp (ringUnit f O')
          (pushforwardRingMap f (inverseImageRingMap f c)))).symm) ≪≫
    isoWhiskerRight
      (pullbackModuleFunctorRestrictScalarsIso K f.pushforward (inverseImageRingMap f c))
      (SheafOfModules.restrictScalars (ringUnit f O'))

/-- **Direct image of sheaves of modules commutes with restriction of scalars**, on a single
sheaf of modules. -/
noncomputable abbrev directImageModulesRestrictScalarsIso
    (M : SheafOfModules.{w} (inverseImageRingSheaf f O)) :
    (SheafOfModules.restrictScalars c).obj ((directImageModules f O).obj M) ≅
      (directImageModules f O').obj
        ((SheafOfModules.restrictScalars (inverseImageRingMap f c)).obj M) :=
  (directImageModulesCompRestrictScalarsIso f c).app M

/-- The two readings of the direct image of a sheaf of modules have the very same underlying
sheaf of sets: restriction of scalars does not change it. -/
lemma moduleSheaf_directImageModules_restrictScalars
    (M : SheafOfModules.{w} (inverseImageRingSheaf f O)) :
    Sheaf.moduleSheaf O'
        ((SheafOfModules.restrictScalars c).obj ((directImageModules f O).obj M)) =
      Sheaf.moduleSheaf O' ((directImageModules f O').obj
        ((SheafOfModules.restrictScalars (inverseImageRingMap f c)).obj M)) :=
  ((moduleSheaf_restrictScalars c _).trans
      (moduleSheaf_restrictScalars (ringUnit f O) _)).trans
    (((moduleSheaf_restrictScalars (ringUnit f O') _).trans
        (moduleSheaf_pullbackModuleObj_restrictScalars K f.pushforward
          (inverseImageRingMap f c) M)).symm)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Restriction of scalars acts on a morphism of sheaves of modules by the very same morphism
of underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_restrictScalars_map {R R' : Sheaf J RingCat.{w}} (u : R ⟶ R')
    {M N : SheafOfModules.{w} R'} (k : M ⟶ N) :
    (Sheaf.moduleSheafFunctor R).map ((SheafOfModules.restrictScalars u).map k) =
      (Sheaf.moduleSheafFunctor R').map k :=
  rfl

end DirectImageRestrictScalars

/-! ## The comparison on underlying sheaves of sets -/

section UnderlyingPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  [J.HasSheafCompose (forget RingCat.{ww})]

variable (J) (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {S S' : Sheaf K RingCat.{ww'}} (α : S' ⟶ S) (G : SheafOfModules.{ww'} S)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- Restricting scalars along `u` after the inverse image leaves the underlying sheaf of sets
unchanged, so the two orders of the inverse image and of the restriction along `α` have the
same underlying sheaf of sets. -/
lemma moduleSheaf_restrictScalars_pullbackModuleFunctor_restrictScalars
    {R : Sheaf J RingCat.{ww}} (u : R ⟶ pullbackRingSheaf J Φ S') :
    Sheaf.moduleSheaf R ((SheafOfModules.restrictScalars u).obj
        ((pullbackModuleFunctor J Φ S ⋙
          SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α)).obj G)) =
      Sheaf.moduleSheaf R ((SheafOfModules.restrictScalars u).obj
        ((SheafOfModules.restrictScalars α ⋙ pullbackModuleFunctor J Φ S').obj G)) :=
  (moduleSheaf_restrictScalars u _).trans
    (((moduleSheaf_restrictScalars (pullbackRingSheafMap J Φ α) (pullbackModuleObj J Φ S G)).trans
      (moduleSheaf_pullbackModuleObj_restrictScalars J Φ α G).symm).trans
        (moduleSheaf_restrictScalars u _).symm)

/-- The comparison of the inverse image with restriction of scalars, read after a further
restriction of scalars along `u`, is the identity on underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_restrictScalars_map_pullbackModuleFunctorRestrictScalarsIso
    {R : Sheaf J RingCat.{ww}} (u : R ⟶ pullbackRingSheaf J Φ S') :
    (Sheaf.moduleSheafFunctor R).map ((SheafOfModules.restrictScalars u).map
        ((pullbackModuleFunctorRestrictScalarsIso J Φ α).hom.app G)) =
      eqToHom (moduleSheaf_restrictScalars_pullbackModuleFunctor_restrictScalars J Φ α G u) :=
  (moduleSheafFunctor_map_restrictScalars_map u _).trans
    ((moduleSheafFunctor_map_pullbackModuleObjRestrictScalarsHom J Φ α G).trans
      (eqToHom_refl _ _).symm)

/-- An identification of functors followed by the comparison of the inverse image with
restriction of scalars, whiskered by a restriction of scalars along `u`, is the identity on
underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_eqToIso_trans_pullbackModuleFunctorRestrictScalarsIso_app
    {R : Sheaf J RingCat.{ww}} (u : R ⟶ pullbackRingSheaf J Φ S')
    {P : SheafOfModules.{ww'} S ⥤ SheafOfModules.{ww} R}
    (E : P = (pullbackModuleFunctor J Φ S ⋙
        SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α)) ⋙
      SheafOfModules.restrictScalars u)
    (hP : Sheaf.moduleSheaf R (P.obj G) =
      Sheaf.moduleSheaf R (((SheafOfModules.restrictScalars α ⋙ pullbackModuleFunctor J Φ S') ⋙
        SheafOfModules.restrictScalars u).obj G)) :
    (Sheaf.moduleSheafFunctor R).map
        ((eqToIso E ≪≫ isoWhiskerRight (pullbackModuleFunctorRestrictScalarsIso J Φ α)
          (SheafOfModules.restrictScalars u)).app G).hom = eqToHom hP := by
  have h1 : (Sheaf.moduleSheafFunctor R).map ((eqToHom E).app G) =
      eqToHom (congrArg (Sheaf.moduleSheafFunctor R).obj (Functor.congr_obj E G)) :=
    (congrArg (Sheaf.moduleSheafFunctor R).map (eqToHom_app E G)).trans (eqToHom_map _ _)
  have hd : ((eqToIso E ≪≫ isoWhiskerRight (pullbackModuleFunctorRestrictScalarsIso J Φ α)
          (SheafOfModules.restrictScalars u)).app G).hom =
      (eqToHom E).app G ≫ (SheafOfModules.restrictScalars u).map
        ((pullbackModuleFunctorRestrictScalarsIso J Φ α).hom.app G) := rfl
  rw [hd, Functor.map_comp, h1,
    moduleSheafFunctor_map_restrictScalars_map_pullbackModuleFunctorRestrictScalarsIso,
    eqToHom_trans]

end UnderlyingPullback

section UnderlyingDirectImage

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  {O O' : Sheaf K RingCat.{w'}} (c : O' ⟶ O)

/-- **The comparison of the direct image with restriction of scalars is the identity on
underlying sheaves of sets.** -/
lemma moduleSheafFunctor_map_directImageModulesRestrictScalarsIso_hom
    (M : SheafOfModules.{w} (inverseImageRingSheaf f O)) :
    (Sheaf.moduleSheafFunctor O').map (directImageModulesRestrictScalarsIso f c M).hom =
      eqToHom (moduleSheaf_directImageModules_restrictScalars f c M) :=
  moduleSheafFunctor_map_eqToIso_trans_pullbackModuleFunctorRestrictScalarsIso_app K f.pushforward
    (inverseImageRingMap f c) M (ringUnit f O') _
    (moduleSheaf_directImageModules_restrictScalars f c M)

end UnderlyingDirectImage

end Stacks.Sheaves.RingedToposModules

end
