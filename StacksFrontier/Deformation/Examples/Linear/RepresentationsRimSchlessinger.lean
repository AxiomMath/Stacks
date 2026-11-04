module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Linear.FiniteProjectiveRimSchlessinger
public import StacksFrontier.Deformation.Examples.Linear.RepresentationsCofibered
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldComparison
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransport

/-!
# Representations of a group satisfy the Rim–Schlessinger condition

Finite projective representations of a group over Artinian local algebras satisfy condition
(RS). The patch is the one for the underlying modules: forgetting the action lands in the
category of finite projective modules, which satisfies (RS) by Stacks 0DVP, and the action
transports to the patched module because the patched module is a limit upstairs and the
action is a family of automorphisms over the identity of the base.

Consequently the deformations of a finite-dimensional representation over the residue field
form a deformation category.

## Main results

* `Deformation.Examples.FiniteProjectiveRepresentation.satisfiesRS_projection`: condition (RS)
  for the category of finite projective representations.
* `Deformation.Examples.FiniteProjectiveRepresentation.isDeformationCategory_deformationCategory`:
  the deformations of a fixed residual representation form a deformation category.

## Implementation notes

The category of finite projective modules is presented here as the category of finite
projective representations of the trivial group, so that forgetting the action is a functor
between two instances of one construction; `moduleFamily` records that presentation as a
`FiniteProjectiveModule.Family`, which is what Stacks 0DVP is stated for.

Condition (RS) for the modules is available with the residue field in the same universe as the
base algebras, while a representation may have its base algebras in a smaller universe than
its module. `changeResidueBase` and `changeResidueModules` move the residue field into the
universe of the base algebras along an algebra equivalence; they are full, faithful and
essentially surjective, which is what transports a pullback square back.

## References

* [Stacks Project, Tag 0DVS](https://stacks.math.columbia.edu/tag/0DVS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation.Examples.FiniteProjectiveRepresentation

universe u v w m

/-- A finite projective module read as a representation of the trivial group. -/
private abbrev trivialRepresentation {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (X : FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k)) :
    FiniteProjectiveRepresentation.{u, v, w, m} Λ k PUnit.{1} where
  base := X.base
  carrier := X.carrier
  action := 1

/-- The category structure on finite projective modules obtained from the representations of
the trivial group. -/
private abbrev moduleCategory {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k] :
    Category (FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k)) where
  Hom X Y := trivialRepresentation X ⟶ trivialRepresentation Y
  id X := 𝟙 (trivialRepresentation X)
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

attribute [local instance] moduleCategory

/-- The projection of that category to the base algebras. -/
private abbrev moduleProjection {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k] :
    FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k) ⥤
      ArtinianLocalAlgCat.{u, v, w} Λ k where
  obj X := X.base
  map f := f.base

private lemma module_comp_base {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k]
    {X Y Z : FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k)}
    (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base := rfl

private lemma module_id_base {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (X : FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k)) :
    (𝟙 X : X ⟶ X).base = 𝟙 X.base := rfl

attribute [local simp] module_comp_base module_id_base

/-- Its morphisms are the base-change morphisms of finite projective modules. -/
private noncomputable def moduleHomEquiv {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (X Y : FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k)) :
    (X ⟶ Y) ≃ FiniteProjectiveModule.Hom X Y where
  toFun f := {
    base := f.base
    linear := { f.map with map_smul' := f.map_smul }
    baseChange := by
      let : Algebra X.base Y.base := f.base.hom.toAlgebra
      let : Module X.base Y.carrier := Module.compHom Y.carrier f.base.hom.toRingHom
      let : IsScalarTower X.base Y.base Y.carrier :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      exact ⟨f.isBaseChange.equiv, fun x => by
        rw [f.isBaseChange.equiv_tmul]; exact one_smul _ _⟩ }
  invFun f := {
    base := f.base
    map := f.linear.toAddMonoidHom
    map_smul := f.linear.map_smulₛₗ
    equivariant := fun _ _ => rfl
    isBaseChange := by
      let : Algebra X.base Y.base := f.base.hom.toAlgebra
      let : Module X.base Y.carrier := Module.compHom Y.carrier f.base.hom.toRingHom
      let : IsScalarTower X.base Y.base Y.carrier :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      obtain ⟨e, he⟩ := f.baseChange
      exact IsBaseChange.of_equiv e he }
  left_inv f := FiniteProjectiveRepresentation.Hom.ext rfl rfl
  right_inv f := FiniteProjectiveModule.Hom.ext_of_base_eq _ _ rfl (fun _ => rfl)

/-- The presentation of the finite projective modules as a `Family`, so that Stacks 0DVP
applies to it. -/
private noncomputable def moduleFamily {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k] :
    FiniteProjectiveModule.Family.{u, w, m} (Λ := Λ) (k := k) where
  category := moduleCategory
  homEquiv := moduleHomEquiv
  id_base _ := rfl
  id_linear _ _ := rfl
  comp_base _ _ := rfl
  comp_linear _ _ _ := rfl
  projection := moduleProjection
  projection_obj _ := rfl
  projection_map _ := by change 𝟙 _ ≫ _ ≫ 𝟙 _ = _; simp; rfl

/-- Condition (RS) for the finite projective modules, in this presentation. -/
private theorem moduleProjection_satisfiesRS {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k] :
    SatisfiesRS (moduleProjection.{u, w, w, m} (Λ := Λ) (k := k)) :=
  FiniteProjectiveModule.Family.satisfiesRS_projection moduleFamily

/-- Forgetting the action of a finite projective representation. -/
private abbrev forgetAction {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] :
    FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ ⥤
      FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k) where
  obj X := { base := X.base, carrier := X.carrier }
  map f := {
    base := f.base
    map := f.map
    map_smul := f.map_smul
    equivariant := fun _ _ => rfl
    isBaseChange := f.isBaseChange }

/-- The action of a group element, read as an endomorphism of the underlying module over the
identity of the base algebra. -/
private abbrev actionEnd {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (X : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ) (γ : Γ) :
    End (forgetAction.obj X) where
  base := 𝟙 X.base
  map := (X.action γ).toAddMonoidHom
  map_smul := (X.action γ).map_smul
  equivariant := fun _ _ => rfl
  isBaseChange := by
    let e : X.carrier ≃ₗ[X.base] X.carrier := {
      toLinearMap := X.action γ
      invFun := X.action γ⁻¹
      left_inv := fun x => by
        change (X.action γ⁻¹ * X.action γ) x = x
        rw [← map_mul, inv_mul_cancel, map_one]; rfl
      right_inv := fun x => by
        change (X.action γ * X.action γ⁻¹) x = x
        rw [← map_mul, mul_inv_cancel, map_one]; rfl }
    exact IsBaseChange.ofEquiv e

private lemma actionEnd_one {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (X : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ) :
    actionEnd X 1 = 𝟙 (forgetAction.obj X) := by
  refine FiniteProjectiveRepresentation.Hom.ext ?_ ?_
  · show 𝟙 _ = _; simp
  exact congrArg LinearMap.toAddMonoidHom (map_one X.action)

private lemma actionEnd_mul {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (X : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ) (γ δ : Γ) :
    actionEnd X (γ * δ) = actionEnd X δ ≫ actionEnd X γ := by
  refine FiniteProjectiveRepresentation.Hom.ext ?_ ?_
  · show 𝟙 _ = _; simp
  exact congrArg LinearMap.toAddMonoidHom (map_mul X.action γ δ)

private lemma actionEnd_naturality {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    {X Y : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ} (f : X ⟶ Y) (γ : Γ) :
    actionEnd X γ ≫ forgetAction.map f = forgetAction.map f ≫ actionEnd Y γ := by
  refine FiniteProjectiveRepresentation.Hom.ext ?_ ?_
  · show 𝟙 _ ≫ f.base = f.base ≫ 𝟙 _; simp
  ext x
  exact f.equivariant γ x

/-- Morphisms of representations are determined by their underlying module morphisms. -/
private lemma forgetAction_map_injective {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    {X Y : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ} {f g : X ⟶ Y}
    (h : forgetAction.map f = forgetAction.map g) : f = g :=
  FiniteProjectiveRepresentation.Hom.ext (congrArg (fun f => f.base) h)
    (congrArg (fun f => f.map) h)

/-- A morphism of the underlying modules which commutes with the actions is a morphism of
representations. -/
private abbrev homOfEquivariant {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    {X Y : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ}
    (l : forgetAction.obj X ⟶ forgetAction.obj Y)
    (h : ∀ γ x, l.map (X.action γ x) = Y.action γ (l.map x)) : X ⟶ Y where
  base := l.base
  map := l.map
  map_smul := l.map_smul
  equivariant := h
  isBaseChange := l.isBaseChange

/-- A family of endomorphisms of a module over the identity of the base, multiplicative up to
order, is a representation. -/
private abbrev actionOfEnds {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    {Y : FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k)} (a : Γ → End Y)
    (hbase : ∀ γ, (a γ).base = 𝟙 Y.base) (hone : a 1 = 𝟙 Y)
    (hmul : ∀ γ δ, a (γ * δ) = a δ ≫ a γ) : Representation Y.base Γ Y.carrier where
  toFun γ := {
    toFun := (a γ).map
    map_add' := (a γ).map.map_add
    map_smul' := by
      intro r x
      rw [(a γ).map_smul, hbase]
      rfl }
  map_one' := by
    ext x
    exact congrArg (fun f => f.map x) hone
  map_mul' γ δ := by
    ext x
    exact congrArg (fun f => f.map x) (hmul γ δ)

/-- Moving the fixed residue field along an algebra equivalence. -/
private noncomputable abbrev changeResidueBase {Λ : Type u} {k : Type w} {k' : Type v}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (ε : k ≃ₐ[Λ] k') :
    ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ ArtinianLocalAlgCat.{u, v, v} Λ k' where
  obj A := { carrier := A, residueEquiv := A.residueEquiv.trans ε }
  map f := {
    hom := f.hom
    isLocal := f.isLocal
    residue_comm := fun x => congrArg ε (f.residue_comm x) }

private theorem changeResidueBase_full {Λ : Type u} {k : Type w} {k' : Type v}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (ε : k ≃ₐ[Λ] k') : (changeResidueBase ε).Full where
  map_surjective f := ⟨{
    hom := f.hom
    isLocal := f.isLocal
    residue_comm := fun x => ε.injective (f.residue_comm x) }, by
      apply ArtinianLocalAlgCat.hom_ext; rfl⟩

attribute [local instance] changeResidueBase_full

private theorem changeResidueBase_faithful {Λ : Type u} {k : Type w} {k' : Type v}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (ε : k ≃ₐ[Λ] k') : (changeResidueBase ε).Faithful where
  map_injective h := ArtinianLocalAlgCat.hom_ext (congrArg (fun f => f.hom) h)

attribute [local instance] changeResidueBase_faithful

/-- Moving the fixed residue field of the finite projective modules along an algebra
equivalence. -/
private noncomputable abbrev changeResidueModules {Λ : Type u} {k : Type w} {k' : Type v}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (ε : k ≃ₐ[Λ] k') :
    FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k) ⥤
      FiniteProjectiveModule.{u, v, v, m} (Λ := Λ) (k := k') where
  obj X := { base := (changeResidueBase ε).obj X.base, carrier := X.carrier }
  map f := {
    base := (changeResidueBase ε).map f.base
    map := f.map
    map_smul := f.map_smul
    equivariant := fun _ _ => rfl
    isBaseChange := f.isBaseChange }

private theorem changeResidueModules_full {Λ : Type u} {k : Type w} {k' : Type v}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (ε : k ≃ₐ[Λ] k') : (changeResidueModules.{u, v, w, m} ε).Full where
  map_surjective f := ⟨{
    base := {
      hom := f.base.hom
      isLocal := f.base.isLocal
      residue_comm := fun x => ε.injective (f.base.residue_comm x) }
    map := f.map
    map_smul := f.map_smul
    equivariant := fun _ _ => rfl
    isBaseChange := f.isBaseChange }, by
      apply FiniteProjectiveRepresentation.Hom.ext <;> rfl⟩

attribute [local instance] changeResidueModules_full

private theorem changeResidueModules_faithful {Λ : Type u} {k : Type w} {k' : Type v}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (ε : k ≃ₐ[Λ] k') : (changeResidueModules.{u, v, w, m} ε).Faithful where
  map_injective h := FiniteProjectiveRepresentation.Hom.ext
    ((changeResidueBase ε).map_injective (congrArg (fun f => f.base) h))
    (congrArg (fun f => f.map) h)

attribute [local instance] changeResidueModules_faithful

private lemma changeResidueModules_essSurj {Λ : Type u} {k : Type w} {k' : Type v}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (ε : k ≃ₐ[Λ] k')
    (Y : FiniteProjectiveModule.{u, v, v, m} (Λ := Λ) (k := k')) :
    ∃ X, Nonempty ((changeResidueModules ε).obj X ≅ Y) := by
  let X : FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k) := {
    base := { carrier := Y.base, residueEquiv := Y.base.residueEquiv.trans ε.symm }
    carrier := Y.carrier }
  refine ⟨X, ⟨eqToIso ?_⟩⟩
  have hε : (Y.base.residueEquiv.trans ε.symm).trans ε = Y.base.residueEquiv := by
    ext x
    exact ε.apply_symm_apply _
  exact congrArg (fun E => ({
    base := { carrier := Y.base, residueEquiv := E }
    carrier := Y.carrier } :
      FiniteProjectiveModule.{u, v, v, m} (Λ := Λ) (k := k'))) hε

/-- Condition (RS) for the finite projective modules with the residue field in a universe of
its own, obtained from the equal-universe statement along `changeResidueModules`. -/
private lemma modulePullback_of_residueEquiv {Λ : Type u} {k : Type w} {k' : Type v}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (ε : k ≃ₐ[Λ] k')
    {X₁ X₂ X : FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k)}
    (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (hf₂ : Function.Surjective f₂.base.hom) :
    ∃ c : PullbackCone f₁ f₂,
      Nonempty (IsLimit c) ∧ Nonempty (IsLimit (c.map moduleProjection)) := by
  classical
  let F := changeResidueModules ε
  obtain ⟨c, ⟨hc⟩, ⟨hb⟩⟩ := moduleProjection_satisfiesRS.2 (F.map f₁) (F.map f₂) hf₂
  obtain ⟨Y, ⟨i⟩⟩ := changeResidueModules_essSurj ε c.pt
  let l₁ : Y ⟶ X₁ := F.preimage (i.hom ≫ c.fst)
  let l₂ : Y ⟶ X₂ := F.preimage (i.hom ≫ c.snd)
  have he₁ : F.map l₁ = i.hom ≫ c.fst := F.map_preimage _
  have he₂ : F.map l₂ = i.hom ≫ c.snd := F.map_preimage _
  have hm : IsPullback (F.map l₁) (F.map l₂) (F.map f₁) (F.map f₂) :=
    (IsPullback.of_isLimit hc).of_iso' i (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [he₁]) (by simp [he₂]) (by simp) (by simp)
  have hl : IsPullback l₁ l₂ f₁ f₂ := hm.of_map_of_faithful F
  refine ⟨hl.cone, ⟨hl.isLimit⟩, ⟨?_⟩⟩
  have hm' : IsPullback ((changeResidueBase ε).map l₁.base)
      ((changeResidueBase ε).map l₂.base) ((changeResidueBase ε).map f₁.base)
      ((changeResidueBase ε).map f₂.base) :=
    (IsPullback.of_isLimit hb).of_iso' (moduleProjection.mapIso i)
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        show i.hom.base ≫ c.fst.base = (F.map l₁).base
        exact (congrArg (fun f => f.base) he₁).symm)
      (by
        show i.hom.base ≫ c.snd.base = (F.map l₂).base
        exact (congrArg (fun f => f.base) he₂).symm)
      (by simp; rfl) (by simp; rfl)
  exact (hm'.of_map_of_faithful (changeResidueBase ε)).isLimit

private lemma module_unique_lift {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (hp : IsCofiberedInGroupoids (moduleProjection.{u, v, w, m} (Λ := Λ) (k := k)))
    {X Y Z : FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k)}
    (f : X ⟶ Y) (g : X ⟶ Z) (b : Y.base ⟶ Z.base) (h : f.base ≫ b = g.base) :
    ∃! l : Y ⟶ Z, l.base = b ∧ f ≫ l = g := by
  obtain ⟨l, hl, hu⟩ := hp.unique_lift f.op g.op b.op (congrArg Quiver.Hom.op h)
  refine ⟨l.unop, ⟨congrArg Quiver.Hom.unop hl.1, congrArg Quiver.Hom.unop hl.2⟩, ?_⟩
  intro l' hl'
  exact congrArg Quiver.Hom.unop (hu l'.op
    ⟨congrArg Quiver.Hom.op hl'.1, congrArg Quiver.Hom.op hl'.2⟩)

/-- A morphism of modules filling a square of representations is automatically equivariant. -/
private lemma equivariant_module_lift {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (hp : IsCofiberedInGroupoids (moduleProjection.{u, v, w, m} (Λ := Λ) (k := k)))
    {X Y Z : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ}
    (f : X ⟶ Y) (g : X ⟶ Z)
    (l : forgetAction.obj Y ⟶ forgetAction.obj Z)
    (hl : forgetAction.map f ≫ l = forgetAction.map g) :
    ∀ γ x, l.map (Y.action γ x) = Z.action γ (l.map x) := by
  intro γ x
  obtain ⟨q, hq, hu⟩ := module_unique_lift hp (forgetAction.map f)
    (actionEnd X γ ≫ forgetAction.map g) l.base (by
      simpa using congrArg (fun h => h.base) hl)
  have h₁ : actionEnd Y γ ≫ l = q := hu _ ⟨by simp, by
    rw [← Category.assoc, ← actionEnd_naturality, Category.assoc, hl]⟩
  have h₂ : l ≫ actionEnd Z γ = q := hu _ ⟨by simp, by
    rw [← Category.assoc, hl, ← actionEnd_naturality]⟩
  exact congrArg (fun h => h.map x) (h₁.trans h₂.symm)

/-- The pushforward of a representation along a morphism of modules out of its underlying
module. -/
private lemma pushforwardAction {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (hp : IsCofiberedInGroupoids (moduleProjection.{u, v, w, m} (Λ := Λ) (k := k)))
    (X : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ)
    (Y : FiniteProjectiveModule.{u, v, w, m} (Λ := Λ) (k := k))
    (f : forgetAction.obj X ⟶ Y) :
    ∃ (ρ : Representation Y.base Γ Y.carrier),
      ∀ γ x, f.map (X.action γ x) = ρ γ (f.map x) := by
  classical
  have H (γ : Γ) := module_unique_lift hp f (actionEnd X γ ≫ f) (𝟙 Y.base) (by simp)
  choose a ha hu using H
  have hone : a 1 = 𝟙 Y := by
    symm
    apply hu 1
    exact ⟨rfl, by rw [actionEnd_one]; simp⟩
  have hmul (γ δ : Γ) : a (γ * δ) = a δ ≫ a γ := by
    symm
    apply hu (γ * δ)
    refine ⟨by simp [(ha γ).1, (ha δ).1], ?_⟩
    rw [← Category.assoc, (ha δ).2, Category.assoc, (ha γ).2,
      ← Category.assoc, ← actionEnd_mul]
  exact ⟨actionOfEnds a (fun γ => (ha γ).1) hone hmul,
    fun γ x => (congrArg (fun f => f.map x) (ha γ).2).symm⟩

private lemma representationProjection_isCofibered_of_moduleProjection
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (hp : IsCofiberedInGroupoids (moduleProjection.{u, v, w, m} (Λ := Λ) (k := k))) :
    IsCofiberedInGroupoids
      (FiniteProjectiveRepresentation.projection.{u, v, w, m}
        (Λ := Λ) (k := k) (Γ := Γ)) := by
  constructor
  · intro B A f X hX
    obtain ⟨Y, g, hg⟩ := hp.exists_lift f (Opposite.op (forgetAction.obj X.unop)) hX
    obtain ⟨ρ, hρ⟩ := pushforwardAction hp X.unop Y.unop g.unop
    let Z : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ := {
      base := Y.unop.base
      carrier := Y.unop.carrier
      action := ρ }
    let l : X.unop ⟶ Z := homOfEquivariant g.unop hρ
    refine ⟨Opposite.op Z, l.op, ?_⟩
    let := hg
    exact IsHomLift.of_fac' _ f l.op
      (IsHomLift.domain_eq moduleProjection.op f g)
      (IsHomLift.codomain_eq moduleProjection.op f g)
      (IsHomLift.fac' moduleProjection.op f g)
  · intro X Y Z f g b h
    obtain ⟨l, hl, hu⟩ := module_unique_lift hp
      (forgetAction.map f.unop) (forgetAction.map g.unop) b.unop
      (congrArg Quiver.Hom.unop h)
    let q : Y.unop ⟶ Z.unop :=
      homOfEquivariant l (equivariant_module_lift hp f.unop g.unop l hl.2)
    have hq : f.unop ≫ q = g.unop := forgetAction_map_injective hl.2
    refine ⟨q.op, ⟨congrArg Quiver.Hom.op hl.1, congrArg Quiver.Hom.op hq⟩, ?_⟩
    intro q' hq'
    have he : forgetAction.map q'.unop = l := hu _
      ⟨congrArg Quiver.Hom.unop hq'.1,
        congrArg (fun f => forgetAction.map f.unop) hq'.2⟩
    exact Quiver.Hom.unop_inj (forgetAction_map_injective he)

/-- A pullback cone of the underlying modules carries a unique action making it a pullback cone
of representations. -/
private lemma liftRepresentationPullback {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    {X₁ X₂ X : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ}
    (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X)
    (c : PullbackCone (forgetAction.map f₁) (forgetAction.map f₂))
    (hc : IsLimit c) (hb : IsLimit (c.map moduleProjection)) :
    ∃ d : PullbackCone f₁ f₂,
      Nonempty (IsLimit d) ∧
        Nonempty (IsLimit (d.map FiniteProjectiveRepresentation.projection)) := by
  classical
  let a (γ : Γ) : c.pt ⟶ c.pt := hc.lift (PullbackCone.mk
    (c.fst ≫ actionEnd X₁ γ) (c.snd ≫ actionEnd X₂ γ) (by
      rw [Category.assoc, actionEnd_naturality, ← Category.assoc, c.condition,
        Category.assoc, ← actionEnd_naturality, ← Category.assoc]))
  have ha₁ (γ : Γ) : a γ ≫ c.fst = c.fst ≫ actionEnd X₁ γ :=
    hc.fac _ WalkingCospan.left
  have ha₂ (γ : Γ) : a γ ≫ c.snd = c.snd ≫ actionEnd X₂ γ :=
    hc.fac _ WalkingCospan.right
  have hbase (γ : Γ) : (a γ).base = 𝟙 c.pt.base := by
    apply PullbackCone.IsLimit.hom_ext hb
    · show (a γ).base ≫ c.fst.base = 𝟙 c.pt.base ≫ c.fst.base
      simpa only [module_comp_base, Category.comp_id, Category.id_comp] using
        congrArg (fun f => f.base) (ha₁ γ)
    · show (a γ).base ≫ c.snd.base = 𝟙 c.pt.base ≫ c.snd.base
      simpa only [module_comp_base, Category.comp_id, Category.id_comp] using
        congrArg (fun f => f.base) (ha₂ γ)
  have hone : a 1 = 𝟙 c.pt := by
    apply PullbackCone.IsLimit.hom_ext hc <;>
      simp [ha₁, ha₂, actionEnd_one]
  have hmul (γ δ : Γ) : a (γ * δ) = a δ ≫ a γ := by
    apply PullbackCone.IsLimit.hom_ext hc
    · simp only [ha₁, actionEnd_mul, Category.assoc]
      simpa only [Category.assoc] using
        congrArg (fun l => l ≫ actionEnd X₁ γ) (ha₁ δ).symm
    · simp only [ha₂, actionEnd_mul, Category.assoc]
      simpa only [Category.assoc] using
        congrArg (fun l => l ≫ actionEnd X₂ γ) (ha₂ δ).symm
  let Y : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ := {
    base := c.pt.base
    carrier := c.pt.carrier
    action := actionOfEnds a hbase hone hmul }
  let t₁ : Y ⟶ X₁ :=
    homOfEquivariant c.fst fun γ x => congrArg (fun f => f.map x) (ha₁ γ)
  let t₂ : Y ⟶ X₂ :=
    homOfEquivariant c.snd fun γ x => congrArg (fun f => f.map x) (ha₂ γ)
  have ht : t₁ ≫ f₁ = t₂ ≫ f₂ := forgetAction_map_injective c.condition
  let d := PullbackCone.mk t₁ t₂ ht
  have hd : IsLimit d := by
    refine PullbackCone.IsLimit.mk ht ?_ ?_ ?_ ?_
    · intro s
      let l : forgetAction.obj s.pt ⟶ c.pt := hc.lift (s.map forgetAction)
      have hl₁ : l ≫ c.fst = forgetAction.map s.fst := hc.fac _ WalkingCospan.left
      have hl₂ : l ≫ c.snd = forgetAction.map s.snd := hc.fac _ WalkingCospan.right
      have hl (γ : Γ) : actionEnd s.pt γ ≫ l = l ≫ a γ := by
        apply PullbackCone.IsLimit.hom_ext hc
        · simp only [Category.assoc, hl₁, ha₁]
          rw [← Category.assoc, hl₁, actionEnd_naturality]
        · simp only [Category.assoc, hl₂, ha₂]
          rw [← Category.assoc, hl₂, actionEnd_naturality]
      exact homOfEquivariant l fun γ x => congrArg (fun f => f.map x) (hl γ)
    · intro s
      exact forgetAction_map_injective (hc.fac (s.map forgetAction) WalkingCospan.left)
    · intro s
      exact forgetAction_map_injective (hc.fac (s.map forgetAction) WalkingCospan.right)
    · intro s l hl₁ hl₂
      have he : forgetAction.map l = hc.lift (s.map forgetAction) :=
        PullbackCone.IsLimit.hom_ext hc
          ((congrArg (fun f => forgetAction.map f) hl₁).trans
            (hc.fac (s.map forgetAction) WalkingCospan.left).symm)
          ((congrArg (fun f => forgetAction.map f) hl₂).trans
            (hc.fac (s.map forgetAction) WalkingCospan.right).symm)
      exact forgetAction_map_injective he
  exact ⟨d, ⟨hd⟩, ⟨(IsPullback.of_isLimit hb).isLimit⟩⟩

/-- Finite projective representations satisfy the Rim–Schlessinger condition. -/
@[stacks 0DVS "Rim-Schlessinger condition"]
public theorem satisfiesRS_projection
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] :
    SatisfiesRS
      (FiniteProjectiveRepresentation.projection.{u, v, w, max v m}
        (Λ := Λ) (k := k) (Γ := Γ)) := by
  refine ⟨FiniteProjectiveRepresentation.projection_isCofiberedInGroupoids, ?_⟩
  intro X₁ X₂ X f₁ f₂ hf₂
  obtain ⟨c, ⟨hc⟩, ⟨hb⟩⟩ := modulePullback_of_residueEquiv X.base.residueEquiv.symm
    (forgetAction.map f₁) (forgetAction.map f₂) hf₂
  exact liftRepresentationPullback f₁ f₂ c hc hb

/-- Condition (RS) for finite projective representations, with the module universe
independent of the universe of the coefficient algebras.

This is the form `satisfiesRS_projection` takes when the morphism universe of `𝒞_Λ` is the
residue-field universe `w`: the pullback of modules is then produced by `moduleProjection`
rather than by a residue-field comparison, so the module universe `m` is unconstrained. The
tagged `satisfiesRS_projection` above keeps a free morphism universe `v` and pays for it with
the module universe `max v m`; neither statement implies the other. -/
public theorem satisfiesRS_projection_carrierUniverse
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] :
    SatisfiesRS
      (FiniteProjectiveRepresentation.projection.{u, w, w, m}
        (Λ := Λ) (k := k) (Γ := Γ)) := by
  refine ⟨representationProjection_isCofibered_of_moduleProjection
    moduleProjection_satisfiesRS.1, ?_⟩
  intro X₁ X₂ X f₁ f₂ hf₂
  obtain ⟨c, ⟨hc⟩, ⟨hb⟩⟩ := moduleProjection_satisfiesRS.2
    (forgetAction.map f₁) (forgetAction.map f₂) hf₂
  exact liftRepresentationPullback f₁ f₂ c hc hb

/-- The deformations of a finite-dimensional representation form a deformation category. -/
@[stacks 0DVS "deformation category"]
public theorem isDeformationCategory_deformationCategory
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) :
    IsDeformationCategory
      (objectsOverFunctor
        (FiniteProjectiveRepresentation.projection.{u, w, w, m}
          (Λ := Λ) (k := k) (Γ := Γ))
        (FiniteProjectiveRepresentation.specialFiber (Λ := Λ) V ρ₀)) :=
  isDeformationCategory_objectsOverFunctor_of_baseIso _
    satisfiesRS_projection_carrierUniverse
    (FiniteProjectiveRepresentation.specialFiber (Λ := Λ) V ρ₀) residueFieldBaseIso

end Deformation.Examples.FiniteProjectiveRepresentation
