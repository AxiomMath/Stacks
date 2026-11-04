module

public import StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.BaseChange

/-!
# Extension of scalars along a locally surjective map is locally surjective

Let `f : O ⟶ O₀` be a locally surjective morphism of sheaves of commutative rings on a site. A
morphism `M ⟶ M₀|_O` with the universal property of extension of scalars
(`Stacks.SheafOfModules.ComplexLifting.IsExtensionOfScalars`) agrees with the canonical unit
`M ⟶ (O₀ ⊗_O M)|_O` up to an isomorphism, and that unit is locally surjective on sections. So
the morphism is locally surjective on sections: a section of the extension is, locally, the
image of a section of `M`. This sharpens
`Stacks.SheafOfModules.ComplexLifting.IsExtensionOfScalars.epi_unit` from an epimorphism of
sheaves of modules to a statement about sections.

## Main results

* `Stacks.SheafOfModules.ComplexLifting.extensionOfScalarsUnit_isLocallySurjective`: the
  canonical unit is locally surjective.
* `Stacks.SheafOfModules.ComplexLifting.IsExtensionOfScalars.isIso_desc`: a morphism with the
  universal property is the canonical unit followed by an isomorphism.
* `Stacks.SheafOfModules.ComplexLifting.IsExtensionOfScalars.isLocallySurjective`: a morphism
  with the universal property is locally surjective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.SheafOfModules.ComplexLifting

open Stacks.Sheaves.ChangeOfRings (ringSheafMap)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w z}]
  [HasSheafify J AddCommGrpCat.{max w z}]
  {O O₀ : Sheaf J CommRingCat.{w}}

/-- **The canonical unit `M ⟶ (O₀ ⊗_O M)|_O` is locally surjective on sections** when `f` is: it
is the presheaf-level unit, which is locally surjective, followed by the sheafification unit. -/
lemma extensionOfScalarsUnit_isLocallySurjective (f : O ⟶ O₀)
    (hf : Sheaf.IsLocallySurjective f)
    (M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    Sheaf.IsLocallySurjective
      ((_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).map
        (extensionOfScalarsUnit f M)) := by
  let T := (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj M.val
  let η : M.val.presheaf ⟶ T.presheaf :=
    (_root_.PresheafOfModules.toPresheaf _).map (Stacks.PresheafOfModules.ChangeOfRings.unitHom
      f.hom (𝟙 T))
  have hη : Presheaf.IsLocallySurjective J η :=
    presheafUnit_isLocallySurjective f hf M.val
  have heq : ((_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).map
      (extensionOfScalarsUnit f M)).hom = η ≫ CategoryTheory.toSheafify J T.presheaf := by
    ext U x
    let _inst := (f.hom.app U).hom.toAlgebra
    exact Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply f.hom
      (_root_.PresheafOfModules.sheafificationHomEquiv
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj) (𝟙 _)) U x
  change Presheaf.IsLocallySurjective J _
  rw [heq]
  exact Presheaf.isLocallySurjective_comp J η (CategoryTheory.toSheafify J T.presheaf)

/-- **A morphism with the universal property of extension of scalars is the canonical unit
followed by an isomorphism**: the comparison out of the canonical extension of scalars that the
universal property of the latter produces is invertible, its inverse being the comparison the
universal property of the former produces. -/
lemma IsExtensionOfScalars.isIso_desc (f : O ⟶ O₀)
    {M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {M₀ : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    {uM : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj M₀}
    (h : IsExtensionOfScalars f M M₀ uM) :
    IsIso (IsExtensionOfScalars.desc f (extensionOfScalarsUnit_isExtension f M) uM) := by
  let R := _root_.SheafOfModules.restrictScalars (ringSheafMap f)
  let h' := extensionOfScalarsUnit_isExtension f M
  let a := IsExtensionOfScalars.desc f h' uM
  let b := IsExtensionOfScalars.desc f h (extensionOfScalarsUnit f M)
  have ha : extensionOfScalarsUnit f M ≫ R.map a = uM := IsExtensionOfScalars.desc_spec f h' uM
  have hb : uM ≫ R.map b = extensionOfScalarsUnit f M := IsExtensionOfScalars.desc_spec f h _
  refine ⟨b, ?_, ?_⟩
  · apply (h' _).injective
    change extensionOfScalarsUnit f M ≫ R.map (a ≫ b) =
      extensionOfScalarsUnit f M ≫ R.map (𝟙 _)
    rw [R.map_comp, ← Category.assoc, ha, hb, R.map_id, Category.comp_id]
  · apply (h _).injective
    change uM ≫ R.map (b ≫ a) = uM ≫ R.map (𝟙 _)
    rw [R.map_comp, ← Category.assoc, hb, ha, R.map_id, Category.comp_id]

/-- **Any morphism with the universal property of extension of scalars is locally
surjective** when `f` is. This is `IsExtensionOfScalars.epi_unit` sharpened from an
epimorphism of sheaves of modules to local surjectivity of the map of sections, which is what
lets a section of the extension be written locally as the image of a section of the original
module. -/
lemma IsExtensionOfScalars.isLocallySurjective (f : O ⟶ O₀)
    (hf : Sheaf.IsLocallySurjective f)
    {M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {M₀ : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    {uM : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj M₀}
    (h : IsExtensionOfScalars f M M₀ uM) :
    Sheaf.IsLocallySurjective
      ((_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).map uM) := by
  let R := _root_.SheafOfModules.restrictScalars (ringSheafMap f)
  let S := _root_.SheafOfModules.toSheaf.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)
  let a := IsExtensionOfScalars.desc f (extensionOfScalarsUnit_isExtension f M) uM
  have ha : extensionOfScalarsUnit f M ≫ R.map a = uM :=
    IsExtensionOfScalars.desc_spec f (extensionOfScalarsUnit_isExtension f M) uM
  have : IsIso a := IsExtensionOfScalars.isIso_desc f h
  have : Sheaf.IsLocallySurjective (S.map (extensionOfScalarsUnit f M)) :=
    extensionOfScalarsUnit_isLocallySurjective f hf M
  have : Sheaf.IsLocallySurjective (S.map (R.map a)) := inferInstance
  rw [← ha, S.map_comp]
  change Presheaf.IsLocallySurjective J
    ((S.map (extensionOfScalarsUnit f M)).hom ≫ (S.map (R.map a)).hom)
  exact Presheaf.isLocallySurjective_comp J _ _

end Stacks.SheafOfModules.ComplexLifting

end
