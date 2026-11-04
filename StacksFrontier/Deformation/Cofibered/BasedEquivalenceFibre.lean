module

public import StacksFrontier.Deformation.Cofibered.Over
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# Essential surjectivity on fibres of a based functor over the base

For a based functor `φ : 𝓐 ⥤ᵇ 𝓑` the comparison `Deformation.fiberFunctor φ A` relates the
strict fibres, which are cut out by the *equality* `p.obj x = A`. Fullness and faithfulness of
`φ` transport to each comparison on fibres, but essential surjectivity does not: a functor
over the base that is essentially surjective carries an object of one fibre only to an object
lying over a base object *isomorphic* to `A`. The gap closes when the source projection is
cofibered in groupoids, because the isomorphism of base objects is then realised by a
pushforward upstairs.

## Main results

* `Deformation.essSurj_fiberFunctor`: the comparison on fibres is essentially surjective when
  the based functor is essentially surjective and the source projection is cofibered in
  groupoids.
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Functor
universe u v u₁ v₁ u₂ v₂

variable {C : Type u} [Category.{v} C] {𝓐 : BasedCategory.{v₁, u₁} C}
  {𝓑 : BasedCategory.{v₂, u₂} C}

/-- **The comparison on fibres is essentially surjective** for an essentially surjective based
functor whose source projection is cofibered in groupoids. An object `z` of the fibre of `𝓑`
over `A` is the image of some `a` up to an isomorphism `ε`, which lies over an isomorphism of
`A` with the base of `a`. Pushing `a` forward along that isomorphism lands it in the fibre
over `A`, and correcting `ε` by the image of the pushforward arrow gives an isomorphism over
`𝟙 A`. -/
public theorem essSurj_fiberFunctor (h𝓐 : IsCofiberedInGroupoids 𝓐.p) (φ : 𝓐 ⥤ᵇ 𝓑)
    [φ.toFunctor.EssSurj] (A : C) : (fiberFunctor φ A).EssSurj := by
  refine ⟨fun z => ?_⟩
  obtain ⟨a, ⟨ε⟩⟩ := Functor.EssSurj.mem_essImage φ.toFunctor z.1
  have hbase : 𝓑.p.obj (φ.toFunctor.obj a) = 𝓐.p.obj a := BasedFunctor.w_obj φ a
  let gIso : 𝓐.p.obj a ≅ A :=
    eqToIso hbase.symm ≪≫ 𝓑.p.mapIso ε ≪≫ eqToIso z.2
  have hεlift : 𝓑.p.IsHomLift gIso.hom ε.hom :=
    CategoryTheory.IsHomLift.of_fac 𝓑.p gIso.hom ε.hom hbase z.2 (by simp [gIso])
  obtain ⟨a', ι, hι⟩ := exists_pushforward h𝓐 gIso.hom a rfl
  have := hι
  have ha' : 𝓐.p.obj a' = A := CategoryTheory.IsHomLift.codomain_eq 𝓐.p gIso.hom ι
  have hιmapiso : IsIso (𝓐.p.map ι) := by
    rw [CategoryTheory.IsHomLift.fac' 𝓐.p gIso.hom ι]
    infer_instance
  have : IsIso ι := isIso_of_isCofiberedInGroupoids_of_map_isIso h𝓐 ι
  let ιIso : φ.toFunctor.obj a ≅ φ.toFunctor.obj a' := φ.toFunctor.mapIso (asIso ι)
  have : 𝓑.p.IsHomLift gIso.hom ιIso.hom :=
    BasedFunctor.preserves_isHomLift φ gIso.hom ι
  let δ : φ.toFunctor.obj a' ≅ z.1 := ιIso.symm ≪≫ ε
  have hδhom : 𝓑.p.IsHomLift (𝟙 A) δ.hom := by
    have h : 𝓑.p.IsHomLift (gIso.inv ≫ gIso.hom) (ιIso.inv ≫ ε.hom) := inferInstance
    rwa [gIso.inv_hom_id] at h
  exact ⟨Fiber.mk ha', ⟨{
    hom := ⟨δ.hom, hδhom⟩
    inv := ⟨δ.inv, CategoryTheory.IsHomLift.lift_id_inv 𝓑.p A δ⟩
    hom_inv_id := Fiber.hom_ext δ.hom_inv_id
    inv_hom_id := Fiber.hom_ext δ.inv_hom_id }⟩⟩

end

end Deformation

end
