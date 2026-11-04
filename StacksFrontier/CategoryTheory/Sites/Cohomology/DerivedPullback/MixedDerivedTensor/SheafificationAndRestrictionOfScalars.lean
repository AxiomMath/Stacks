module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.UnderivedTensorInverseImage

/-!
# Sheafification of presheaves of modules commutes with restriction of scalars

Let `α : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)`.  A presheaf
of `O₂`-modules can be turned into a sheaf of `O₁`-modules in two ways: restrict its scalars
along `α` and then sheafify over `O₁`, or sheafify over `O₂` and then restrict the scalars of
the resulting sheaf.  The two functors are canonically isomorphic.

Both have the same underlying sheaf of abelian groups, namely the sheafification of the
underlying abelian presheaf, because neither restriction of scalars nor the passage from a
presheaf of modules to its associated sheaf changes it.  The comparison between them is
therefore the unit of the sheafification over `O₁`, read on the restriction of scalars of the
unit of the sheafification over `O₂`: that morphism is locally bijective, since on underlying
abelian presheaves it *is* the sheafification map, and a locally bijective morphism from a
presheaf of modules into a sheaf of modules exhibits the latter as the former's sheafification.

This is the comparison isolated as
`Stacks.Cohomology.MixedDerivedTensor.SheafifyCommutesRestrictScalars`, and the only input the
`O₁`-linear form of the cancellation of a base change was missing.  Granting it unconditionally
makes the `f⁻¹O'`-linear form of the underived identity of Stacks 08I6 unconditional as well.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.restrictUnit`: the unit of the sheafification over `O₂`,
  read after restriction of scalars along `α`.
* `Stacks.Cohomology.MixedDerivedTensor.sheafifyRestrictHom`: the induced comparison morphism
  from the sheafification over `O₁` of a restriction of scalars to the restriction of scalars of
  the sheafification over `O₂`.
* `Stacks.Cohomology.MixedDerivedTensor.sheafifyCommutesRestrictScalars`: **the comparison**, as
  an isomorphism of functors.
* `Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso`: the cancellation of a base
  change as an isomorphism of sheaves of `O₁`-modules, now unconditional.
* `Stacks.Cohomology.MixedDerivedTensor.underivedTensorInverseImageLinearIso`: the underived
  identity of Stacks 08I6 as an isomorphism of sheaves of `f⁻¹O'`-modules, now unconditional.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.toPresheaf_map_restrictUnit`: on underlying abelian
  presheaves the restricted unit is the sheafification map, by `rfl`.  This is what makes it
  locally bijective and hence what makes the comparison invertible.
* `Stacks.Cohomology.MixedDerivedTensor.isIso_sheafifyRestrictHom`: the comparison morphism is
  invertible at every presheaf of `O₂`-modules.

## Implementation notes

The invertibility is `Stacks.SheafOfModules.SliceSheafification.isIso_sheafificationHomEquiv_symm`,
which says that a locally bijective morphism from a presheaf of modules into the restriction of
scalars of a sheaf of modules exhibits the latter as the sheafification of the former.  Its two
hypotheses are about the underlying morphism of abelian presheaves, and there that morphism is
the sheafification map `CategoryTheory.toSheafify`, which is locally bijective.

**Where the types are chosen rather than inferred.**  `PresheafOfModules.restrictScalars` along
an identity of presheaves of rings is the identity functor, but only up to unfolding; the
composite of restriction of scalars along `α` with restriction of scalars along an identity is
accordingly the same functor in either order, and asking the elaborator to see that costs more
than the whole file.  So `Stacks.Cohomology.MixedDerivedTensor.toSheafifyVal` states the
sheafification unit with the identity restriction already removed, and
`Stacks.Cohomology.MixedDerivedTensor.restrictUnit` carries the ascribed type in which the
identity restriction appears on the outside — the shape the sheafification adjunction over `O₁`
consumes.  Each crossing then costs one unfolding instead of two nested ones.

Naturality is proved after applying the sheafification adjunction's hom-bijection, where it
becomes the naturality of the unit: this avoids ever comparing the two composites directly, a
comparison which is again available only by unfolding.

**Universes.**  The site is `C : Type u` with `Category.{v} C`, and the structure sheaves and
the modules both live in universe `w`, as they do in
`Stacks.Cohomology.MixedDerivedTensor.SheafifyCommutesRestrictScalars` and in
`Stacks.FlatChangeOfRings`.

**No tag is placed in this file.**  Stacks 08I6 asserts an isomorphism in the derived category,
and nothing here concludes that; the identity below is the underived step of the source's proof.

## References

* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
* [The Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Cohomology.MixedDerivedTensor

/-! ### The comparison of the two sheafifications -/

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- The unit of the sheafification of presheaves of `O₂`-modules, with the restriction of
scalars along the identity of the presheaf of rings underlying `O₂` removed. -/
def toSheafifyVal (M : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj) :
    M ⟶ ((Stacks.moduleSheafification O₂).obj M).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app M

/-- The sheafification unit is natural. -/
lemma toSheafifyVal_naturality
    {M N : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj} (ψ : M ⟶ N) :
    ψ ≫ toSheafifyVal N = toSheafifyVal M ≫
        (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂)).map
          ((Stacks.moduleSheafification O₂).map ψ) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.naturality ψ

/-- The sheafification unit of a presheaf of `O₂`-modules, read after restriction of scalars
along `α`.  This is the morphism whose adjoint is the comparison of the two sheafifications. -/
def restrictUnit (α : O₁ ⟶ O₂)
    (M : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj) :
    (PresheafOfModules.restrictScalars
        (Stacks.FlatChangeOfRings.ringSheafMap α).hom).obj M ⟶
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₁) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj)).obj
        ((SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap α)).obj
          ((Stacks.moduleSheafification O₂).obj M)) :=
  (PresheafOfModules.restrictScalars
    (Stacks.FlatChangeOfRings.ringSheafMap α).hom).map (toSheafifyVal M)

/-- **On underlying abelian presheaves the restricted unit is the sheafification map.**
Restriction of scalars does not change the underlying presheaf of modules and the
sheafification of a presheaf of modules has the sheafification of the underlying abelian
presheaf underlying it, so this holds by `rfl`. -/
lemma toPresheaf_map_restrictUnit (α : O₁ ⟶ O₂)
    (M : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj) :
    (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj).map
        (restrictUnit α M) = CategoryTheory.toSheafify J M.presheaf :=
  rfl

/-- The restricted unit is natural. -/
lemma restrictUnit_naturality (α : O₁ ⟶ O₂)
    {M N : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj} (ψ : M ⟶ N) :
    (PresheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap α).hom).map ψ ≫ restrictUnit α N
      = restrictUnit α M ≫
          (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₁) ⋙
            PresheafOfModules.restrictScalars
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj)).map
            ((SheafOfModules.restrictScalars.{w}
              (Stacks.FlatChangeOfRings.ringSheafMap α)).map
                ((Stacks.moduleSheafification O₂).map ψ)) :=
  (PresheafOfModules.restrictScalars
    (Stacks.FlatChangeOfRings.ringSheafMap α).hom).map_comp _ _ ▸
      (PresheafOfModules.restrictScalars
        (Stacks.FlatChangeOfRings.ringSheafMap α).hom).congr_map
          (toSheafifyVal_naturality ψ)

/-- The comparison morphism from the sheafification over `O₁` of a restriction of scalars to
the restriction of scalars of the sheafification over `O₂`, adjoint to the restricted unit. -/
def sheafifyRestrictHom (α : O₁ ⟶ O₂)
    (M : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj) :
    (Stacks.moduleSheafification O₁).obj
        ((PresheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap α).hom).obj M) ⟶
      (SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap α)).obj
        ((Stacks.moduleSheafification O₂).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj)).symm (restrictUnit α M)

/-- **The comparison morphism is invertible.**  Its adjoint is locally bijective, by
`toPresheaf_map_restrictUnit`, so it exhibits the restriction of scalars of the sheafification
over `O₂` as the sheafification over `O₁` of the restriction of scalars. -/
instance isIso_sheafifyRestrictHom (α : O₁ ⟶ O₂)
    (M : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj) :
    IsIso (sheafifyRestrictHom α M) :=
  Stacks.SheafOfModules.SliceSheafification.isIso_sheafificationHomEquiv_symm
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj) (restrictUnit α M)
    (by rw [toPresheaf_map_restrictUnit]; exact (J.W_toSheafify M.presheaf).isLocallyInjective)
    (by rw [toPresheaf_map_restrictUnit]; exact (J.W_toSheafify M.presheaf).isLocallySurjective)

/-- The adjoint of the comparison morphism is the restricted unit, by construction. -/
lemma homEquiv_sheafifyRestrictHom (α : O₁ ⟶ O₂)
    (M : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj) :
    (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj)).homEquiv _ _ (sheafifyRestrictHom α M)
      = restrictUnit α M :=
  (PresheafOfModules.sheafificationHomEquiv
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O₁)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj)).apply_symm_apply _

/-- The comparison morphism is natural in the presheaf of `O₂`-modules. -/
lemma sheafifyRestrictHom_naturality (α : O₁ ⟶ O₂)
    {M N : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj} (ψ : M ⟶ N) :
    (Stacks.moduleSheafification O₁).map
        ((PresheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap α).hom).map ψ) ≫ sheafifyRestrictHom α N
      = sheafifyRestrictHom α M ≫
          (SheafOfModules.restrictScalars.{w}
            (Stacks.FlatChangeOfRings.ringSheafMap α)).map
              ((Stacks.moduleSheafification O₂).map ψ) := by
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, homEquiv_sheafifyRestrictHom, restrictUnit_naturality,
    ← homEquiv_sheafifyRestrictHom, Adjunction.homEquiv_naturality_right]

/-- **Sheafification of presheaves of modules commutes with restriction of scalars.**
Restricting the scalars along `α : O₁ ⟶ O₂` and then sheafifying over `O₁` agrees with
sheafifying over `O₂` and then restricting the scalars. -/
def sheafifyCommutesRestrictScalars (α : O₁ ⟶ O₂) :
    SheafifyCommutesRestrictScalars.{u, v, w} α :=
  NatIso.ofComponents
    (fun (M : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj) ↦
      @asIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) _ _ _
        (sheafifyRestrictHom α M) (isIso_sheafifyRestrictHom α M))
    fun ψ ↦ sheafifyRestrictHom_naturality α ψ

/-- **Cancellation of a base change, as sheaves of `O₁`-modules.**  For a morphism
`α : O₁ ⟶ O₂` of sheaves of commutative rings and a sheaf `G` of `O₁`-modules, tensoring an
`O₂`-module `H` with the extension of scalars `O₂ ⊗_{O₁} G` gives, as a sheaf of
`O₁`-modules, the tensor product over `O₁` of the restriction of `H` with `G`, naturally
in `H`.

This is `tensorBaseChangeModuleIso` with its hypothesis discharged by
`sheafifyCommutesRestrictScalars`. -/
def tensorBaseChangeLinearIso (α : O₁ ⟶ O₂)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) :
    SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap α) ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₁).flip.obj G
      ≅ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₂).flip.obj
            ((Stacks.FlatChangeOfRings.extendScalars α).obj G) ⋙
          SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap α) :=
  tensorBaseChangeModuleIso α (sheafifyCommutesRestrictScalars α) G

end Sheafify

/-! ### The underived identity of Stacks 08I6, unconditionally `f⁻¹O'`-linear -/

section Tag08I6

open StacksPullbackFactorization

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : AlgebraicGeometry.RingedToposSiteHom X Y)

/-- **The underived identity of Stacks 08I6, as sheaves of `f⁻¹O'`-modules.**  For a sheaf `G`
of `O'`-modules, the functor carrying a sheaf `F` of `O`-modules to
`F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G` and the functor carrying it to `(F ⊗_O f^*G)|_{f⁻¹O'}` are
isomorphic, naturally in `F`.

This is `underivedTensorInverseImageModuleIso` with its hypothesis discharged by
`sheafifyCommutesRestrictScalars`.  Unlike the identity of underlying sheaves of abelian
groups, this one records the `f⁻¹O'`-module structure, which is what a derived form of the
tag consumes. -/
def underivedTensorInverseImageLinearIso
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :
    restrictToInvRing f ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).flip.obj
          ((auxHomG f).pullbackTopos.obj G)
      ≅ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.obj
            (f.pullbackTopos.obj G) ⋙ restrictToInvRing f :=
  underivedTensorInverseImageModuleIso f
    (sheafifyCommutesRestrictScalars ((auxHomH f).fSharp)) G

end Tag08I6

end Stacks.Cohomology.MixedDerivedTensor

end
