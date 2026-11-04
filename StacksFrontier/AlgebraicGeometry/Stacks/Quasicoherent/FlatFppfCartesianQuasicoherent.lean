module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineCoveringFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Cartesian modules on the flat-fppf site are quasi-coherent

Let `𝒳` be an algebraic stack and `𝒳_{flat,fppf}` its flat-fppf site (**Stacks 0787**), ringed
by the restriction `𝒪` of the structure sheaf of `𝒳`. A sheaf of `𝒪`-modules `ℋ` on it is
*cartesian along the arrows between flat objects over affine schemes* when for every arrow
`y ⟶ y'` of `𝒳_{flat,fppf}` between objects lying over affine schemes the base-change map
`ℋ(y') ⊗_{𝒪(y')} 𝒪(y) ⟶ ℋ(y)` is an isomorphism. This file proves that such a module is
quasi-coherent on `𝒳_{flat,fppf}`.

## The proof

The flat objects lying over affine schemes form a dense subsite `𝒳_{flat,aff}` of
`𝒳_{flat,fppf}`: every flat object is covered by flat objects over affine schemes, the lifts of an
affine open covering of the scheme below it
(`AlgebraicGeometry.Stack.FlatFppf.isCoveringFamily_isAffine`). Quasi-coherence is detected on a
dense subsite (`Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff`, Stacks 03DM). On
`𝒳_{flat,aff}` *every* arrow is one along which `ℋ` is cartesian, and a module all of whose
base-change maps are isomorphisms is quasi-coherent
(`Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso`, the core of Stacks 0GZV):
on the chaotic site it has a global presentation over every object by Stacks 0GZN.

All the sites here are essentially small at the universe `u` of the schemes, being full
subcategories of the category underlying an algebraic stack
(`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`), which supplies the
sheafification and the limits the comparison lemma needs at module universe `u`.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.affineObject`: the flat objects lying over affine schemes.

## Main results

* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_of_isCoverDense`:
  on an essentially small site, a module cartesian along the arrows of a cover-dense full
  subcategory is quasi-coherent.
* `AlgebraicGeometry.Stack.FlatFppf.isCoverDense_affineObject_ι`: `𝒳_{flat,aff}` is cover dense
  in `𝒳_{flat,fppf}`.
* `AlgebraicGeometry.Stack.FlatFppf.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_affine`:
  a module on `𝒳_{flat,fppf}` cartesian along the arrows between flat objects over affine
  schemes is quasi-coherent.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 0GZN](https://stacks.math.columbia.edu/tag/0GZN)
* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 0H14](https://stacks.math.columbia.edu/tag/0H14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe w v u

/-- **A sheaf of modules cartesian along the arrows of a cover-dense full subcategory is
quasi-coherent.** Let `G : C ⥤ D` be the inclusion of a full subcategory which is cover dense for
a topology `K` on `D`, let `𝒪` be a sheaf of commutative rings on `(D, K)`, and let `ℋ` be a sheaf
of `𝒪`-modules such that for every arrow `U ⟶ V` of `C` the base-change map
`ℋ(V) ⊗_{𝒪(V)} 𝒪(U) ⟶ ℋ(U)` is an isomorphism. If both sites are essentially small at the
universe of the module sections, `ℋ` is quasi-coherent.

Quasi-coherence is detected on the dense subsite `C` (Stacks 03DM), and on `C` every base-change
map is an isomorphism, which makes the restriction of `ℋ` quasi-coherent (the core of
Stacks 0GZV). -/
theorem isQuasicoherentOnSite_of_isIso_restrictionBaseChange_of_isCoverDense
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D] (G : C ⥤ D) [G.Full]
    [G.Faithful] (K : GrothendieckTopology D) [G.IsCoverDense K]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (O : Sheaf K CommRingCat.{w})
    (H : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hH : ∀ ⦃U V : C⦄ (f : U ⟶ V),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange (R := O.obj) H.val (G.map f).op)) :
    H.IsQuasicoherentOnSite := by
  let J := G.inducedTopology K
  have : ∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w} := fun U =>
    (GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{w} (J.over U)).1
  have : ∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w} := fun U =>
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have : ∀ V : D, HasWeakSheafify (K.over V) AddCommGrpCat.{w} := fun V =>
    (GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{w} (K.over V)).1
  have : ∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{w} :=
    fun V => GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have : ∀ (U : C) (X : (Over (G.obj U))ᵒᵖ),
      HasLimitsOfShape (StructuredArrow X (Over.post (X := U) G).op) AddCommGrpCat.{w} :=
    fun _ _ => hasLimitsOfShape_of_essentiallySmall.{w} _ _
  have : ∀ X : Dᵒᵖ, HasLimitsOfShape (StructuredArrow X G.op) AddCommGrpCat.{w} :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{w} _ _
  have h1 : ((Stacks.DenseSubsiteModules.moduleRestriction J K G
      (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj H).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_canonicalMap_isIso (AlgebraicGeometry.affineRingedSite J K G O)
      ((Stacks.DenseSubsiteModules.moduleRestriction J K G
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj H)
      fun U V f => hH f
  exact (Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff J K G
    (Stacks.SheafOfModules.Tensor.ringSheaf O) H).2 h1

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack.FlatFppf

universe u t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, t} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- The flat objects of an algebraic stack lying over affine schemes. -/
abbrev affineObject : ObjectProperty (FlatFppf B S hS 𝒳) :=
  fun y => IsAffine (𝒳.val.val.p.obj y.obj).left.1

/-- **The flat objects over affine schemes are cover dense in the flat-fppf site**: every flat
object is covered by flat objects over affine schemes, the lifts of an affine open covering of
the scheme below it. -/
instance isCoverDense_affineObject_ι :
    (affineObject B S hS 𝒳).ι.IsCoverDense (inclusionTopology B S hS 𝒳) where
  is_cover y := by
    obtain ⟨R, hR, haff⟩ := isCoveringFamily_isAffine B S hS 𝒳 y
    rw [← inclusionTopology_eq_topology B S hS 𝒳] at hR
    refine (inclusionTopology B S hS 𝒳).superset_covering ?_ hR
    rintro Z g ⟨W, h, k, hk, rfl⟩
    exact ⟨⟨⟨W, haff hk⟩, h, k, rfl⟩⟩

/-- **A module on the flat-fppf site cartesian along the arrows between flat objects over affine
schemes is quasi-coherent.** Let `ℋ` be a sheaf of modules on the flat-fppf site of an algebraic
stack such that for every arrow `y ⟶ y'` between flat objects lying over affine schemes the
base-change map `ℋ(y') ⊗_{𝒪(y')} 𝒪(y) ⟶ ℋ(y)` is an isomorphism. Then `ℋ` is quasi-coherent.

Quasi-coherence is detected on the dense subsite of the flat objects over affine schemes
(Stacks 03DM), where every arrow is cartesian, so that the restriction of `ℋ` is quasi-coherent
by the core of Stacks 0GZV. -/
theorem isQuasicoherentOnSite_of_isIso_restrictionBaseChange_affine
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (subsiteRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
        (objectProperty B S hS 𝒳)).O))
    (hH : ∀ ⦃y y' : FlatFppf B S hS 𝒳⦄ (f : y ⟶ y'),
      IsAffine (𝒳.val.val.p.obj y.obj).left.1 → IsAffine (𝒳.val.val.p.obj y'.obj).left.1 →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (subsiteStructureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology
          le_rfl (objectProperty B S hS 𝒳)).obj) H.val f.op)) :
    H.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_of_isCoverDense
    (affineObject B S hS 𝒳).ι (inclusionTopology B S hS 𝒳)
    (subsiteStructureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
      (objectProperty B S hS 𝒳)) H fun U V _ => hH _ U.property V.property

end AlgebraicGeometry.Stack.FlatFppf

end
