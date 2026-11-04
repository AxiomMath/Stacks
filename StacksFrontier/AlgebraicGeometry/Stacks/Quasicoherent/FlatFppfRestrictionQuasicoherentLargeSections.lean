module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeCartesianFlatObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCartesianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineCoveringFamily
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsiteReflect
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCoarsening
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOnAChaoticSite

/-!
# Stacks 07B1 (2)(b) at module universe `u + 1`

Let `𝒳` be an algebraic stack and `g` the morphism of ringed topoi of Stacks 0788 for the flat-fppf
site. For `𝓕` in the faithful `LQCoh^fbc(𝒪_𝒳)` with sections in `Type (u + 1)`, the universe of
the coherator and of the direct images of Chapter 104, `g^{-1}𝓕` is quasi-coherent on
`(𝒳_{flat,fppf}, 𝒪_{𝒳_{flat,fppf}})`.

The source deduces this from the coherator (Stacks 0778, 0779). Here it is proved directly, so that
it can feed the construction of the coherator as `g_! g^*`: the flat objects over affine schemes
form a dense subsite, on which `g^{-1}𝓕` is cartesian along every arrow
(`AlgebraicGeometry.Stack.bijective_restrictionBaseChange_of_flatObject`); a cartesian module is
quasi-coherent for the chaotic topology (Stacks 0GZN, at a free module universe), hence for the
induced topology, and quasi-coherence reflects along a dense subsite.

## Main results

* `isQuasicoherentOnSite_moduleInverseImage_of_sheafFlatBaseChangeModulesSucc`: for `𝓕` in
  `LQCoh^fbc(𝒪_𝒳)` with sections in `Type (u + 1)`, the restriction `g^{-1}𝓕` to the flat-fppf
  site is quasi-coherent.

## References

* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
* [Stacks Project, Tag 0GZN](https://stacks.math.columbia.edu/tag/0GZN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.PresheafOfModules

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The flat objects lying over affine schemes cover the flat-fppf site. -/
instance isCoverDense_affineObject :
    (affineObject B S hS 𝒳).ι.IsCoverDense (topology B S hS 𝒳) where
  is_cover U := by
    obtain ⟨R, hR, hP⟩ := isCoveringFamily_isAffine B S hS 𝒳 U
    refine (topology B S hS 𝒳).superset_covering ?_ hR
    rw [Sieve.generate_le_iff]
    intro Y f hf
    exact ⟨⟨⟨Y, hP hf⟩, 𝟙 _, f, by simp⟩⟩

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology

/-- **Stacks 07B1 (2)(b) at module universe `u + 1`**: for a module `𝓕` in the faithful
`LQCoh^fbc(𝒪_𝒳)` of an algebraic stack, with sections in `Type (u + 1)`, the restriction
`g^{-1}𝓕` to the flat-fppf site is quasi-coherent. -/
theorem isQuasicoherentOnSite_moduleInverseImage_of_sheafFlatBaseChangeModulesSucc
    (F : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : sheafFlatBaseChangeModulesSucc B E h S hS 𝒳 F) :
    ((moduleInverseImage B S hS 𝒳).obj F).IsQuasicoherentOnSite := by
  let v := (affineObject B S hS 𝒳).ι
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_restriction
    (K := v.restrictedTopology (topology B S hS 𝒳)) v (subsiteRingStructureSheaf B S hS 𝒳)
    ((moduleInverseImage B S hS 𝒳).obj F) ?_
  refine SheafOfModules.isQuasicoherentOnSite_of_coarser.{u + 1, u, u, u + 1} (J' := ⊥) bot_le ?_
  rw [Stacks.ModulesOnACategory.isQuasicoherentOnSite_iff_isUniversalArrow.{u + 1, u, u, u + 1} rfl]
  intro U V a
  let Rc : (ObjectProperty.FullSubcategory (affineObject B S hS 𝒳))ᵒᵖ ⥤ CommRingCat.{u} :=
    (v ⋙ (objectProperty B S hS 𝒳).ι).op ⋙
      (AlgebraicGeometry.Stack.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B)
        (etaleTopology_le_topology B)).obj
  refine (CategoryTheory.Functor.isUniversalArrow_iff_isIso
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} (Rc.map a).hom) _).2 ?_
  have hb := bijective_restrictionBaseChange_of_flatObject B E h S hS 𝒳 F.val hF
    U.unop.obj.property V.unop.obj.property a.unop.hom.hom U.unop.property V.unop.property
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  have ht := (bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff_freeModuleUniverse.{
    u + 1, u, u + 1, u, u, u + 1}
    (v ⋙ (objectProperty B S hS 𝒳).ι)
    (AlgebraicGeometry.Stack.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B)).obj Rc (𝟙 _) (fun _ => inferInstance)
    F.val a).2 hb
  exact ht

end AlgebraicGeometry.Stack.FlatFppf

end
