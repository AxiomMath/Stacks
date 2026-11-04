module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveSmoothEtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentPullback

/-!
# Local quasi-coherence descends along a smooth covering family (Stacks 075Y)

Let `f j : 𝒵 j ⟶ 𝒳`, `j ∈ J`, be a family of smooth 1-morphisms of algebraic stacks over `S`
whose images cover the points of `𝒳`, that is `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be a sheaf
of `𝒪_𝒳`-modules on `𝒳_étale`. Stacks 075Y says that if every inverse image `f j^{-1} F` is
locally quasi-coherent, then so is `F`.

## Main definitions

* `AlgebraicGeometry.Stack.stackModulePresheafPullback`: the inverse image of a presheaf of
  modules on the étale site of an algebraic stack along a 1-morphism of algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale_image`: at the image
  of an object of the source, the restriction of `F` is quasi-coherent as soon as the inverse
  image of `F` is locally quasi-coherent.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isSmooth_jointlySurjective`: a sheaf of
  modules whose inverse images along a jointly surjective family of smooth 1-morphisms are locally
  quasi-coherent is locally quasi-coherent.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w v' w' m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure functor of the source of a 1-morphism of categories fibred in groupoids,
written as the morphism's functor followed by the structure functor of the target, is again
fibred in groupoids. -/
theorem isFiberedInGroupoids_homFunctor_comp
    {𝒵 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (G : 𝒵 ⟶ 𝒳) :
    (CatFiberedInGroupoids.homFunctor G ⋙ 𝒳.val.p).IsFiberedInGroupoids := by
  rw [CatFiberedInGroupoids.homFunctor_comp_p]
  exact 𝒵.isFiberedInGroupoids

/-- The functor of a 1-morphism of categories fibred in groupoids is a fibred 1-morphism from
that presentation of the source's structure functor to the target's. -/
theorem isFibredOneMorphism_homFunctor_comp
    {𝒵 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (G : 𝒵 ⟶ 𝒳) :
    (CatFiberedInGroupoids.homFunctor G ⋙ 𝒳.val.p).IsFibredOneMorphism 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor G) :=
  𝒳.isFiberedInGroupoids.isFibredOneMorphism rfl

/-- The inverse image of a presheaf of modules on the étale site of an algebraic stack along a
1-morphism of algebraic stacks: restriction along the morphism's functor, with the scalars moved
by the identification of the two structure sheaves. -/
noncomputable abbrev stackModulePresheafPullback
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒳) :
    PresheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj ⥤
      PresheafOfModules.{m} (ringStructureSheafCore B S hS
        (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
        (etaleTopology B) (etaleTopology_le_topology B)).obj :=
  modulePresheafPullback.{u, u + 1, u, u + 1, u, m} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
    (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)

/-- The underlying scheme morphism of an `eqToHom` in the site is an isomorphism. -/
private theorem isIso_inclusion_map_eqToHom_left {U V : BigFppfOver B S hS} (e : U = V) :
    IsIso (B.inclusion.map (eqToHom e).left) := by
  change IsIso ((Over.forget (B.obj hS) ⋙ B.inclusion).map (eqToHom e))
  infer_instance

/-- An arrow of a category fibred in groupoids lying over an étale morphism of the site has
étale underlying morphism of schemes. -/
theorem etale_map_left_of_isHomLift {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) {U V : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : Etale (B.inclusion.map k.left)) {y x : 𝒳} (φ : y ⟶ x) (hφ : p.IsHomLift k φ) :
    Etale (B.inclusion.map (p.map φ).left) := by
  have := hφ
  have hleft : (p.map φ).left =
      (eqToHom (IsHomLift.domain_eq p k φ)).left ≫ k.left ≫
        (eqToHom (IsHomLift.codomain_eq p k φ).symm).left := by
    rw [IsHomLift.fac' p k φ]; rfl
  have := isIso_inclusion_map_eqToHom_left B S hS (IsHomLift.domain_eq p k φ)
  have := isIso_inclusion_map_eqToHom_left B S hS (IsHomLift.codomain_eq p k φ).symm
  have := hk
  rw [hleft, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- An arrow of a category fibred in groupoids lying over a morphism `k` of the site has the same
image on points as `k`. -/
theorem range_map_left_of_isHomLift {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) {y x : 𝒳} {V : BigFppfOver B S hS} {k : V ⟶ p.obj x}
    (φ : y ⟶ x) (hφ : p.IsHomLift k φ) {t : B.inclusion.obj (p.obj x).left}
    (ht : t ∈ Set.range (B.inclusion.map k.left)) :
    t ∈ Set.range (B.inclusion.map (p.map φ).left) := by
  have := hφ
  have hleft : (p.map φ).left = (eqToHom (IsHomLift.domain_eq p k φ)).left ≫ k.left := by
    rw [IsHomLift.fac' p k φ, eqToHom_refl, Category.comp_id]; rfl
  obtain ⟨s, rfl⟩ := ht
  have := isIso_inclusion_map_eqToHom_left B S hS (IsHomLift.domain_eq p k φ)
  refine ⟨inv (B.inclusion.map (eqToHom (IsHomLift.domain_eq p k φ)).left) s, ?_⟩
  rw [hleft, Functor.map_comp, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (inv _),
    IsIso.inv_hom_id]
  rfl

/-- If the inverse image of `F` along a 1-morphism of categories fibred in groupoids is locally
quasi-coherent, then the small étale restriction of `F` at the image of any object of the source
is quasi-coherent. -/
theorem isQuasicoherentOnSite_restrictModuleToSmallEtale_image
    {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
    (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (g : 𝒳 ⥤ 𝒴)
    (hp : (g ⋙ q).IsFiberedInGroupoids) (hg : (g ⋙ q).IsFibredOneMorphism q g)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS q (etaleTopology B)) F.presheaf)
    (hlqc : IsLocallyQuasicoherent B E h S hS (g ⋙ q) hp
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq g hp).obj F))
    (z : 𝒳) :
    (⟨restrictModuleToSmallEtale B E h S hS q hq (g.obj z) (etaleTopology B)
        (etaleTopology_le_topology B) F,
      restrictModuleToSmallEtale_isSheaf B E h S hS q hq (g.obj z) F hF⟩ :
      SheafOfModules (SmallEtale.structureSheaf E (q.obj (g.obj z)).left.1
        (contains_base B E h S hS q (g.obj z)))).IsQuasicoherentOnSite := by
  let Rsmall := SmallEtale.structureSheaf E (q.obj (g.obj z)).left.1
    (contains_base B E h S hS q (g.obj z))
  let eModule := restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
    B E h S hS q hq g hp F hF hg z
  obtain ⟨hMsrc, hQCsrc⟩ := hlqc.2 z
  let eSheaf : (⟨_, hMsrc⟩ : SheafOfModules Rsmall) ≅
      ⟨_, restrictModuleToSmallEtale_isSheaf B E h S hS q hq (g.obj z) F hF⟩ :=
    (SheafOfModules.fullyFaithfulForget Rsmall).preimageIso eModule
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso eSheaf hQCsrc

/-- Let `f j : 𝒵 j ⟶ 𝒳` be a family of smooth 1-morphisms of algebraic stacks over `S` with
`|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be a sheaf of `𝒪_𝒳`-modules on `𝒳_étale`. If every inverse
image `f j^{-1} F` is locally quasi-coherent, then so is `F`. -/
@[stacks 075Y]
theorem isLocallyQuasicoherent_of_isSmooth_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hlqc : ∀ j, IsLocallyQuasicoherent B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F)) :
    IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F := by
  classical
  refine ⟨hF, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS _ _ x F hF, ?_⟩⟩
  obtain ⟨I, W, e, a, hetale, hcov, hlift⟩ :=
    exists_etaleCovering_family_fibre_lift B S hS f hsmooth hjs
      (𝒳.val.val.p.obj x) (Functor.Fiber.mk rfl)
  choose zz αα hαα using hlift
  exact isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover
    B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x F hF
    (fun i => (CatFiberedInGroupoids.homFunctor (f (a i)).hom).obj (zz i)) αα
    (fun i => etale_map_left_of_isHomLift B S hS 𝒳.val.val.p _ (hetale i) (αα i) (hαα i))
    (fun t => (hcov t).imp fun i hi =>
      range_map_left_of_isHomLift B S hS 𝒳.val.val.p (αα i) (hαα i) hi)
    (fun i => isQuasicoherentOnSite_restrictModuleToSmallEtale_image.{u, u + 1, u, u + 1, u, u}
      B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor (f (a i)).hom)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f (a i)).hom)
      (isFibredOneMorphism_homFunctor_comp B S hS (f (a i)).hom) F hF (hlqc (a i)) (zz i))

end AlgebraicGeometry.Stack

end
