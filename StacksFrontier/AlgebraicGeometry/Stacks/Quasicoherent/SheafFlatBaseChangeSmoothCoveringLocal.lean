module

public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveSmoothEtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleRestrictModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFlatObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeInverseImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The flat base change property is local for smooth coverings (Stacks 0764 (3), 07AQ (1))

Let `f j : 𝒵 j ⟶ 𝒳` be a family of smooth 1-morphisms of algebraic stacks with
`|𝒳| = ⋃ j, |f j|(|𝒵 j|)` and let `F` be a sheaf of `𝒪_𝒳`-modules on `𝒳_étale`. **Stacks 0764**
part (3) says that if every inverse image `f j^{-1} F` has the flat base change property of
**Stacks 0762** then so does `F`, and **Stacks 07AQ** part (1) combines it with **Stacks 075Y**:
if every `f j^{-1} F` lies in `LQCoh^fbc(𝒪_{𝒵 j})`, then `F` lies in `LQCoh^fbc(𝒪_𝒳)`.

The flat base change property is the one of the source, for the pullback of sheaves on the small
étale sites (`AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty`), and nothing is assumed of
`F` beyond the étale sheaf condition.

## The argument

Let `φ : x ⟶ y` lie over a flat morphism `U ⟶ V`, and write `θ_ψ` for the comparison of an arrow
`ψ` read as a morphism of sheaves (`AlgebraicGeometry.Stack.sheafifiedRestrictComparison`).

* By **Stacks 06XH** part (2) in family form
  (`AlgebraicGeometry.Stack.exists_etaleCovering_family_fibre_lift`) there is an étale covering
  `{V_i → V}` and arrows `α_i : f(z_i) ⟶ y` over its members, `z_i` an object of `𝒵 (a i)`.
* Over `U_i = U ×_V V_i` let `μ_i : x_i ⟶ x` be a cartesian lift of the first projection; the
  `μ_i` lie over a jointly surjective family of étale morphisms. Since `α_i` is cartesian,
  `μ_i ≫ φ = ν_i ≫ α_i` for an arrow `ν_i` over the second projection, which is flat.
* `θ_{ν_i}` is invertible because `ν_i` is a flat arrow into the image of `f (a i)`: lifting `z_i`
  along the second projection inside `𝒵 (a i)` gives `γ_i : w_i ⟶ z_i` and `ν_i = ι_i ≫ f(γ_i)`
  with `ι_i` over an identity; `θ_{f(γ_i)}` is invertible by the hypothesis on `f^{-1} F` and
  **Stacks 075D** part (4)
  (`isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_inverseImage_iff`).
* `θ_{ι_i}`, `θ_{α_i}` and `θ_{μ_i}` are invertible because those arrows lie over étale morphisms
  (**Stacks 075D** part (2) for modules,
  `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparison_of_etale`).
* The composition law **Stacks 075D** part (1), as two out of three, makes the pullback of `θ_φ`
  along every `μ_i` invertible, and pullback along a jointly surjective family of étale arrows is
  jointly conservative (`AlgebraicGeometry.Stack.isIso_of_isIso_sheafifiedPullbackComparison_map`).

## Main results

* `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparison_of_flat_of_image`: the comparison
  along a flat arrow into the image of a 1-morphism `g` is an isomorphism when `g^{-1} F` has the
  flat base change property.
* `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparison_of_isSmooth_jointlySurjective`: the
  comparison along a flat arrow is an isomorphism of sheaves.
* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isSmooth_jointlySurjective`:
  **Stacks 0764** part (3).
* `isLocallyQuasicoherentWithSheafFlatBaseChange_of_isSmooth_jointlySurjective`:
  **Stacks 07AQ** part (1).
* `locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_isSmooth_jointlySurjective`:
  the same for a module on the fppf site and the subcategory `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison along a flat arrow into the image of a 1-morphism.** Let `g : 𝒵 ⟶ 𝒳` be a
1-morphism of algebraic stacks such that `g^{-1} F` has the flat base change property of
Stacks 0762, `F` being an étale sheaf of `𝒪_𝒳`-modules. Then the comparison map of Stacks 06WC,
read as a morphism of sheaves, is an isomorphism along every arrow `ψ : z ⟶ g(w)` of `𝒳` lying
over a flat morphism of schemes, whatever the source `z`.

Pulling `w` back along the morphism of schemes below `ψ` gives `γ : w' ⟶ w` in `𝒵`, and `ψ`
factors as `ι ≫ g(γ)` with `ι` lying over an identity; the comparison along `g(γ)` is invertible by
the hypothesis and **Stacks 075D** part (4), the one along `ι` by **Stacks 075D** part (2), and the
composition law gives the one along `ψ`. -/
theorem isIso_sheafifiedRestrictComparison_of_flat_of_image
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒳)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hfbc : HasSheafFlatBaseChangeProperty B E h S hS
      (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS g.hom) (etaleTopology B)
      (etaleTopology_le_topology B) ((stackModulePresheafPullback.{u, w, u} B S hS g).obj F))
    {z : 𝒳.val.val.obj} {w₀ : 𝒵.val.val.obj}
    (ψ : z ⟶ (CatFiberedInGroupoids.homFunctor g.hom).obj w₀)
    (hflat : Flat (B.inclusion.map (𝒳.val.val.p.map ψ).left)) :
    IsIso (sheafifiedRestrictComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F ψ
      (restrictModuleToSmallEtale_isSheaf B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids z
        F hF)) := by
  set p := 𝒳.val.val.p
  have hfib := 𝒳.val.isFiberedInGroupoids
  have : p.IsFibered := hfib.isFibered
  have hM : ∀ a, Presheaf.IsSheaf (SmallEtale.topology E (p.obj a).left.1
      (contains_base B E h S hS p a))
      (restrictModuleToSmallEtale B E h S hS p hfib a (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf := fun a =>
    restrictModuleToSmallEtale_isSheaf B E h S hS p hfib a F hF
  let G := CatFiberedInGroupoids.homFunctor g.hom
  let q := G ⋙ p
  have : q.IsFibered := (isFiberedInGroupoids_homFunctor_comp B S hS g.hom).isFibered
  let k := p.map ψ
  let w' : 𝒵.val.val.obj := Functor.IsPreFibered.pullbackObj (p := q) (a := w₀) rfl k
  let γ : w' ⟶ w₀ := Functor.IsPreFibered.pullbackMap (p := q) (a := w₀) rfl k
  have hγlift : p.IsHomLift k (G.map γ) :=
    IsHomLift.of_fac' (p := p) _ _ (IsHomLift.domain_eq q k γ)
      (IsHomLift.codomain_eq q k γ) (IsHomLift.fac' q k γ)
  have : p.IsStronglyCartesian k (G.map γ) := hfib.isStronglyCartesian_homLift _ _
  have : p.IsHomLift k ψ := IsHomLift.map (p := p) ψ
  let ι : z ⟶ G.obj w' := Functor.IsStronglyCartesian.map p k (G.map γ)
    (Category.id_comp k).symm ψ
  have hιγ : ι ≫ G.map γ = ψ := Functor.IsStronglyCartesian.fac p k _ (Category.id_comp k).symm ψ
  have hιlift : p.IsHomLift (𝟙 _) ι :=
    Functor.IsStronglyCartesian.map_isHomLift p k _ (Category.id_comp k).symm ψ
  have hιet : Etale (B.inclusion.map (p.map ι).left) :=
    etale_map_left_of_isHomLift B S hS p (𝟙 _)
      (by rw [Over.id_left, CategoryTheory.Functor.map_id]; infer_instance) ι hιlift
  have hγflat : Flat (B.inclusion.map (p.map (G.map γ)).left) :=
    flat_map_left_of_isHomLift B S hS p k hflat _ hγlift
  have := isIso_sheafifiedRestrictComparison_of_etale B E h S hS p hfib ι hιet F (hM _)
  have : IsIso (sheafifiedRestrictComparison B E h S hS p hfib F (G.map γ) (hM _)) :=
    (isIso_sheafifiedRestrictModulePullbackComparison_iff B E h S hS p hfib (etaleTopology B)
      (etaleTopology_le_topology B) _ F (hM _)).2
      ((isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_inverseImage_iff
        B E h S hS p hfib G (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
        (isFibredOneMorphism_homFunctor_comp B S hS g.hom) F hF γ).1 (hfbc γ hγflat))
  have h₃ := isIso_sheafifiedRestrictComparison_comp B E h S hS p hfib F ι (G.map γ) (hM _)
    (hM _) (hM _)
  rwa [hιγ] at h₃

/-- The comparison along `ν ≫ α` is an isomorphism when `ν` is a flat arrow into the image of a
1-morphism `g` along which flat base change holds and `α` lies over an étale morphism. -/
private theorem isIso_sheafifiedRestrictComparison_comp_of_flat_of_image_of_etale
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒳)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hfbc : HasSheafFlatBaseChangeProperty B E h S hS
      (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS g.hom) (etaleTopology B)
      (etaleTopology_le_topology B) ((stackModulePresheafPullback.{u, w, u} B S hS g).obj F))
    {x y : 𝒳.val.val.obj} {w₀ : 𝒵.val.val.obj}
    (ν : x ⟶ (CatFiberedInGroupoids.homFunctor g.hom).obj w₀)
    (α : (CatFiberedInGroupoids.homFunctor g.hom).obj w₀ ⟶ y)
    (hν : Flat (B.inclusion.map (𝒳.val.val.p.map ν).left))
    (hα : Etale (B.inclusion.map (𝒳.val.val.p.map α).left)) :
    IsIso (sheafifiedRestrictComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F
      (ν ≫ α) (restrictModuleToSmallEtale_isSheaf B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids x F hF)) := by
  have hM := fun a => restrictModuleToSmallEtale_isSheaf B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids a F hF
  have := isIso_sheafifiedRestrictComparison_of_flat_of_image B E h S hS g F hF hfbc ν hν
  have := isIso_sheafifiedRestrictComparison_of_etale B E h S hS _ _ α hα F (hM _)
  exact isIso_sheafifiedRestrictComparison_comp B E h S hS _ _ F ν α (hM y) (hM _) (hM _)

/-- The pulled-back comparison along `φ` is an isomorphism over an étale arrow `μ` lying over
`fst`, when `fst ≫ p φ = snd ≫ k` with `snd` flat, `k` étale, and `α` strongly cartesian over `k`
with source in the image of a 1-morphism `g` along which flat base change holds. -/
private theorem isIso_sheafifiedPullbackComparison_map_of_comm_flat_etale
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒳)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hfbc : HasSheafFlatBaseChangeProperty B E h S hS
      (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS g.hom) (etaleTopology B)
      (etaleTopology_le_topology B) ((stackModulePresheafPullback.{u, w, u} B S hS g).obj F))
    {x y x' : 𝒳.val.val.obj} {w₀ : 𝒵.val.val.obj} (φ : x ⟶ y) (μ : x' ⟶ x)
    (α : (CatFiberedInGroupoids.homFunctor g.hom).obj w₀ ⟶ y)
    {P T : BigFppfOver B S hS} {fst : P ⟶ 𝒳.val.val.p.obj x} {snd : P ⟶ T}
    {k : T ⟶ 𝒳.val.val.p.obj y} (hcond : fst ≫ 𝒳.val.val.p.map φ = snd ≫ k)
    [𝒳.val.val.p.IsHomLift fst μ] [𝒳.val.val.p.IsStronglyCartesian k α]
    (hsnd : Flat (B.inclusion.map snd.left)) (hk : Etale (B.inclusion.map k.left))
    (hμ : Etale (B.inclusion.map (𝒳.val.val.p.map μ).left)) :
    IsIso ((sheafifiedPullbackComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) μ).map
        (sheafifiedRestrictComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F φ
          (restrictModuleToSmallEtale_isSheaf B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
            x F hF))) := by
  have hM := fun z => restrictModuleToSmallEtale_isSheaf B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids z F hF
  have : 𝒳.val.val.p.IsHomLift (fst ≫ 𝒳.val.val.p.map φ) (μ ≫ φ) :=
    IsHomLift.comp (p := 𝒳.val.val.p) fst (𝒳.val.val.p.map φ) μ φ
  let ν : x' ⟶ (CatFiberedInGroupoids.homFunctor g.hom).obj w₀ :=
    Functor.IsStronglyCartesian.map 𝒳.val.val.p k α hcond (μ ≫ φ)
  have hνα : ν ≫ α = μ ≫ φ := Functor.IsStronglyCartesian.fac 𝒳.val.val.p k α hcond (μ ≫ φ)
  have hνlift : 𝒳.val.val.p.IsHomLift snd ν :=
    Functor.IsStronglyCartesian.map_isHomLift 𝒳.val.val.p k α hcond (μ ≫ φ)
  have h₅ := isIso_sheafifiedRestrictComparison_comp_of_flat_of_image_of_etale B E h S hS
    g F hF hfbc ν α
    (flat_map_left_of_isHomLift B S hS 𝒳.val.val.p snd hsnd ν hνlift)
    (etale_map_left_of_isHomLift B S hS 𝒳.val.val.p k hk α inferInstance)
  rw [hνα] at h₅
  have := isIso_sheafifiedRestrictComparison_of_etale B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids μ hμ F (hM _)
  exact isIso_sheafifiedPullbackComparison_map_of_comp B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F μ φ (hM y) (hM x) (hM x')

/-- **The comparison along a flat arrow is an isomorphism, given smooth-local flat base change.**
Let `f j : 𝒵 j ⟶ 𝒳` be a jointly surjective family of smooth 1-morphisms of algebraic stacks and
`F` an étale sheaf of `𝒪_𝒳`-modules every inverse image `f j^{-1} F` of which has the flat base
change property of Stacks 0762. Then for every arrow `φ` of `𝒳` lying over a flat morphism of
schemes, the comparison map of Stacks 06WC read as a morphism of sheaves is an isomorphism.

See the module documentation for the argument. -/
theorem isIso_sheafifiedRestrictComparison_of_isSmooth_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hfbc : ∀ j, HasSheafFlatBaseChangeProperty B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom) (etaleTopology B)
      (etaleTopology_le_topology B) ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F))
    {x y : 𝒳.val.val.obj} (φ : x ⟶ y)
    (hflat : Flat (B.inclusion.map (𝒳.val.val.p.map φ).left)) :
    IsIso (sheafifiedRestrictComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F φ
      (restrictModuleToSmallEtale_isSheaf B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x
        F hF)) := by
  classical
  set p := 𝒳.val.val.p
  have hfib := 𝒳.val.isFiberedInGroupoids
  have : p.IsFibered := hfib.isFibered
  obtain ⟨I, W, e, a, hetale, hcov, hlift⟩ :=
    exists_etaleCovering_family_fibre_lift B S hS f hsmooth hjs (p.obj y) (Functor.Fiber.mk rfl)
  choose zz α₀ hα₀ using hlift
  let α : ∀ i, (CatFiberedInGroupoids.homFunctor (f (a i)).hom).obj (zz i) ⟶ y := α₀
  have hα : ∀ i, p.IsHomLift (Over.homMk (e i) rfl :
      (Over.mk (e i ≫ (p.obj y).hom) : BigFppfOver B S hS) ⟶ p.obj y) (α i) := hα₀
  have := hasPullbacks_bigFppfOver B S hS
  have := preservesPullbacks_bigFppfOverToScheme B S hS
  let k : ∀ i, (Over.mk (e i ≫ (p.obj y).hom) : BigFppfOver B S hS) ⟶ p.obj y :=
    fun i => Over.homMk (e i) rfl
  let fst : ∀ i, pullback (p.map φ) (k i) ⟶ p.obj x := fun i => pullback.fst _ _
  let snd : ∀ i, pullback (p.map φ) (k i) ⟶ Over.mk (e i ≫ (p.obj y).hom) :=
    fun i => pullback.snd _ _
  have hsq : ∀ i, IsPullback ((BigFppfOver.toScheme B S hS).map (fst i))
      ((BigFppfOver.toScheme B S hS).map (snd i)) ((BigFppfOver.toScheme B S hS).map (p.map φ))
      ((BigFppfOver.toScheme B S hS).map (k i)) := fun i =>
    (IsPullback.of_hasPullback (p.map φ) (k i)).map (BigFppfOver.toScheme B S hS)
  let xi : I → 𝒳.val.val.obj := fun i =>
    Functor.IsPreFibered.pullbackObj (p := p) (a := x) rfl (fst i)
  let μ : ∀ i, xi i ⟶ x := fun i => Functor.IsPreFibered.pullbackMap (p := p) (a := x) rfl (fst i)
  have hμlift : ∀ i, p.IsHomLift (fst i) (μ i) := fun i => inferInstance
  have hμet : ∀ i, Etale (B.inclusion.map (p.map (μ i)).left) := fun i =>
    etale_map_left_of_isHomLift B S hS p (fst i)
      (MorphismProperty.of_isPullback (P := @Etale) (hsq i).flip (hetale i)) (μ i) (hμlift i)
  have hμcov : ∀ t : B.inclusion.obj (p.obj x).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (μ i)).left) := fun t => by
    obtain ⟨i, s, hs⟩ := hcov ((B.inclusion.map (p.map φ).left) t)
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (hsq i) t s hs.symm
    exact ⟨i, range_map_left_of_isHomLift B S hS p (μ i) (hμlift i) ⟨z, hz⟩⟩
  refine isIso_of_isIso_sheafifiedPullbackComparison_map B E h S hS p hfib x xi μ hμet hμcov _
    fun i => ?_
  have := hα i
  have := hμlift i
  have : p.IsStronglyCartesian (k i) (α i) := hfib.isStronglyCartesian_homLift (k i) (α i)
  exact isIso_sheafifiedPullbackComparison_map_of_comm_flat_etale B E h S hS (f (a i)) F hF
    (hfbc (a i)) φ (μ i) (α i) (pullback.condition : fst i ≫ p.map φ = snd i ≫ k i)
    (MorphismProperty.of_isPullback (P := @Flat) (hsq i) hflat) (hetale i) (hμet i)

/-- **Stacks 07AQ, part (1).** Let `f j : 𝒵 j ⟶ 𝒳` be a family of smooth 1-morphisms of
algebraic stacks with `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be a sheaf of `𝒪_𝒳`-modules on
`𝒳_étale`. If every inverse image `f j^{-1} F` lies in `LQCoh^fbc(𝒪_{𝒵 j})`, then `F` lies in
`LQCoh^fbc(𝒪_𝒳)`.

Membership is read with the flat base change property of Stacks 0762 for the pullback of
sheaves (`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithSheafFlatBaseChange`). Local
quasi-coherence is **Stacks 075Y**
(`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isSmooth_jointlySurjective`) and the flat
base change property is **Stacks 0764** part (3)
(`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isSmooth_jointlySurjective`), as in
the source. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_of_isSmooth_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hlqc : ∀ j, IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F)) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F :=
  ⟨isLocallyQuasicoherent_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs F hF
      fun j => (hlqc j).1,
    hasSheafFlatBaseChangeProperty_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs F hF
      fun j => (hlqc j).2⟩

/-- **Stacks 07AQ, part (1)**, for a module on the fppf site: an `𝒪_𝒳`-module `F` on `𝒳_fppf` lies
in the subcategory `LQCoh^fbc(𝒪_𝒳)` of `Mod(𝒪_𝒳)` as soon as its inverse images along a jointly
surjective family of smooth 1-morphisms do. An fppf sheaf is an étale sheaf, and membership is
tested on the underlying presheaf of modules. -/
theorem locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_isSmooth_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : fppfModules B S hS 𝒳)
    (hlqc : ∀ j, IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F.val)) :
    lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 F :=
  isLocallyQuasicoherentWithSheafFlatBaseChange_of_isSmooth_jointlySurjective B E h S hS f
    hsmooth hjs F.val (F.isSheaf.of_le (BigFppfOver.associatedTopology_le_fppf B S hS _ .etale))
    hlqc

end AlgebraicGeometry.Stack

end
