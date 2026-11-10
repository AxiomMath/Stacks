module

public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChangeOfFieldsDescent
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.Deformation.Artin.Infinitesimal.FunctorDataComparison
public import StacksFrontier.Deformation.Artin.Infinitesimal.TrivialLift
public import StacksFrontier.Deformation.PredeformationTangent.DifferentialLinear
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# Finite dimensionality of `T_x(k)` and `Inf_x(k)` from natural comparisons

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category over the big fppf site of `S`, `k` a field and `x`
an object of `𝒳` over `Spec k`.  The tangent functor `T_x` and the functor `Inf_x` of
Stacks 07Y9 are `k`-linear functors of the site module `M`.  The usual way to show that their
values at `M = k` are finite dimensional, used in the proofs of Stacks 0D4S and 0DLL, is to map
them into, respectively onto them from, a `k`-linear functor `G` of `M` whose value at `k` is a
known finite-dimensional vector space (a space of derivations, or an `Ext` group): a family of
maps, natural in `M`, is linear at `M = k` by the product argument of Stacks 06I7
(`Deformation.isLinearMap_of_natural_on_fgModules`), so

* an injection `T_x(M) ↪ G(M)`, natural in `M`, bounds `T_x(k)`;
* a surjection `G(M) ↠ Inf_x(M)`, natural in `M`, bounds `Inf_x(k)`.

The maps need only be given on the isomorphism classes of lifts, respectively on the
infinitesimal automorphisms of the trivial deformations: they are not required to be linear,
and they are not required to be defined on the values of a particular tangent functor.  With
(RS*) and Stacks 0D18 this bounds the tangent space and the infinitesimal automorphisms of the
deformation category `𝓕_{𝒳,k,x}` of Stacks 07WY.

## Main results

* `Deformation.Artin.finiteDimensional_tangentFunctor_obj_of_natural_injective`
* `Deformation.Artin.finiteDimensional_tangentFunctor_obj_of_natural_injective_prod`: the same
  with a comparison into a product of two linear functors, injective only as a pair.
* `Deformation.Artin.finiteDimensional_infinitesimalAutomorphismFunctor_obj_of_natural_surjective`
* `Deformation.Artin.finiteDimensional_tangentModuleAt_of_natural_injective`,
  `Deformation.Artin.finiteDimensional_tangentModuleAt_of_natural_injective_prod` and
  `Deformation.Artin.finiteDimensional_localizedAutomorphismFunctorTangent_of_natural_surjective`:
  with (RS*) and Stacks 0D18, the same bounds for the tangent space and the infinitesimal
  automorphisms of the deformation category `𝓕_{𝒳,k,x}` of Stacks 07WY.

## References

* [Stacks Project, Tag 06I7](https://stacks.math.columbia.edu/tag/06I7)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
* [Stacks Project, Tag 0D18](https://stacks.math.columbia.edu/tag/0D18)
* [Stacks Project, Tag 0D4S](https://stacks.math.columbia.edu/tag/0D4S)
* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w v₂ v₃

@[expose] public noncomputable section

namespace Deformation.Artin

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (x : 𝒳)
  (hx : p.obj x = algebraOver k B S hS toS hk)

/-- **`T_x(k)` is finite dimensional when it embeds naturally into a finite-dimensional linear
functor.**  Let `G` be a `k`-linear functor on finite-dimensional `k`-vector spaces with `G(k)`
finite dimensional, and let `θ_M` send the isomorphism classes of lifts of `x` over `k[M]` to
`G(M)`, compatibly with the pullback of lifts along every linear map `M ⟶ N`, injectively at
`M = k`.  Then the value at `k` of every tangent functor of Stacks 07Y9 is finite dimensional.

The maps `θ_M` are not assumed linear: linearity at `k` follows from naturality (Stacks 06I7). -/
theorem finiteDimensional_tangentFunctor_obj_of_natural_injective
    (T : TangentFunctorData k B S hS toS hk p x hx)
    (G : FGModuleCat.{u} k ⥤ ModuleCat.{v₂} k) [G.Additive] [G.Linear k]
    [FiniteDimensional k (G.obj (FGModuleCat.of k k))]
    (θ : ∀ V : FGModuleCat.{u} k,
      squareZeroLiftClasses k B S hS toS hk p x hx ((fgSiteModule B hk).obj V) → G.obj V)
    (hθ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (a : squareZeroLiftClasses k B S hS toS hk p x hx ((fgSiteModule B hk).obj V))
      (b : squareZeroLiftClasses k B S hS toS hk p x hx ((fgSiteModule B hk).obj W)),
      IsPullbackOfSquareZeroLift k B S hS toS hk p x hx ((fgSiteModule B hk).map f) a b →
        θ W b = G.map f (θ V a))
    (hinj : Function.Injective (θ (FGModuleCat.of k k))) :
    FiniteDimensional k (T.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k))) := by
  have : (fgSiteModule B hk).Additive := ⟨rfl⟩
  have : (fgSiteModule B hk).Linear k := ⟨by intros; rfl⟩
  let F := fgSiteModule B hk ⋙ T.functor
  let t : ∀ V : FGModuleCat.{u} k, F.obj V → G.obj V := fun V a =>
    θ V (T.liftEquiv _ a)
  have hlin := isLinearMap_of_natural_on_fgModules k F G t fun f a =>
    hθ f _ _ (T.liftEquiv_natural ((fgSiteModule B hk).map f) a)
  have hinj' : Function.Injective (t (FGModuleCat.of k k)) :=
    hinj.comp (T.liftEquiv _).injective
  exact FiniteDimensional.of_injective (IsLinearMap.mk' _ hlin) hinj'

/-- **`T_x(k)` is finite dimensional when it embeds naturally into a product of two
finite-dimensional linear functors.**  The two components `θ₁`, `θ₂` are each natural for the
pullback of lifts, and only the pair is required to be injective at `M = k`.  This is the shape
in which a lift is recorded by two invariants, e.g. its image in a factor of a 2-fibre product
and a class in an `Ext` group. -/
theorem finiteDimensional_tangentFunctor_obj_of_natural_injective_prod
    (T : TangentFunctorData k B S hS toS hk p x hx)
    (G₁ : FGModuleCat.{u} k ⥤ ModuleCat.{v₂} k) [G₁.Additive] [G₁.Linear k]
    [FiniteDimensional k (G₁.obj (FGModuleCat.of k k))]
    (G₂ : FGModuleCat.{u} k ⥤ ModuleCat.{v₃} k) [G₂.Additive] [G₂.Linear k]
    [FiniteDimensional k (G₂.obj (FGModuleCat.of k k))]
    (θ₁ : ∀ V : FGModuleCat.{u} k,
      squareZeroLiftClasses k B S hS toS hk p x hx ((fgSiteModule B hk).obj V) → G₁.obj V)
    (θ₂ : ∀ V : FGModuleCat.{u} k,
      squareZeroLiftClasses k B S hS toS hk p x hx ((fgSiteModule B hk).obj V) → G₂.obj V)
    (hθ₁ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (a : squareZeroLiftClasses k B S hS toS hk p x hx ((fgSiteModule B hk).obj V))
      (b : squareZeroLiftClasses k B S hS toS hk p x hx ((fgSiteModule B hk).obj W)),
      IsPullbackOfSquareZeroLift k B S hS toS hk p x hx ((fgSiteModule B hk).map f) a b →
        θ₁ W b = G₁.map f (θ₁ V a))
    (hθ₂ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (a : squareZeroLiftClasses k B S hS toS hk p x hx ((fgSiteModule B hk).obj V))
      (b : squareZeroLiftClasses k B S hS toS hk p x hx ((fgSiteModule B hk).obj W)),
      IsPullbackOfSquareZeroLift k B S hS toS hk p x hx ((fgSiteModule B hk).map f) a b →
        θ₂ W b = G₂.map f (θ₂ V a))
    (hinj : Function.Injective fun a => (θ₁ (FGModuleCat.of k k) a, θ₂ (FGModuleCat.of k k) a)) :
    FiniteDimensional k (T.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k))) := by
  have : (fgSiteModule B hk).Additive := ⟨rfl⟩
  have : (fgSiteModule B hk).Linear k := ⟨by intros; rfl⟩
  let F := fgSiteModule B hk ⋙ T.functor
  let t₁ : ∀ V : FGModuleCat.{u} k, F.obj V → G₁.obj V := fun V a => θ₁ V (T.liftEquiv _ a)
  let t₂ : ∀ V : FGModuleCat.{u} k, F.obj V → G₂.obj V := fun V a => θ₂ V (T.liftEquiv _ a)
  have hlin₁ := isLinearMap_of_natural_on_fgModules k F G₁ t₁ fun f a =>
    hθ₁ f _ _ (T.liftEquiv_natural ((fgSiteModule B hk).map f) a)
  have hlin₂ := isLinearMap_of_natural_on_fgModules k F G₂ t₂ fun f a =>
    hθ₂ f _ _ (T.liftEquiv_natural ((fgSiteModule B hk).map f) a)
  let L := (IsLinearMap.mk' _ hlin₁).prod (IsLinearMap.mk' _ hlin₂)
  exact FiniteDimensional.of_injective L fun _ _ hab => (T.liftEquiv _).injective (hinj hab)

variable (hp : p.IsFiberedInGroupoids)

/-- **`Inf_x(k)` is finite dimensional when a finite-dimensional linear functor surjects
naturally onto it.**  Let `G` be a `k`-linear functor on finite-dimensional `k`-vector spaces
with `G(k)` finite dimensional, and let `θ_M` send `G(M)` to the infinitesimal automorphisms of
the trivial deformation of `x` over `k[M]`, compatibly with the transition maps of Stacks 07Y9
along every linear map `M ⟶ N`, surjectively at `M = k`.  Then the value at `k` of every functor
`Inf_x` of Stacks 07Y9 is finite dimensional.

The maps `θ_M` are not assumed linear: linearity at `k` follows from naturality (Stacks 06I7). -/
theorem finiteDimensional_infinitesimalAutomorphismFunctor_obj_of_natural_surjective
    (I : InfinitesimalAutomorphismFunctorData k B S hS toS hk p x hx hp)
    (G : FGModuleCat.{u} k ⥤ ModuleCat.{v₂} k) [G.Additive] [G.Linear k]
    [FiniteDimensional k (G.obj (FGModuleCat.of k k))]
    (θ : ∀ V : FGModuleCat.{u} k, G.obj V →
      (trivialDeformation k B S hS toS hk p x hx hp ((fgSiteModule B hk).obj V) ⟶
        trivialDeformation k B S hS toS hk p x hx hp ((fgSiteModule B hk).obj V)))
    (hθ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W) (g : G.obj V),
      θ W (G.map f g) =
        (infinitesimalAutomorphismSetFunctor k B S hS toS hk p x hx hp).map
          ((fgSiteModule B hk).map f) (θ V g))
    (hsurj : Function.Surjective (θ (FGModuleCat.of k k))) :
    FiniteDimensional k (I.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k))) := by
  have : (fgSiteModule B hk).Additive := ⟨rfl⟩
  have : (fgSiteModule B hk).Linear k := ⟨by intros; rfl⟩
  let F := fgSiteModule B hk ⋙ I.functor
  let t : ∀ V : FGModuleCat.{u} k, G.obj V → F.obj V := fun V g =>
    (I.autEquiv _).symm (θ V g)
  have ht : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W) (g : G.obj V),
      t W ((G.map f) g) = (F.map f) (t V g) := by
    intro V W f g
    apply (I.autEquiv _).injective
    change I.autEquiv _ ((I.autEquiv _).symm (θ W (G.map f g))) =
      I.autEquiv _ (I.functor.map ((fgSiteModule B hk).map f) ((I.autEquiv _).symm (θ V g)))
    rw [Equiv.apply_symm_apply, I.autEquiv_natural, Equiv.apply_symm_apply]
    exact hθ f g
  have hlin := isLinearMap_of_natural_on_fgModules k G F t ht
  have hsurj' : Function.Surjective (t (FGModuleCat.of k k)) :=
    (I.autEquiv _).symm.surjective.comp hsurj
  exact LinearMap.finiteDimensional_of_surjective (IsLinearMap.mk' _ hlin)
    (LinearMap.range_eq_top.mpr hsurj')

attribute [local instance] PredeformationConstruction.category

section Predeformation

variable {Λ : Type u} [CommRing Λ] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (hRS : SatisfiesRSStar B S hS p hp)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx' : p.obj x = algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk)

/-- The tangent module of `𝓕_{𝒳,k,x}` is finite dimensional once the tangent functor of
Stacks 07Y9 is finite dimensional at `k`. -/
private theorem finiteDimensional_tangentModuleAt_of_tangentFunctor
    (hD : IsDeformationCategory.{u, u, u}
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx₀).projection)
    (h : FiniteDimensional k ((tangentFunctor k B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk p x hx' hp hRS).functor.obj
        ((fgSiteModule B hk).obj (FGModuleCat.of k k)))) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx₀).projection) hD
      (FGModuleCat.of k k)) := by
  let toS := Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ
  let T := tangentFunctor k B S hS toS hk _ x hx' hp hRS
  let : Fact (IsPredeformationCategory (BasedCategory.ofFunctor (predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x hx₀).projection).p) := ⟨hD.predeformation⟩
  let : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (BasedCategory.ofFunctor (predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x hx₀).projection)
        hD.predeformation.cofibered))) := ⟨tangentConditionS2 hD⟩
  obtain ⟨e, -⟩ := tangentSpace_deformationCategory_linearEquiv_of_tangentFunctorData B S hS iΛ
    toS hk _ hp x hx₀ hx' T hD
  have := h
  exact (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt
    (𝓕 := BasedCategory.ofFunctor (predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x hx₀).projection) hD).mp e.symm.finiteDimensional

include hp hRS in
/-- **The tangent space of Stacks 07WY is finite dimensional when the lifts embed naturally into
a finite-dimensional linear functor.**  Let `p` be fibred in groupoids and satisfy (RS*), let
`k` be presented through `Spec k ⟶ Spec Λ ⟶ S`, and let `x` lie over `Spec k`.  If the
isomorphism classes of lifts of `x` over `k[M]` map, naturally in `M` and injectively at
`M = k`, to a `k`-linear functor `G` with `G(k)` finite dimensional, then for every witness that
`𝓕_{𝒳,k,x}` is a deformation category its tangent module at `k` is finite dimensional.

The tangent functor of Stacks 07Y9 exists by (RS*); its value at `k` is finite dimensional by
`Deformation.Artin.finiteDimensional_tangentFunctor_obj_of_natural_injective`, and Stacks 0D18
identifies it with the tangent space of `𝓕_{𝒳,k,x}`. -/
theorem finiteDimensional_tangentModuleAt_of_natural_injective
    (G : FGModuleCat.{u} k ⥤ ModuleCat.{v₂} k) [G.Additive] [G.Linear k]
    [FiniteDimensional k (G.obj (FGModuleCat.of k k))]
    (θ : ∀ V : FGModuleCat.{u} k,
      squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk p x
        hx' ((fgSiteModule B hk).obj V) → G.obj V)
    (hθ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (a : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk p x hx' ((fgSiteModule B hk).obj V))
      (b : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk p x hx' ((fgSiteModule B hk).obj W)),
      IsPullbackOfSquareZeroLift k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk p x hx' ((fgSiteModule B hk).map f) a b →
        θ W b = G.map f (θ V a))
    (hinj : Function.Injective (θ (FGModuleCat.of k k)))
    (hD : IsDeformationCategory.{u, u, u}
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx₀).projection) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx₀).projection) hD
      (FGModuleCat.of k k)) := by
  exact finiteDimensional_tangentModuleAt_of_tangentFunctor (hRS := hRS) (hD := hD)
    (h := finiteDimensional_tangentFunctor_obj_of_natural_injective B S hS _ hk p x hx' _ G θ hθ
      hinj)

include hp hRS in
/-- **The tangent space of Stacks 07WY is finite dimensional when the lifts embed naturally into
a product of two finite-dimensional linear functors.**  The variant of
`Deformation.Artin.finiteDimensional_tangentModuleAt_of_natural_injective` in which the
comparison has two components, each natural, injective only as a pair. -/
theorem finiteDimensional_tangentModuleAt_of_natural_injective_prod
    (G₁ : FGModuleCat.{u} k ⥤ ModuleCat.{v₂} k) [G₁.Additive] [G₁.Linear k]
    [FiniteDimensional k (G₁.obj (FGModuleCat.of k k))]
    (G₂ : FGModuleCat.{u} k ⥤ ModuleCat.{v₃} k) [G₂.Additive] [G₂.Linear k]
    [FiniteDimensional k (G₂.obj (FGModuleCat.of k k))]
    (θ₁ : ∀ V : FGModuleCat.{u} k,
      squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk p x
        hx' ((fgSiteModule B hk).obj V) → G₁.obj V)
    (θ₂ : ∀ V : FGModuleCat.{u} k,
      squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk p x
        hx' ((fgSiteModule B hk).obj V) → G₂.obj V)
    (hθ₁ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (a : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk p x hx' ((fgSiteModule B hk).obj V))
      (b : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk p x hx' ((fgSiteModule B hk).obj W)),
      IsPullbackOfSquareZeroLift k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk p x hx' ((fgSiteModule B hk).map f) a b →
        θ₁ W b = G₁.map f (θ₁ V a))
    (hθ₂ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (a : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk p x hx' ((fgSiteModule B hk).obj V))
      (b : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk p x hx' ((fgSiteModule B hk).obj W)),
      IsPullbackOfSquareZeroLift k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk p x hx' ((fgSiteModule B hk).map f) a b →
        θ₂ W b = G₂.map f (θ₂ V a))
    (hinj : Function.Injective fun a => (θ₁ (FGModuleCat.of k k) a, θ₂ (FGModuleCat.of k k) a))
    (hD : IsDeformationCategory.{u, u, u}
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx₀).projection) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx₀).projection) hD
      (FGModuleCat.of k k)) := by
  exact finiteDimensional_tangentModuleAt_of_tangentFunctor (hRS := hRS) (hD := hD)
    (h := finiteDimensional_tangentFunctor_obj_of_natural_injective_prod B S hS _ hk p x hx' _ G₁ G₂
      θ₁ θ₂ hθ₁ hθ₂ hinj)

include hRS in
/-- **The infinitesimal automorphisms of Stacks 07WY are finite dimensional when a
finite-dimensional linear functor surjects naturally onto them.**  Let `p` be fibred in
groupoids and satisfy (RS*), let `k` be presented through `Spec k ⟶ Spec Λ ⟶ S`, and let `x`
lie over `Spec k`.  If a `k`-linear functor `G` with `G(k)` finite dimensional maps, naturally in
`M` and surjectively at `M = k`, onto the infinitesimal automorphisms of the trivial deformations
of `x` over `k[M]`, then for every witness that `𝓕_{𝒳,k,x}` is a deformation category, every
object `y` of its special fibre and every choice of pushforwards of `y`, the space
`Inf(𝓕_{𝒳,k,x})` of Stacks 07WY is finite dimensional.

The functor `Inf_x` of Stacks 07Y9 exists by (RS*); its value at `k` is finite dimensional by
`Deformation.Artin.finiteDimensional_infinitesimalAutomorphismFunctor_obj_of_natural_surjective`,
and Stacks 0D18 identifies it with `Inf(𝓕_{𝒳,k,x})`. -/
theorem finiteDimensional_localizedAutomorphismFunctorTangent_of_natural_surjective
    (G : FGModuleCat.{u} k ⥤ ModuleCat.{v₂} k) [G.Additive] [G.Linear k]
    [FiniteDimensional k (G.obj (FGModuleCat.of k k))]
    (θ : ∀ V : FGModuleCat.{u} k, G.obj V →
      (trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk p x
          hx' hp ((fgSiteModule B hk).obj V) ⟶
        trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk p x
          hx' hp ((fgSiteModule B hk).obj V)))
    (hθ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W) (g : G.obj V),
      θ W (G.map f g) =
        (infinitesimalAutomorphismSetFunctor k B S hS
          (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk p x hx' hp).map
          ((fgSiteModule B hk).map f) (θ V g))
    (hsurj : Function.Surjective (θ (FGModuleCat.of k k)))
    (hD : IsDeformationCategory.{u, u, u}
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx₀).projection)
    (y : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx₀).carrier)
    (hy : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx₀).projection.obj y =
      residueFieldObject Λ k)
    (P : ChosenPushforwardsAt
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx₀).projection y) :
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P) := by
  let := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
  let := naturalLocalizedTangentModule P hD.satisfiesRS
  let toS := Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ
  let I := infinitesimalAutomorphismFunctor k B S hS toS hk _ x hx' hp hRS
  obtain ⟨E⟩ := nonempty_linearEquiv_infinitesimalAutomorphismLinearLift B S hS iΛ toS hk _ hp x
    hx₀ hx' I hD y hy P (FGModuleCat.of k (ULift.{u} k))
  have := finiteDimensional_infinitesimalAutomorphismFunctor_obj_of_natural_surjective B S hS
    toS hk p x hx' hp I G θ hθ hsurj
  have : FiniteDimensional k (I.functor.obj ((fgSiteModule B hk).obj
      (FGModuleCat.of k (ULift.{u} k)))) :=
    (I.functor.mapIso ((fgSiteModule B hk).mapIso
      fgModuleCatULiftSelfIso)).toLinearEquiv.symm.finiteDimensional
  have : FiniteDimensional k ↥((infinitesimalAutomorphismLinearLift.{u, u, u} P
      hD.satisfiesRS).functor.obj (FGModuleCat.of k (ULift.{u} k))) := E.symm.finiteDimensional
  exact Module.Finite.equiv (tangentCarrierLinearEquiv.{u, u, u} P hD.satisfiesRS)

end Predeformation

end Deformation.Artin

end
