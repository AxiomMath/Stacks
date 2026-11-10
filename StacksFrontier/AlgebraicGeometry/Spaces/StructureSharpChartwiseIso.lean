module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalIntegralEtaleChart

/-!
# Invertibility of `𝒪_Y ⟶ f_*𝒪_X` tested on global functions over the charts

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  This file reduces the
invertibility of the structure map `𝒪_Y ⟶ f_*𝒪_X` of the morphism of small étale ringed topoi
(Stacks 03G8) to a statement about global functions: it suffices that, for every étale scheme
chart `V` of `Y` in a family having enough objects, pullback of functions
`Γ(V, 𝒪_V) ⟶ Γ(X ×_Y V, 𝒪)` is bijective.

The link is `AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions`, the injective
homomorphism from the sections of `f_*𝒪_X` over `V` to the global functions on `X ×_Y V`, which
carries the structure map to pullback of functions.  Bijectivity of the composite and
injectivity of the second factor give bijectivity of the structure map on sections over `V`.

When `Y` is normal and integral, the family of étale charts whose scheme is affine, normal and
integral has enough objects: every étale chart is covered by affine ones, and every point of an
affine étale chart has a normal integral affine open neighbourhood inside it, by the shrinking
step of Stacks 0AYH.  This is the reduction to a normal integral affine base used in the proof
of Stacks 0AYI.

## Main results

* `CategoryTheory.GrothendieckTopology.HasEnoughObjects.of_forall_exists_covering`: if every
  object is covered by `P`-objects and every `P`-object is covered by `Q`-objects, then every
  object is covered by `Q`-objects.
* `CategoryTheory.Sheaf.isIso_of_hasEnoughObjects_bijective`: a morphism of sheaves valued in a
  concrete category which is bijective on sections over a family of objects with enough objects
  is invertible.
* `AlgebraicGeometry.Space.hasEnoughObjects_isNormalIntegralAffineChart`: on a normal integral
  algebraic space, the normal integral affine étale charts have enough objects.
* `AlgebraicGeometry.Space.isIso_fSharp_of_forall_bijective_globalFunctions`: the reduction of
  invertibility of `𝒪_Y ⟶ f_*𝒪_X` to bijectivity of pullback of functions over the charts.

## References

* [Stacks Project, Tag 0AYI](https://stacks.math.columbia.edu/tag/0AYI)
* [Stacks Project, Tag 0AYH](https://stacks.math.columbia.edu/tag/0AYH)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' v u' u

namespace CategoryTheory

namespace GrothendieckTopology

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Enough objects is transitive.**  If every object of the site is covered by objects with
`P`, and every object with `P` is covered by objects with `Q`, then every object is covered by
objects with `Q`: the composite family, indexed by pairs, generates a covering sieve by the
transitivity axiom. -/
theorem HasEnoughObjects.of_forall_exists_covering {P Q : ObjectProperty C}
    (hP : J.HasEnoughObjects P)
    (hPQ : ∀ U : C, P U → ∃ (I : Type v) (Ui : I → C) (f : ∀ i, Ui i ⟶ U),
      Sieve.ofArrows Ui f ∈ J U ∧ ∀ i, Q (Ui i)) :
    J.HasEnoughObjects Q := by
  intro U
  obtain ⟨I, Ui, f, hf, hPi⟩ := hP U
  choose Ii Uij fij hij hQ using fun i => hPQ (Ui i) (hPi i)
  refine ⟨Σ i, Ii i, fun k => Uij k.1 k.2, fun k => fij k.1 k.2 ≫ f k.1, ?_,
    fun k => hQ k.1 k.2⟩
  refine J.transitive hf _ ?_
  intro W g hg
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  rw [Sieve.pullback_comp]
  apply J.pullback_stable
  refine J.superset_covering ?_ (hij i)
  intro Z h hh
  obtain ⟨j, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
  rw [Sieve.pullback_apply, Category.assoc]
  exact (Sieve.ofArrows _ _).downward_closed
    (Sieve.ofArrows_mk (fun k : Σ i, Ii i => Uij k.1 k.2) (fun k => fij k.1 k.2 ≫ f k.1)
      ⟨i, j⟩) b

end GrothendieckTopology

namespace Sheaf

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- **Bijectivity on a family of objects with enough objects makes a morphism of sheaves
invertible.**  For sheaves valued in a concrete category whose forgetful functor reflects
isomorphisms and preserves the sheaf condition: a morphism which is bijective on sections over
every object of a family covering every object is locally injective and locally surjective,
hence invertible. -/
theorem isIso_of_hasEnoughObjects_bijective [(forget A).ReflectsIsomorphisms]
    [J.HasSheafCompose (forget A)] {F G : Sheaf J A} (φ : F ⟶ G) {P : ObjectProperty C}
    (hP : J.HasEnoughObjects P)
    (hbij : ∀ ⦃U : C⦄, P U → Function.Bijective (φ.hom.app (op U))) :
    IsIso φ :=
  (Sheaf.isLocallyBijective_iff_isIso φ).1
    ⟨Presheaf.isLocallyInjective_of_hasEnoughObjects_injective J φ.hom hP
        fun _ h => (hbij h).injective,
      Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective J φ.hom hP
        fun _ h => (hbij h).surjective⟩

end Sheaf

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Normal integral affine charts -/

/-- An étale chart of `F` is a *normal integral affine chart* when its underlying scheme is
affine, normal and integral. -/
abbrev IsNormalIntegralAffineChart (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    ObjectProperty (SmallEtale B S hS F) :=
  fun V ↦ IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)) ∧
    IsNormal ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)) ∧
    IsIntegral ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V))

/-- **On a normal integral algebraic space the normal integral affine étale charts have enough
objects.**  Every étale chart is covered by affine ones
(`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`), and every point of an affine étale
chart has an affine open neighbourhood inside it which is a normal integral scheme, by the
shrinking step of Stacks 0AYH
(`AlgebraicGeometry.Space.exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart`);
those opens, read as charts, cover the chart pointwise. -/
theorem hasEnoughObjects_isNormalIntegralAffineChart (Y : AlgebraicSpaces B S hS)
    (hnormal : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsNormal T))
    (hintegral : IsIntegralSpace B S hS Y.1) :
    (SmallEtale.topology B S hS Y.1).HasEnoughObjects
      (IsNormalIntegralAffineChart B S hS Y.1) := by
  refine GrothendieckTopology.HasEnoughObjects.of_forall_exists_covering
    (hasEnoughObjects_isAffineChart B S hS Y.1) fun V hV => ?_
  let T : B.Schemes := (SmallEtale.toSchemes B S hS Y.1).obj V
  choose W haW hWaff hWn hWi using fun a =>
    exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart B S hS Y.2 hnormal
      hintegral V.obj.left hV V.obj.hom V.property a
  have hsize : ∀ a, B.Contains (W a).toScheme := fun a =>
    Scheme.size_lt_of_isOpenImmersion (W a).ι T.property
  let Ya : _ → B.Schemes := fun a => B.obj (hsize a)
  let fa : ∀ a, Ya a ⟶ T := fun a =>
    B.inclusion.preimage (show B.inclusion.obj (Ya a) ⟶ B.inclusion.obj T from (W a).ι)
  have hmapfa : ∀ a, B.inclusion.map (fa a) = (W a).ι := fun a => B.inclusion.map_preimage _
  have hetalefa : ∀ a, AlgebraicGeometry.Etale (B.inclusion.map (fa a)) := fun a => by
    rw [hmapfa a]
    infer_instance
  let E := chartFamily B S hS Y.1 Ya fa hetalefa
  refine ⟨E.I₀, E.X, E.f, ?_, fun a => ⟨hWaff a, hWn a, hWi a⟩⟩
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro x
  refine ⟨E.X x, E.f x, Sieve.ofArrows_mk _ _ x, ?_⟩
  change x ∈ Set.range (B.inclusion.map (fa x))
  rw [hmapfa x]
  exact ⟨⟨x, haW x⟩, rfl⟩

/-! ### The reduction to global functions over the charts -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **Invertibility of `𝒪_Y ⟶ f_*𝒪_X` from bijectivity of pullback of functions over the
charts.**  Let `P` be a family of étale charts of `Y` with enough objects.  If, for every chart
`V` with `P`, every ring homomorphism `Γ(V, 𝒪_V) ⟶ Γ(X ×_Y V, 𝒪)` which is pullback of
functions along the projection `X ×_Y V ⟶ V` on every étale scheme chart of `X ×_Y V` is
bijective, then the structure map `𝒪_Y ⟶ f_*𝒪_X` of the morphism of small étale ringed topoi
is invertible.

The structure map on sections over `V`, followed by the injective comparison
`AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions`, is such a homomorphism, so it is
bijective, and the structure map is bijective on sections over `V`; bijectivity over a family
with enough objects is invertibility. -/
theorem isIso_fSharp_of_forall_bijective_globalFunctions (f : X ⟶ Y)
    {P : ObjectProperty (SmallEtale B S hS Y.1)}
    (hP : (SmallEtale.topology B S hS Y.1).HasEnoughObjects P)
    (h : ∀ V, P V → ∀ ψ : Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS Y.1).obj V), ⊤) →+*
          globalFunctions B S hS (chartBaseChangeSpace B S hS f V).obj,
      (∀ c : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj,
        (globalFunctionsChartRestriction B S hS _ c).comp ψ =
          ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS
            (chartBaseChangeProjection B S hS f V).hom c)).appTop.hom) →
      Function.Bijective ψ) :
    IsIso (smallEtaleRingedToposHom B S hS f).fSharp := by
  refine Sheaf.isIso_of_hasEnoughObjects_bijective _ hP fun V hV => ?_
  let σ := ((smallEtaleRingedToposHom B S hS f).fSharp.hom.app (op V)).hom
  let ψ := (directImageSectionsToGlobalFunctions B S hS f V).comp σ
  have hψ : Function.Bijective ψ := h V hV ψ fun c => by
    ext r
    exact directImageSectionsToGlobalFunctions_algebraMap B S hS f V c r
  change Function.Bijective σ
  refine ⟨Function.Injective.of_comp (f := directImageSectionsToGlobalFunctions B S hS f V)
    hψ.injective, fun a => ?_⟩
  obtain ⟨r, hr⟩ := hψ.surjective (directImageSectionsToGlobalFunctions B S hS f V a)
  exact ⟨r, injective_directImageSectionsToGlobalFunctions B S hS f V hr⟩

end AlgebraicGeometry.Space

end
