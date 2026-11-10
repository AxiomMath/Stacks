module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.QuasiCoherentAffineAcyclicity
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineAcyclicityFromSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFlatBaseChangeProved
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedFppfFamilyTransport
public import StacksFrontier.CategoryTheory.MorphismProperty.OverFiniteProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexIsoOfComponents
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Localization

/-!
# Higher cohomology of a locally quasi-coherent module over an affine object

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `ℱ` be a sheaf of
`𝒪_𝒳`-modules on `𝒳_{fppf}` which is locally quasi-coherent (**Stacks 06WJ**) and whose
comparison maps `c_φ` of **Stacks 06WC** are isomorphisms along the arrows lying over flat
morphisms locally of finite presentation — hypotheses (a) and (b) of **Stacks 075R**. This file
proves that

`H^p(x, ℱ) = 0` for `p > 0` and every object `x` of `𝒳` lying over an affine scheme.

## The argument

This is Cohomology on Sites, **Stacks 03F9**, on the site `𝒳_{fppf}`, for the class `ℬ` of
objects lying over an affine scheme and the coverings `{x_i → x}` of such an object which lie
over a *standard* fppf covering `{U_i → U}` of the affine scheme `U` below `x` — a finite family
of flat morphisms of finite presentation between affine schemes, jointly surjective.

* Such coverings are cofinal: an fppf covering sieve of `x` moves to an fppf covering sieve of
  `U` (**Stacks 0CN0**), which contains a standard one (**Stacks 03XA**), and the standard one
  lifts back along the localization equivalence `𝒳/x ≃ (Sch/U)` of **Stacks 06W0**.
* Their iterated fibre products `x_{i_0} ×_x … ×_x x_{i_n}` exist and lie over the iterated
  fibre products `U_{i_0} ×_U … ×_U U_{i_n}`, which are affine and flat and locally of finite
  presentation over `U`.
* The Čech complex of `ℱ` on such a covering is the Čech complex of the pullback-sections
  presheaf `𝒢^a` of **Stacks 03DS** of the quasi-coherent `𝒪_U`-module `𝒢` with
  `𝒢^a ≅ ℱ|_{U_{étale}}` on the standard covering `{U_i → U}`: hypothesis (b) identifies the
  sections of `ℱ` over each `x_{i_0} ×_x … ×_x x_{i_n}` with the sections of `𝒢^a` over
  `U_{i_0} ×_U … ×_U U_{i_n}`, compatibly with the restriction maps (the identification
  `AlgebraicGeometry.Stack.overPostSectionsIso` of the proof of **Stacks 076T** and its
  naturality). The higher Čech cohomology of `𝒢^a` on a standard covering vanishes
  (**Stacks 03FJ**, Descent **Stacks 023M**).

This is the vanishing that the source obtains, in the proof of **Stacks 075R**, from
**Stacks 075F**, Descent **Stacks 0756** and Cohomology of Schemes **Stacks 01XB**; the Čech
route above uses the same input, the exactness of the Amitsur complex of a faithfully flat ring
map, without passing through the big site of `U`.

## Main definitions

* `AlgebraicGeometry.Stack.overPostLiftHypercover`: the family of arrows of `𝒳` lifting a family
  of the big fppf site of the scheme below an object.
* `AlgebraicGeometry.Stack.objectsOverAffine` and `AlgebraicGeometry.Stack.standardLiftCoverings`:
  the class `ℬ` and the coverings `Cov` of Stacks 03F9.

## Main results

* `AlgebraicGeometry.Stack.isZero_cechCohomology_overPostLiftHypercover`: the higher Čech
  cohomology of `ℱ` on a covering lying over a standard fppf covering vanishes.
* `AlgebraicGeometry.Stack.isZero_sheafCohomology_of_lqc_flatLfp`: `H^p(x, ℱ) = 0` for `p > 0`
  and `x` lying over an affine scheme, cohomology of the underlying abelian sheaf.

## References

* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 0CN0](https://stacks.math.columbia.edu/tag/0CN0)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe t u v w

namespace CategoryTheory.Over

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {T : C} (L : C ⥤ D)

/-- **A product over a terminal object, read in the base and pushed along a functor.** For a
family `A` of objects over a terminal object `T`, the images under `L` of the projections of
the product of `A` in `C/T` form a limit fan in `D`, provided `L` preserves the product of the
underlying objects. -/
def isLimitFanMapLeftOfIsTerminal {J : Type*} (A : J → Over T) [HasProduct A]
    [PreservesLimit (Discrete.functor A) (Over.forget T ⋙ L)] :
    IsLimit (Fan.mk (L.obj (∏ᶜ A).left) (fun j => L.map (Pi.π A j).left) :
      Fan fun j => L.obj (A j).left) :=
  (isLimitMapConeFanMkEquiv (Over.forget T ⋙ L) A (Pi.π A))
    (isLimitOfPreserves (Over.forget T ⋙ L) (productIsProduct A))

end CategoryTheory.Over

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The size-bounded category of schemes of a big fppf site has finite limits
(**Stacks 022K**); recorded at the spelling `B.Schemes` so that instance search sees it. -/
theorem hasFiniteLimits_schemes : HasFiniteLimits B.Schemes :=
  hasFiniteLimits_siteCategory (τ := .fppf) B

/-- The slices of the size-bounded category of schemes of a big fppf site have finite wide
pullbacks, so the iterated fibre products of a family over an object exist. -/
theorem hasFiniteWidePullbacks_over_schemes (U : B.Schemes) :
    HasFiniteWidePullbacks (Over U) :=
  have := hasFiniteLimits_schemes B
  hasFiniteWidePullbacks_of_hasFiniteLimits _

attribute [local instance] hasFiniteWidePullbacks_over_schemes

-- The index type of the formal coproduct of the iterated fibre products of a family is the type
-- of tuples of indices only after `Stacks.CechSite.cechFormalCoproduct` is unfolded; instance
-- search has to see through it to find the products of the reindexed tuples.
attribute [local implicit_reducible] Stacks.CechSite.cechFormalCoproduct
  Stacks.CechSite.cechFormalCoproductMap

section Lift

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **The family of arrows of `𝒳` lifting a family of the big fppf site of the scheme below an
object.** For an object `y` of `𝒳` lying over the scheme `U` and a family `{V_i → U}` of
objects of the big fppf site of `U`, this is the family `{y_i → y}` of arrows of `𝒳` which the
localization equivalence `𝒳/y ≃ (Sch/U)` of **Stacks 06W0** produces over it. -/
abbrev overPostLiftHypercover (y : 𝒳)
    (G : PreZeroHypercover.{t} (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y)))) :
    PreZeroHypercover.{t} y where
  I₀ := G.I₀
  X i := overPostLiftObj B S hS p hp y (G.X i)
  f i := overPostLiftHom B S hS p hp y (G.X i)

end Lift

section Products

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (y : 𝒳)
  (G : PreZeroHypercover.{t} (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y))))
  [hG : ∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]

/-- The images under the inverse of the localization equivalence of **Stacks 06W0** of the
projections of an iterated fibre product of `G` form a limit fan: the iterated fibre product of
the lifted family. -/
def overPostLiftFanIsLimit (n : ℕ) (i : Fin (n + 1) → G.I₀) :
    IsLimit (Fan.mk ((overPostEquivalence B S hS p hp y).inverse.obj
        (∏ᶜ fun a ↦ Over.mk (G.f (i a))).left)
      (fun a ↦ (overPostEquivalence B S hS p hp y).inverse.map
        (Pi.π (fun a ↦ Over.mk (G.f (i a))) a).left) :
      Fan fun a ↦ Over.mk ((overPostLiftHypercover B S hS p hp y G).f (i a))) :=
  haveI : (Over.forget (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y)))).IsEquivalence :=
    (Over.equivalenceOfIsTerminal
      (Over.mkIdTerminal (X := (p ⋙ Over.forget (B.obj hS)).obj y))).isEquivalence_functor
  haveI : (Over.forget (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y))) ⋙
      (overPostEquivalence B S hS p hp y).inverse).IsEquivalence := inferInstance
  Over.isLimitFanMapLeftOfIsTerminal (overPostEquivalence B S hS p hp y).inverse
    (fun a ↦ Over.mk (G.f (i a)))

include hG in
/-- The iterated fibre products of the lifted family exist. -/
theorem hasProduct_overPostLiftHypercover (n : ℕ) (i : Fin (n + 1) → G.I₀) :
    HasProduct (fun a ↦ Over.mk ((overPostLiftHypercover B S hS p hp y G).f (i a))) :=
  HasLimit.mk ⟨_, overPostLiftFanIsLimit B S hS p hp y G n i⟩

attribute [local instance] hasProduct_overPostLiftHypercover

/-- **The iterated fibre product of the lifted family is the lift of the iterated fibre
product.** -/
def overPostLiftProductIso (n : ℕ) (i : Fin (n + 1) → G.I₀) :
    (overPostEquivalence B S hS p hp y).inverse.obj (∏ᶜ fun a ↦ Over.mk (G.f (i a))).left ≅
      ∏ᶜ fun a ↦ Over.mk ((overPostLiftHypercover B S hS p hp y G).f (i a)) :=
  (overPostLiftFanIsLimit B S hS p hp y G n i).conePointUniqueUpToIso (productIsProduct _)

/-- The identification `AlgebraicGeometry.Stack.overPostLiftProductIso` followed by a
projection is the lift of the corresponding projection of the iterated fibre product. -/
@[reassoc (attr := simp)]
theorem overPostLiftProductIso_hom_π (n : ℕ) (i : Fin (n + 1) → G.I₀) (a : Fin (n + 1)) :
    (overPostLiftProductIso B S hS p hp y G n i).hom ≫
        Pi.π (fun a ↦ Over.mk ((overPostLiftHypercover B S hS p hp y G).f (i a))) a =
      (overPostEquivalence B S hS p hp y).inverse.map
        (Pi.π (fun a ↦ Over.mk (G.f (i a))) a).left :=
  (overPostLiftFanIsLimit B S hS p hp y G n i).conePointUniqueUpToIso_hom_comp
    (productIsProduct _) ⟨a⟩

/-- The identification `AlgebraicGeometry.Stack.overPostLiftProductIso` is compatible with the
reindexing maps between iterated fibre products, which are the face maps of the Čech
complexes. -/
@[reassoc]
theorem overPostLiftProductIso_hom_reindex (n : ℕ) (d : Fin (n + 1) → Fin (n + 2))
    (i : Fin (n + 2) → G.I₀) :
    (overPostLiftProductIso B S hS p hp y G (n + 1) i).hom ≫
        (Stacks.CechSite.cechFormalCoproductMap (overPostLiftHypercover B S hS p hp y G) d).φ i =
      (overPostEquivalence B S hS p hp y).inverse.map
          ((Stacks.CechSite.cechFormalCoproductMap G d).φ i).left ≫
        (overPostLiftProductIso B S hS p hp y G n (i ∘ d)).hom := by
  refine Pi.hom_ext _ _ fun b ↦ ?_
  have h1 := Stacks.CechSite.cechFormalCoproductMap_φ_comp_π
    (overPostLiftHypercover B S hS p hp y G) d i b
  have h2 := Stacks.CechSite.cechFormalCoproductMap_φ_comp_π G d i b
  have h3 := overPostLiftProductIso_hom_π B S hS p hp y G (n + 1) i (d b)
  have h4 := overPostLiftProductIso_hom_π B S hS p hp y G n (i ∘ d) b
  simp only [Category.assoc]
  refine (congrArg (fun z ↦ (overPostLiftProductIso B S hS p hp y G (n + 1) i).hom ≫ z) h1).trans
    (h3.trans ?_)
  refine Eq.trans ?_ (congrArg (fun z ↦ (overPostEquivalence B S hS p hp y).inverse.map
    ((Stacks.CechSite.cechFormalCoproductMap G d).φ i).left ≫ z) h4).symm
  rw [← Functor.map_comp, ← Over.comp_left]
  exact congrArg (fun z ↦ (overPostEquivalence B S hS p hp y).inverse.map (Over.Hom.left z)) h2.symm

end Products

section Cech

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

attribute [local instance] hasProduct_overPostLiftHypercover

/-- The base change of a flat morphism locally of finite presentation in a size-bounded
category of schemes is again flat and locally of finite presentation: the inclusion into all
schemes preserves fibre products. -/
theorem flatLfp_of_isPullback_inclusion {X Y Z W : B.Schemes} (f : X ⟶ Y) (g : X ⟶ Z)
    (k₁ : Y ⟶ W) (k : Z ⟶ W) (hpb : IsPullback f g k₁ k)
    (hk : Flat (B.inclusion.map k) ∧ LocallyOfFinitePresentation (B.inclusion.map k)) :
    Flat (B.inclusion.map f) ∧ LocallyOfFinitePresentation (B.inclusion.map f) := by
  have hpb' := hpb.map B.inclusion
  exact ⟨MorphismProperty.of_isPullback hpb'.flip hk.1,
    MorphismProperty.of_isPullback hpb'.flip hk.2⟩

/-- **The iterated fibre products of a standard fppf covering lie flatly and locally of finite
presentation over the base.** -/
theorem flatLfp_piObj_left_hom {U : B.Schemes}
    (G : PreZeroHypercover.{u} (Over.mk (𝟙 U)))
    (hG : ∀ j, Flat (B.inclusion.map (G.f j).left) ∧
      LocallyOfFinitePresentation (B.inclusion.map (G.f j).left))
    (n : ℕ) (i : Fin (n + 1) → G.I₀) [HasProduct fun a ↦ Over.mk (G.f (i a))] :
    Flat (B.inclusion.map (∏ᶜ fun a ↦ Over.mk (G.f (i a))).left.hom) ∧
      LocallyOfFinitePresentation
        (B.inclusion.map (∏ᶜ fun a ↦ Over.mk (G.f (i a))).left.hom) := by
  have : HasFiniteLimits B.Schemes := hasFiniteLimits_siteCategory (τ := .fppf) B
  have key := Over.prop_hom_piObj_fin
    (fun {X Y : Over U} (f : X ⟶ Y) =>
      Flat (B.inclusion.map f.left) ∧ LocallyOfFinitePresentation (B.inclusion.map f.left))
    (fun f g k₁ k hpb hk =>
      flatLfp_of_isPullback_inclusion B f.left g.left k₁.left k.left
        (hpb.map (Over.forget U)) hk)
    (fun f g hf hg => by
      simp only [Over.comp_left, Functor.map_comp]
      exact ⟨MorphismProperty.comp_mem _ _ _ hf.1 hg.1,
        MorphismProperty.comp_mem _ _ _ hf.2 hg.2⟩)
    (fun e f hf => by
      simp only [Over.comp_left, Functor.map_comp]
      have : IsIso (B.inclusion.map e.hom.left) :=
        ((Over.forget U ⋙ B.inclusion).mapIso e).isIso_hom
      have := hf.1
      have := hf.2
      exact ⟨inferInstance, inferInstance⟩)
    n (fun a ↦ Over.mk (G.f (i a))) (fun a ↦ hG (i a))
  have hw : (∏ᶜ fun a ↦ Over.mk (G.f (i a))).hom.left =
      (∏ᶜ fun a ↦ Over.mk (G.f (i a))).left.hom := by
    simpa using Over.w (∏ᶜ fun a ↦ Over.mk (G.f (i a))).hom
  rw [← hw]
  exact key

end Cech


section Downstairs

/-- **Stacks 03FJ on the big fppf site of a scheme.** The higher Čech cohomology of the
pullback-sections presheaf `𝒢^a` of **Stacks 03DS** of a quasi-coherent module on a standard
fppf covering vanishes. -/
theorem isZero_cechCohomology_sectionsPresheaf (B₀ : BigSite.{u} .fppf) (V : Scheme.{u})
    (hV : V.size < cutoff .fppf B₀) (𝓕 : V.Modules) [𝓕.IsQuasicoherent]
    (G : PreZeroHypercover.{u} (Over.mk (𝟙 (base B₀ V hV))))
    (hG : IsOverStandardCovering .fppf B₀ V hV G) (n : ℕ) (hn : 0 < n) :
    IsZero (Stacks.CechSite.cechCohomology G
      ((overToSlice .fppf B₀ V hV).op ⋙ quasiCoherentPresheafFunctor V 𝓕) n) := by
  obtain ⟨hU, hstd⟩ := hG
  have : IsAffine ((overToSlice .fppf B₀ V hV).obj (Over.mk (𝟙 (base B₀ V hV)))).left := hU
  have hmem := IsOverStandardCovering.sieve₀_mem_overTopology .fppf B₀ V hV G ⟨hU, hstd⟩
  let := overStandardCoverings_hasImageProducts .fppf B₀ V hV ⟨G, hmem⟩ ⟨hU, hstd⟩
  exact Stacks.CechSite.cechCohomology_isZero_of_isZero_of_functor
    (overToSlice .fppf B₀ V hV) G (quasiCoherentPresheafFunctor V 𝓕)
    (overStandardCoverings_comparison .fppf B₀ V hV ⟨G, hmem⟩ ⟨hU, hstd⟩) n
    (isZero_cechCohomology_succ_quasiCoherentPresheaf _ .fppf 𝓕 _ hstd n hn)

end Downstairs

section CechVanishing

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
  (hbc : HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) F)
  {y : 𝒳} (d : QuasicoherentBelow B E h S hS p hp F y)
  (G : PreZeroHypercover.{u} (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y))))
  (hG : ∀ j, Flat (B.inclusion.map (G.f j).left) ∧
    LocallyOfFinitePresentation (B.inclusion.map (G.f j).left))

attribute [local instance] hasProduct_overPostLiftHypercover

include hbc hG in
/-- The comparison map `c_φ` is invertible along the arrow of `𝒳` lifting an iterated fibre
product of a family of flat morphisms locally of finite presentation. -/
theorem isIso_restrictModulePullbackComparison_piObj (n : ℕ) (i : Fin (n + 1) → G.I₀) :
    IsIso (restrictModulePullbackComparison B E h S hS p hp
      (overPostLiftHom B S hS p hp y (∏ᶜ fun a ↦ Over.mk (G.f (i a))).left)
      (etaleTopology B) (etaleTopology_le_topology B) F) :=
  isIso_restrictModulePullbackComparison_overPostLift B E h S hS p hp F hbc y _
    (flatLfp_piObj_left_hom B G hG n i).1 (flatLfp_piObj_left_hom B G hG n i).2

/-- **The sections of `ℱ` over an iterated fibre product of the lifted family are the sections of
`𝒢^a` over the iterated fibre product of the family.** -/
def liftedPiSectionsIso (n : ℕ) (i : Fin (n + 1) → G.I₀) :
    F.presheaf.obj (op (∏ᶜ fun a ↦
        Over.mk ((overPostLiftHypercover B S hS p hp y G).f (i a))).left) ≅
      (overPostSectionsPresheaf B S hS p y d.val d.isQuasicoherent).obj
        (op (∏ᶜ fun a ↦ Over.mk (G.f (i a))).left) :=
  F.presheaf.mapIso ((Over.forget y).mapIso (overPostLiftProductIso B S hS p hp y G n i)).op ≪≫
    overPostSectionsIso B E h S hS p hp F hlqc y _ d.val d.isQuasicoherent d.isSheaf d.iso
      (isIso_restrictModulePullbackComparison_piObj B E h S hS p hp F hbc G hG n i)

/-- The forward map of `AlgebraicGeometry.Stack.liftedPiSectionsIso` is restriction along
`AlgebraicGeometry.Stack.overPostLiftProductIso` followed by the identification
`AlgebraicGeometry.Stack.overPostSectionsIso`. -/
theorem liftedPiSectionsIso_hom (n : ℕ) (i : Fin (n + 1) → G.I₀) :
    (liftedPiSectionsIso B E h S hS p hp F hlqc hbc d G hG n i).hom =
      F.presheaf.map ((Over.forget y).map (overPostLiftProductIso B S hS p hp y G n i).hom).op ≫
        (overPostSectionsIso B E h S hS p hp F hlqc y _ d.val d.isQuasicoherent d.isSheaf d.iso
          (isIso_restrictModulePullbackComparison_piObj B E h S hS p hp F hbc G hG n i)).hom := by
  simp only [liftedPiSectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom]

/-- The identifications `AlgebraicGeometry.Stack.liftedPiSectionsIso` commute with the
restriction maps along the reindexing maps between iterated fibre products. This is the
naturality of the identification of the proof of **Stacks 076T**, which is the cocycle condition
`AlgebraicGeometry.Stack.LiftedSectionsCocycle`. -/
theorem liftedPiSectionsIso_reindex (n : ℕ) (e : Fin (n + 1) → Fin (n + 2))
    (i : Fin (n + 2) → G.I₀) :
    F.presheaf.map ((Stacks.CechSite.cechFormalCoproductMap
        (overPostLiftHypercover B S hS p hp y G) e).φ i).left.op ≫
        (liftedPiSectionsIso B E h S hS p hp F hlqc hbc d G hG (n + 1) i).hom =
      (liftedPiSectionsIso B E h S hS p hp F hlqc hbc d G hG n (i ∘ e)).hom ≫
        (overPostSectionsPresheaf B S hS p y d.val d.isQuasicoherent).map
          ((Stacks.CechSite.cechFormalCoproductMap G e).φ i).left.op := by
  have hcoc : LiftedSectionsCocycle B E h S hS p hp :=
    liftedSectionsCocycle_of_factorFourSquare B E h S hS p hp
      (liftedSectionsFactorFourSquare_of_compat B E h S hS p hp
        (associatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp))
  obtain ⟨r, hr⟩ : ∃ r : (∏ᶜ fun a ↦ Over.mk (G.f (i a))).left ⟶
      (∏ᶜ fun a ↦ Over.mk (G.f ((i ∘ e) a))).left,
      ((Stacks.CechSite.cechFormalCoproductMap G e).φ i).left = r := ⟨_, rfl⟩
  have hnat := overPostSectionsIso_naturality B E h S hS p hp F hlqc hcoc y r
    d.val d.isQuasicoherent d.isSheaf d.iso
    (isIso_restrictModulePullbackComparison_piObj B E h S hS p hp F hbc G hG n (i ∘ e))
    (isIso_restrictModulePullbackComparison_piObj B E h S hS p hp F hbc G hG (n + 1) i)
  have hre := congrArg Over.Hom.left
    (overPostLiftProductIso_hom_reindex B S hS p hp y G n e i)
  simp only [Over.comp_left] at hre
  rw [liftedPiSectionsIso_hom, liftedPiSectionsIso_hom]
  simp only [Over.forget_map]
  rw [← Category.assoc, ← F.presheaf.map_comp, ← op_comp, hre, op_comp, F.presheaf.map_comp,
    Category.assoc]
  rw [Category.assoc]
  refine congrArg (fun z ↦ F.presheaf.map
    (overPostLiftProductIso B S hS p hp y G n (i ∘ e)).hom.left.op ≫ z) ?_
  subst hr
  convert hnat using 3


include hlqc hbc hG in
/-- The Čech-complex comparison at a chosen quasi-coherent module below `y`: the Čech cohomology
of `ℱ` on the lifted family is the Čech cohomology of `𝒢^a` on the family. -/
theorem isZero_cechCohomology_overPostLiftHypercover_of_isZero (n : ℕ)
    (hQ : IsZero (Stacks.CechSite.cechCohomology G
      (overPostSectionsPresheaf B S hS p y d.val d.isQuasicoherent) n)) :
    IsZero (Stacks.CechSite.cechCohomology (overPostLiftHypercover B S hS p hp y G)
      F.presheaf n) :=
  Stacks.CechSite.cechCohomology_isZero_of_components
    (fun j ↦ overPostLiftObj B S hS p hp y (G.X j)) (fun j ↦ overPostLiftHom B S hS p hp y (G.X j))
    G.X G.f F.presheaf (overPostSectionsPresheaf B S hS p y d.val d.isQuasicoherent)
    (liftedPiSectionsIso B E h S hS p hp F hlqc hbc d G hG)
    (liftedPiSectionsIso_reindex B E h S hS p hp F hlqc hbc d G hG) n hQ

end CechVanishing

section CechVanishingFinal

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
  (hbc : HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) F)

attribute [local instance] hasProduct_overPostLiftHypercover

include hlqc hbc in
/-- **The higher Čech cohomology of `ℱ` on a covering lying over a standard fppf covering
vanishes.** Let `y` be an object of `𝒳` lying over the affine scheme `U`, and let
`{U_i → U}` be a standard fppf covering of `U`. The Čech complex of `ℱ` on the lifted family
`{y_i → y}` is the Čech complex on `{U_i → U}` of the pullback-sections presheaf `𝒢^a` of the
quasi-coherent module `𝒢` below `y` (`AlgebraicGeometry.Stack.liftedPiSectionsIso`), and the
latter has no higher cohomology (**Stacks 03FJ**). -/
theorem isZero_cechCohomology_overPostLiftHypercover (y : 𝒳)
    (G : PreZeroHypercover.{u} (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y))))
    (hG : IsOverStandardCovering .fppf B ((p ⋙ Over.forget (B.obj hS)).obj y).1
      ((p ⋙ Over.forget (B.obj hS)).obj y).2 G)
    (n : ℕ) (hn : 0 < n) :
    IsZero (Stacks.CechSite.cechCohomology (overPostLiftHypercover B S hS p hp y G)
      F.presheaf n) := by
  obtain ⟨d⟩ := nonempty_quasicoherentBelow B E h S hS p hp F hlqc y
  have hflat : ∀ j, Flat (B.inclusion.map (G.f j).left) ∧
      LocallyOfFinitePresentation (B.inclusion.map (G.f j).left) := by
    obtain ⟨hU, hstd⟩ := hG
    exact fun j ↦ ⟨(hstd.standard j).1, (hstd.standard j).2.1⟩
  have hQ := @isZero_cechCohomology_sectionsPresheaf B _ _ d.val d.isQuasicoherent G hG n hn
  exact isZero_cechCohomology_overPostLiftHypercover_of_isZero B E h S hS p hp F hlqc hbc d G
    hflat n hQ

end CechVanishingFinal


section Coverings

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

include hp in
/-- The inherited fppf topology of `𝒳` is inherited from the fppf topology of the big site in
the sense of `CategoryTheory.Functor.IsInheritedTopology`. -/
theorem isInheritedTopology_fppf :
    Functor.IsInheritedTopology.{t} p (B.topology.over (B.obj hS))
      (BigFppfOver.associatedTopology B S hS p .fppf) :=
  have : p.IsFibered := hp.isFibered
  have := hasFiniteLimits_schemes B
  Functor.isInheritedTopology_inheritedTopology p (B.topology.over (B.obj hS))

/-- **The lift of a covering family of the big fppf site of the scheme below an object is a
covering family of `𝒳`.** -/
theorem overPostLiftHypercover_sieve₀_mem (y : 𝒳)
    (G : PreZeroHypercover.{u} (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y))))
    (hG : G.sieve₀ ∈ overTopology .fppf B ((p ⋙ Over.forget (B.obj hS)).obj y).1
      ((p ⋙ Over.forget (B.obj hS)).obj y).2 (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y)))) :
    (overPostLiftHypercover B S hS p hp y G).sieve₀ ∈
      BigFppfOver.associatedTopology B S hS p .fppf y := by
  have hJ : Functor.IsInheritedTopology.{u} p (B.topology.over (B.obj hS))
      (BigFppfOver.associatedTopology B S hS p .fppf) := isInheritedTopology_fppf B S hS p hp
  rw [PreZeroHypercover.sieve₀, hJ _ _ fun i ↦ hp.isStronglyCartesian _,
    GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  have hG' : G.sieve₀ ∈ (B.topology.over ((p ⋙ Over.forget (B.obj hS)).obj y))
      (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y))) := hG
  rw [GrothendieckTopology.mem_over_iff, PreZeroHypercover.sieve₀, Sieve.overEquiv_ofArrows] at hG'
  refine B.topology.superset_covering ?_ hG'
  intro W g hg
  rw [Sieve.mem_ofArrows_iff] at hg ⊢
  obtain ⟨i, a, rfl⟩ := hg
  refine ⟨i, a ≫ (overPostLiftIso B S hS p hp y (G.X i)).inv.left, ?_⟩
  have h1 : (G.f i).left = (G.X i).hom := by simpa using Over.w (G.f i)
  have h2 := Over.w (overPostLiftIso B S hS p hp y (G.X i)).inv
  change (overPostLiftIso B S hS p hp y (G.X i)).inv.left ≫
    (p.map (overPostLiftHom B S hS p hp y (G.X i))).left = (G.X i).hom at h2
  change a ≫ (G.f i).left = (a ≫ (overPostLiftIso B S hS p hp y (G.X i)).inv.left) ≫
    (p.map (overPostLiftHom B S hS p hp y (G.X i))).left
  rw [Category.assoc, h2, h1]

/-- **Lifted standard coverings are cofinal.** Every fppf covering sieve of an object of `𝒳`
lying over an affine scheme `U` contains the lift of a standard fppf covering of `U`. -/
theorem exists_overPostLiftHypercover_le (y : 𝒳) (hy : IsAffineOver B S hS (p.obj y))
    (R : Sieve y) (hR : R ∈ BigFppfOver.associatedTopology B S hS p .fppf y) :
    ∃ G : PreZeroHypercover.{u} (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y))),
      IsOverStandardCovering .fppf B ((p ⋙ Over.forget (B.obj hS)).obj y).1
        ((p ⋙ Over.forget (B.obj hS)).obj y).2 G ∧
      (overPostLiftHypercover B S hS p hp y G).sieve₀ ≤ R := by
  have hJ : Functor.IsInheritedTopology.{max v w} p (B.topology.over (B.obj hS))
      (BigFppfOver.associatedTopology B S hS p .fppf) := isInheritedTopology_fppf B S hS p hp
  rw [Functor.IsInheritedTopology.mem_iff_functorPushforward hp hJ,
    GrothendieckTopology.mem_over_iff] at hR
  let T := Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y))
  have hR₀ : (Sieve.overEquiv T).symm
      (Sieve.overEquiv (p.obj y) (R.functorPushforward p)) ∈
        overTopology .fppf B ((p ⋙ Over.forget (B.obj hS)).obj y).1
          ((p ⋙ Over.forget (B.obj hS)).obj y).2 T := by
    change _ ∈ (B.topology.over ((p ⋙ Over.forget (B.obj hS)).obj y)) T
    rw [GrothendieckTopology.mem_over_iff, (Sieve.overEquiv T).apply_symm_apply]
    exact hR
  obtain ⟨G', hGstd, hGle'⟩ := overStandardCoverings_cofinal .fppf B _ _ T hy _ hR₀
  let G : PreZeroHypercover.{u} (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj y))) := G'.1
  have hGle : G.sieve₀ ≤ (Sieve.overEquiv T).symm
      (Sieve.overEquiv (p.obj y) (R.functorPushforward p)) := hGle'
  refine ⟨G, hGstd, ?_⟩
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  have hi : (Sieve.overEquiv (p.obj y) (R.functorPushforward p))
      ((G.f i).left : (G.X i).left ⟶ (p.obj y).left) :=
    hGle _ (Sieve.ofArrows_mk _ _ i)
  rw [Sieve.overEquiv_iff] at hi
  obtain ⟨z, φ, k, hφ, hk⟩ := hi
  have hkl := congrArg CommaMorphism.left hk
  simp only [Over.homMk_left, Over.comp_left] at hkl
  have h1 : (G.f i).left = (G.X i).hom := by simpa using Over.w (G.f i)
  let Φ := overPostEquivalence B S hS p hp y
  let m₀ : G.X i ⟶ Φ.functor.obj (Over.mk φ) :=
    Over.homMk k.left (by
      change k.left ≫ (p.map φ).left = (G.X i).hom
      exact hkl.symm.trans h1)
  let m : Φ.inverse.obj (G.X i) ⟶ Over.mk φ :=
    Φ.fullyFaithfulFunctor.preimage ((overPostLiftIso B S hS p hp y (G.X i)).hom ≫ m₀)
  have hm : m.left ≫ φ = overPostLiftHom B S hS p hp y (G.X i) := Over.w m
  change R.arrows (overPostLiftHom B S hS p hp y (G.X i))
  rw [← hm]
  exact R.downward_closed hφ m.left

end Coverings

section Cartan

variable {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- The objects of `𝒳` lying over an affine scheme: the class `ℬ` of the Čech-vanishing criterion
of **Stacks 03F9**. -/
def objectsOverAffine : Set 𝒳 := {x | IsAffineOver B S hS (p.obj x)}

/-- The coverings of an object of `𝒳` lying over a standard fppf covering of the scheme below it:
the collection `Cov` of the Čech-vanishing criterion of **Stacks 03F9**. -/
def standardLiftCoverings (x : 𝒳) :
    Set { E : PreZeroHypercover.{u} x //
      E.sieve₀ ∈ BigFppfOver.associatedTopology B S hS p .fppf x } :=
  {E | ∃ G : PreZeroHypercover.{u} (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))),
    IsOverStandardCovering .fppf B ((p ⋙ Over.forget (B.obj hS)).obj x).1
      ((p ⋙ Over.forget (B.obj hS)).obj x).2 G ∧
      E.1 = overPostLiftHypercover B S hS p hp x G}

/-- Lying over an affine scheme is invariant under isomorphism. -/
theorem isAffineOver_of_iso {z z' : 𝒳} (e : z ≅ z') (h : IsAffineOver B S hS (p.obj z)) :
    IsAffineOver B S hS (p.obj z') :=
  have := h
  IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).map (p.map e.inv))

/-- The lift of an object of the big fppf site of the scheme below `x` lies over an affine scheme
as soon as that object is affine. -/
theorem isAffineOver_overPostLiftObj (x : 𝒳) (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hV : IsAffine (B.inclusion.obj V.left)) :
    IsAffineOver B S hS (p.obj (overPostLiftObj B S hS p hp x V)) :=
  have := hV
  have : IsIso (B.inclusion.map (overPostLiftIso B S hS p hp x V).hom.left) :=
    ((Over.forget _ ⋙ B.inclusion).mapIso (overPostLiftIso B S hS p hp x V)).isIso_hom
  IsAffine.of_isIso (B.inclusion.map (overPostLiftIso B S hS p hp x V).hom.left)

end Cartan

section CartanVanishing

variable {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

attribute [local instance] hasProduct_overPostLiftHypercover

/-- **The higher cohomology of a locally quasi-coherent module with flat base change vanishes over
the objects lying over an affine scheme.** Let `F` be a presheaf of `𝒪_𝒳`-modules which is
locally quasi-coherent (**Stacks 06WJ**) and whose comparison maps `c_φ` of **Stacks 06WC** are
isomorphisms along the arrows lying over flat morphisms locally of finite presentation, and which
is a sheaf for the fppf topology. Then for every object `x` of `𝒳` lying over an affine scheme
and every `n > 0`,

`H^n(x, F) = 0`,

cohomology of the underlying abelian sheaf on `𝒳_{fppf}`.

This is the Čech-vanishing criterion of **Stacks 03F9** on `𝒳_{fppf}`, for the objects lying
over an affine scheme and the coverings lying over a standard fppf covering, whose Čech
cohomology vanishes by
`AlgebraicGeometry.Stack.isZero_cechCohomology_overPostLiftHypercover`. The homological inputs
of the criterion — sheafification, enough injectives and `Ext`-groups — are its instance
arguments. -/
theorem isZero_sheafCohomology_of_isLocallyQuasicoherent
    [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
    [HasExt.{t} (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
    [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hbc : HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F)
    (hF : Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p .fppf) F.presheaf)
    (x : 𝒳) (hx : IsAffineOver B S hS (p.obj x)) (n : ℕ) (hn : 0 < n) :
    IsZero (Sheaf.H'.{t} (⟨F.presheaf, hF⟩ :
      Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}) n x) := by
  refine Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives
    (BigFppfOver.associatedTopology B S hS p .fppf) (objectsOverAffine B S hS p)
    (standardLiftCoverings B S hS p hp) ?_ ?_ ?_ ⟨F.presheaf, hF⟩ ?_ x hx n hn
  · rintro y ⟨𝓔, h𝓔'⟩ ⟨G, -, rfl : 𝓔 = _⟩ m i
    exact hasProduct_overPostLiftHypercover B S hS p hp y G m i
  · rintro y ⟨𝓔, h𝓔'⟩ ⟨G, ⟨hU, hstd⟩, rfl : 𝓔 = _⟩
    refine ⟨hU, fun i ↦ isAffineOver_overPostLiftObj B S hS p hp y (G.X i)
      (hstd.affine_source i), fun m i ↦ ?_⟩
    exact isAffineOver_of_iso B S hS p
      ((Over.forget y).mapIso (overPostLiftProductIso B S hS p hp y G m i))
      (isAffineOver_overPostLiftObj B S hS p hp y _
        (isAffine_overScheme_piObj .fppf B _ _ hU G hstd.affine_source m i))
  · intro y hy R hR
    obtain ⟨G, hG, hle⟩ := exists_overPostLiftHypercover_le B S hS p hp y hy R hR
    exact ⟨⟨_, overPostLiftHypercover_sieve₀_mem B S hS p hp y G
      (IsOverStandardCovering.sieve₀_mem_overTopology .fppf B _ _ G hG)⟩, ⟨G, hG, rfl⟩, hle⟩
  · rintro y ⟨𝓔, h𝓔'⟩ ⟨G, hG, rfl : 𝓔 = _⟩ m hm
    exact isZero_cechCohomology_overPostLiftHypercover B E h S hS p hp F hlqc hbc y G hG m hm

end CartanVanishing

end AlgebraicGeometry.Stack

end
