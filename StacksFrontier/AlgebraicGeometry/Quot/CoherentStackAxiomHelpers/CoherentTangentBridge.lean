module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.ThickeningLift
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFiberedUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFinitePresentationStability
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme

/-!
# Test schemes over a final `Y`, and `Spec k ⊂ Spec k[M]` as a thickening of test schemes

Let `x₀ = (Spec k, 𝒢₀)` be an object of `Coh_{X/Y}` over a field, with `Y` final. The proof of
Stacks 08W8 reads lifts of `x₀` to the trivial square-zero extensions `k[M]` (Stacks 07Y9) as
lifts of `𝒢₀` across the first order thickening `X_k ⊂ X_{k[M]}`. This file sets up the test
schemes involved: an object of the site as a test scheme over a final `Y`, the square-zero
immersion `Spec k ⟶ Spec k[M]` and its retraction as morphisms of test schemes, their
compatibility with the maps `Spec k[N] ⟶ Spec k[M]` induced by module maps, and the fact that
`Spec k ⟶ Spec k[M]` is a first order thickening.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.terminalTestScheme`,
  `AlgebraicGeometry.Space.CoherentSituation.terminalTestMap`: objects and morphisms of the site
  as test schemes over a final `Y`.
* `AlgebraicGeometry.Space.CoherentSituation.squareZeroTestScheme`,
  `AlgebraicGeometry.Space.CoherentSituation.squareZeroTestMap`,
  `AlgebraicGeometry.Space.CoherentSituation.squareZeroTestRetraction`: `Spec k ⟶ Spec k[M]` and
  its retraction.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isFirstOrderThickening_squareZeroTestMap`.

These are private helpers of Stacks 08W8; no declaration here carries a tag.

## References

* [Stacks Project, Tag 08W8](https://stacks.math.columbia.edu/tag/08W8)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

namespace ThickeningLift

variable {ξ : CoherentObject D}

/-- The lift of `ξ` across `n.base` given by a morphism `n : ξ ⟶ A` of `Coh_{X/Y}`. -/
abbrev ofCoherentHom (A : CoherentObject D) (n : CoherentHom ξ A) : D.ThickeningLift ξ n.base where
  F := A.F
  quasicoherent := A.quasicoherent
  finitePresentation := A.finitePresentation
  flat := A.flat
  properSupport := A.properSupport
  fibre := n.fibre
  isIso_fibre := n.isIso_fibre

end ThickeningLift

section SquareZero

variable (D) (hY : IsTerminal D.Y)

include hY in
/-- Over a final `Y`, a test scheme is determined by its underlying object of the site. -/
theorem schemesOver_ext_of_isTerminal {T T' : SchemesOver D.Y} (h : T.left = T'.left) :
    T = T' := by
  obtain ⟨Tl, Tr, Th⟩ := T
  obtain ⟨Tl', Tr', Th'⟩ := T'
  change Tl = Tl' at h
  subst h
  obtain rfl : Tr = Tr' := Subsingleton.elim _ _
  obtain rfl : Th = Th' := hY.hom_ext _ _
  rfl

/-- An object `U` of the site, as a test scheme over a final `Y`. -/
def terminalTestScheme (U : BigFppfOver B S hS) : SchemesOver D.Y :=
  CostructuredArrow.mk (hY.from ((schemeSpaceFunctor B S hS).obj U))

/-- A morphism `T ⟶ U` of the site out of the test scheme of an object `x` of `Coh_{X/Y}`, as a
morphism of test schemes over a final `Y`. -/
def terminalTestMap (x : CoherentObject D) {U : BigFppfOver B S hS}
    (b : (coherentCFG D).val.p.obj x ⟶ U) : x.T ⟶ D.terminalTestScheme hY U :=
  CostructuredArrow.homMk b (hY.hom_ext _ _)

variable {k : Type u} [Field k] (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))

/-- The test scheme `Spec k[M]` over a final `Y`. -/
def squareZeroTestScheme (M : Deformation.Artin.SiteModule k B) : SchemesOver D.Y :=
  D.terminalTestScheme hY (Deformation.Artin.squareZeroOver k B S hS toS M)

variable (x₀ : CoherentObject D)
  (hx : (coherentCFG D).val.p.obj x₀ = Deformation.Artin.algebraOver k B S hS toS hk)

/-- The square-zero immersion `Spec k ⟶ Spec k[M]` under `x₀`, as a morphism of test schemes. -/
def squareZeroTestMap (M : Deformation.Artin.SiteModule k B) :
    x₀.T ⟶ D.squareZeroTestScheme hY toS M :=
  D.terminalTestMap hY x₀ (eqToHom hx ≫ Deformation.Artin.squareZeroArrow k B S hS toS hk M)

/-- The morphism `Spec k[N] ⟶ Spec k[M]` of test schemes induced by a module map `M ⟶ N`. -/
def squareZeroTestSchemeMap {M N : Deformation.Artin.SiteModule k B} (g : M ⟶ N) :
    D.squareZeroTestScheme hY toS N ⟶ D.squareZeroTestScheme hY toS M :=
  CostructuredArrow.homMk (Deformation.Artin.squareZeroOverMap k B S hS toS g) (hY.hom_ext _ _)

/-- The square-zero immersions are compatible with the maps induced by module maps. -/
theorem squareZeroTestMap_comp_squareZeroTestSchemeMap {M N : Deformation.Artin.SiteModule k B}
    (g : M ⟶ N) :
    D.squareZeroTestMap hY toS hk x₀ hx N ≫ D.squareZeroTestSchemeMap hY toS g =
      D.squareZeroTestMap hY toS hk x₀ hx M := by
  apply CostructuredArrow.hom_ext
  show (eqToHom hx ≫ Deformation.Artin.squareZeroArrow k B S hS toS hk N) ≫
      Deformation.Artin.squareZeroOverMap k B S hS toS g =
    eqToHom hx ≫ Deformation.Artin.squareZeroArrow k B S hS toS hk M
  rw [Category.assoc, Deformation.Artin.squareZeroArrow_naturality]

/-- The retraction `Spec k[M] ⟶ Spec k` of the square-zero immersion, induced by the inclusion
`k → k[M]` of constants, as a morphism of test schemes onto the test scheme of `x₀`. -/
def squareZeroTestRetraction (M : Deformation.Artin.SiteModule k B) :
    D.squareZeroTestScheme hY toS M ⟶ x₀.T :=
  CostructuredArrow.homMk (Deformation.Artin.squareZeroRetraction k B S hS toS hk M ≫
    eqToHom hx.symm) (hY.hom_ext _ _)

/-- The retraction is a retraction of the square-zero immersion `Spec k ⟶ Spec k[M]`. -/
theorem squareZeroTestMap_comp_squareZeroTestRetraction (M : Deformation.Artin.SiteModule k B) :
    D.squareZeroTestMap hY toS hk x₀ hx M ≫ D.squareZeroTestRetraction hY toS hk x₀ hx M =
      𝟙 x₀.T := by
  apply CostructuredArrow.hom_ext
  show (eqToHom hx ≫ Deformation.Artin.squareZeroArrow k B S hS toS hk M) ≫
      Deformation.Artin.squareZeroRetraction k B S hS toS hk M ≫ eqToHom hx.symm = 𝟙 _
  rw [Category.assoc, ← Category.assoc (Deformation.Artin.squareZeroArrow k B S hS toS hk M),
    Deformation.Artin.squareZeroArrow_comp_squareZeroRetraction, Category.id_comp,
    eqToHom_trans, eqToHom_refl]

/-- The retractions are compatible with the maps `Spec k[N] ⟶ Spec k[M]` induced by module
maps `M ⟶ N`. -/
theorem squareZeroTestSchemeMap_comp_squareZeroTestRetraction
    {M N : Deformation.Artin.SiteModule k B} (g : M ⟶ N) :
    D.squareZeroTestSchemeMap hY toS g ≫ D.squareZeroTestRetraction hY toS hk x₀ hx M =
      D.squareZeroTestRetraction hY toS hk x₀ hx N := by
  apply CostructuredArrow.hom_ext
  show Deformation.Artin.squareZeroOverMap k B S hS toS g ≫
      Deformation.Artin.squareZeroRetraction k B S hS toS hk M ≫ eqToHom hx.symm =
    Deformation.Artin.squareZeroRetraction k B S hS toS hk N ≫ eqToHom hx.symm
  rw [← Category.assoc, Deformation.Artin.squareZeroOverMap_comp_squareZeroRetraction]

/-- A transport followed by a first order thickening is a first order thickening. -/
theorem _root_.Stacks.Thickenings.IsFirstOrderThickening.eqToHom_comp {X Y Z : Scheme.{u}}
    (e : X = Y) {f : Y ⟶ Z} (hf : Stacks.Thickenings.IsFirstOrderThickening f) :
    Stacks.Thickenings.IsFirstOrderThickening (eqToHom e ≫ f) := by
  subst e
  simpa using hf

/-- **The square-zero immersion `Spec k ⟶ Spec k[M]` is a first order thickening**: the
projection `k[M] ⟶ k` is surjective with square-zero kernel `M`. -/
theorem isFirstOrderThickening_squareZeroTestMap (M : Deformation.Artin.SiteModule k B) :
    Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (D.squareZeroTestMap hY toS hk x₀ hx M).left) := by
  show Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map
    (eqToHom hx ≫ Deformation.Artin.squareZeroArrow k B S hS toS hk M))
  rw [Functor.map_comp, eqToHom_map]
  refine Stacks.Thickenings.IsFirstOrderThickening.eqToHom_comp _ ?_
  exact Stacks.Smooth.isFirstOrderThickening_specMap
    (Deformation.Artin.squareZeroProjection k M.obj)
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
    (Deformation.Artin.squareZeroProjection_ker_sq k M.obj)

end SquareZero


end AlgebraicGeometry.Space.CoherentSituation

end
