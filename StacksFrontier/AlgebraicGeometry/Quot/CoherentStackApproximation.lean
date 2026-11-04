module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackArtinAxioms
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteChangeTowerFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpaceTruncations
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationFullyFaithful
public import StacksFrontier.Deformation.Artin.FormalObject.Realization
public import StacksFrontier.Deformation.Artin.FormalObject.BaseContains
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitDescentHom
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcDescentUnconditional

/-!
# The functor of Equation 07X6 at `Coh_{X/Y}` is an equivalence

In Situation 08KB, with `f : X ⟶ Y` separated, the functor of Artin's Axioms, Equation 07X6, at
`Coh_{X/Y}` is an equivalence.

Over a complete local base `Spec A ⟶ Y`, objects of `Coh_{X/Y}` are coherent modules on `X_A`
flat over `A` with support proper over `A`, and formal objects are compatible systems of such
modules on the base changes `X_n` of `X` to the thickenings `Spec(A/𝔪^{n+1})`. These base changes
form a `AlgebraicGeometry.Space.SiteChangeTower`
(`AlgebraicGeometry.Space.CoherentSituation.levelTower`).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isEffective_formalObject`: every formal object of
  `Coh_{X/Y}` is effective.
* `AlgebraicGeometry.Space.CoherentSituation.hasUniqueExtensions_approximationFunctor`: the
  functor of Equation 07X6 at `Coh_{X/Y}` has unique extensions.
* `AlgebraicGeometry.Space.CoherentSituation.isEquivalence_approximationFunctor`: the functor of
  Equation 07X6 at `Coh_{X/Y}` is an equivalence.

## References

* [Stacks Project, Tag 08W9](https://stacks.math.columbia.edu/tag/08W9)
* [Stacks Project, Tag 08BE](https://stacks.math.columbia.edu/tag/08BE)
* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
* [Stacks Project, Tag 08VP](https://stacks.math.columbia.edu/tag/08VP)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [-instance] CategoryTheory.catToReflQuiver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The image of an `eqToHom` under `schemeSpaceFunctor` is an isomorphism of presheaves. -/
theorem isIso_schemeSpaceFunctor_map_eqToHom_hom {U V : BigFppfOver B S hS} (e : U = V) :
    IsIso ((schemeSpaceFunctor B S hS).map (eqToHom e)).hom := by
  subst e
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact inferInstanceAs (IsIso (𝟙 _))

/-- The image of an `eqToHom` under `schemeSpaceFunctor` is an isomorphism. -/
theorem isIso_schemeSpaceFunctor_map_eqToHom {U V : BigFppfOver B S hS} (e : U = V) :
    IsIso ((schemeSpaceFunctor B S hS).map (eqToHom e)) := by
  subst e
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  infer_instance

/-- Flatness over a target composed with an isomorphism is flatness over the target. -/
theorem isFlatOver_of_isFlatOver_comp_isIso {X Y Y' : AlgebraicSpaces B S hS} (q : X ⟶ Y)
    (ρ : Y ⟶ Y') [IsIso ρ] (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (h : IsFlatOver B S hS X.2 (q ≫ ρ).hom F) : IsFlatOver B S hS X.2 q.hom F := by
  have : IsIso (inv ρ).hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map (inv ρ)))
  have h1 := isFlatOver_comp_of_isFlat B S hS (q ≫ ρ) (inv ρ) F h (isFlat_of_isIso _ Y.2)
  rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h1

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-! ### The tower of thickenings of a complete local base -/

section Tower

variable (A : Deformation.Artin.FormalBase S) (hA : B.Contains (Spec (.of A.R)))
  {T : SchemesOver D.Y} (hT : T.left = Deformation.Artin.baseOver B S hS A hA)

/-- The projection `X_T ⟶ Spec A` of the base change to a complete local base. -/
abbrev projectionTo :
    D.space T ⟶ schemeSpace (Over.mk (ObjectProperty.homMk (X := B.obj hA) (Y := B.obj hS)
      A.toS)) :=
  D.projection T ≫ (schemeSpaceFunctor B S hS).map (eqToHom hT)

variable (L : ℕ → SchemesOver D.Y) (a : ∀ n, L n ⟶ T) (t : ∀ n, L n ⟶ L (n + 1))
  (ht : ∀ n, t n ≫ a (n + 1) = a n)
  (e : ∀ n, (BigFppfOver.toScheme B S hS).obj (L n).left ≅
    adicThickening A.R (maximalIdeal A.R) n)
  (he : ∀ n, (BigFppfOver.toScheme B S hS).map ((a n).left ≫ eqToHom hT) =
    (e n).hom ≫ adicThickeningι A.R (maximalIdeal A.R) n)

/-- The base change `X_{L_n} ⟶ X_T` lies in a cartesian square over `L_n ⟶ Spec A`. -/
theorem levelTower_isPullback (n : ℕ) :
    IsPullback (D.relativeMap (a n)) (D.projection (L n)) (D.projectionTo A hA hT)
      (schemeSpaceMap ((a n).left ≫ eqToHom hT)) := by
  have top := isPullback_baseChangeMap D.f (a n)
  have bot : IsPullback ((schemeSpaceFunctor B S hS).map (a n).left) (𝟙 _)
      ((schemeSpaceFunctor B S hS).map (eqToHom hT))
      ((schemeSpaceFunctor B S hS).map ((a n).left ≫ eqToHom hT)) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.id_comp, Functor.map_comp]⟩
  have h := top.paste_vert bot
  rwa [Category.comp_id] at h

include ht in
/-- The base changes `X_{L_n} ⟶ X_{L_{n+1}} ⟶ X_T` compose to `X_{L_n} ⟶ X_T`. -/
theorem levelTower_comp (n : ℕ) :
    D.relativeMap (t n) ≫ D.relativeMap (a (n + 1)) = D.relativeMap (a n) :=
  (baseChangeMap_comp D.f (t n) (a (n + 1))).symm.trans (by rw [ht n])

include ht e he in
/-- The thickenings of a complete local base form a tower over `S`: morphisms of test schemes
`a_n : L_n ⟶ T` over `Y` from the infinitesimal thickenings of a complete local base `T`, with
transitions, give the base changes `X_{L_n} ⟶ X_T`. -/
theorem levelTower : SiteChangeTower (D.space T) (D.projectionTo A hA hT) (maximalIdeal A.R)
    (fun n => D.space (L n)) (fun n => D.relativeMap (a n)) (fun n => D.relativeMap (t n))
    (fun n => (L n).left) (fun n => (a n).left ≫ eqToHom hT) (fun n => D.projection (L n)) where
  comp := D.levelTower_comp L a t ht
  isPullback := D.levelTower_isPullback A hA hT L a
  iso n := ⟨e n, he n⟩

/-- The transition triangles of `levelTower` are the comparisons `modulePullbackTriangle`. -/
theorem levelTower_tri (n : ℕ) : (D.levelTower A hA hT L a t ht e he).tri n =
    modulePullbackTriangle B S hS (D.levelTower_comp L a t ht n) := rfl

include e he in
/-- Grothendieck's existence theorem on the thickenings of a complete local base. -/
theorem levelTower_exists_of_compatible [IsNoetherianRing A.R]
    [IsAdicComplete (maximalIdeal A.R) A.R]
    [Fact (HasEtaleLocalProperty B S hS (D.space T).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hπ : IsFiniteType B S hS (D.projectionTo A hA hT).hom)
    (hsep : IsSeparated B S hS (D.projectionTo A hA hT).hom)
    (F : ∀ n, Modules.{u, u} B S hS (D.space (L n)).1 (D.space (L n)).2)
    (hF : ∀ n, IsCoherent B S hS (D.space (L n)).1 (D.space (L n)).2 (F n))
    (φ : ∀ n, (modulePullback B S hS (D.relativeMap (t n))).obj (F (n + 1)) ≅ F n)
    (hp : IsLocallyOfFiniteType B S hS (D.projection (L 0)).hom)
    (hF₀p : HasProperSupport B S hS (D.space (L 0)).2 (schemeSpace (L 0).left).2
      (D.projection (L 0)).hom hp ((SheafOfModules.toSheaf _).obj (F 0))) :
    ∃ (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) (_ : IsCoherent B S hS _ _ G)
      (_ : HasProperSupport B S hS (D.space T).2 (schemeSpace _).2 (D.projectionTo A hA hT).hom
        hπ.1 ((SheafOfModules.toSheaf _).obj G))
      (ψ : ∀ n, (modulePullback B S hS (D.relativeMap (a n))).obj G ≅ F n),
      ∀ n, (modulePullbackTriangle B S hS (D.levelTower_comp L a t ht n)).hom.app G ≫
        (modulePullback B S hS (D.relativeMap (t n))).map (ψ (n + 1)).hom ≫ (φ n).hom =
          (ψ n).hom := by
  obtain ⟨G, hG, hGp, ψ, hψ⟩ :=
    (D.levelTower A hA hT L a t ht e he).exists_of_compatible F hπ hsep hF φ hp hF₀p
  refine ⟨G, hG, hGp, ψ, fun n => ?_⟩
  rw [← D.levelTower_tri A hA hT L a t ht e he n]
  exact hψ n

end Tower

/-! ### Objects over a complete local base -/

section Objects

variable (A : Deformation.Artin.FormalBase S) (hA : B.Contains (Spec (.of A.R)))

/-- The base change to a locally Noetherian test scheme is locally Noetherian. -/
theorem fact_space (T : SchemesOver D.Y) (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
    (hN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T.left)) :
    Fact (HasEtaleLocalProperty B S hS (D.space T).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
  ⟨isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (D.space T).2
    ((schemeSpaceFunctor B S hS).obj T.left).2 _ hp
    ((exists_atlas_iff_of_representable B S hS _ _ T.left (Iso.refl _)).2 hN)⟩

/-- The spectrum of a complete local base is locally Noetherian. -/
theorem isLocallyNoetherian_baseOver :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      (Deformation.Artin.baseOver B S hS A hA)) := by
  have : IsNoetherianRing A.R := A.noetherian
  exact (AlgebraicGeometry.isLocallyNoetherian_Spec (R := .of A.R)).2 inferInstance

/-- The thickenings `Spec(A/𝔪^{n+1})` of a complete local base are locally Noetherian. -/
theorem isLocallyNoetherian_truncationOver (c : ∀ n, B.Contains (A.truncation n)) (n : ℕ) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      (Deformation.Artin.truncationOver B S hS A c n)) := by
  have : IsNoetherianRing A.R := A.noetherian
  exact (AlgebraicGeometry.isLocallyNoetherian_Spec
    (R := .of (A.R ⧸ maximalIdeal A.R ^ (n + 1)))).2 inferInstance

/-- The projection `X_T ⟶ Spec A` is locally of finite type when `X_T ⟶ T` is. -/
theorem isLocallyOfFiniteType_projectionTo {T : SchemesOver D.Y}
    (hT : T.left = Deformation.Artin.baseOver B S hS A hA)
    (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom) :
    IsLocallyOfFiniteType B S hS (D.projectionTo A hA hT).hom :=
  have := isIso_schemeSpaceFunctor_map_eqToHom_hom hT
  isLocallyOfFiniteType_comp' B S hS _ _ ((schemeSpaceFunctor B S hS).obj T.left).2
    (schemeSpace _).2 hp
    (isLocallyOfFiniteType_of_isClosedImmersion B S hS _
      (isClosedImmersion_of_isIso B S hS ((schemeSpaceFunctor B S hS).map (eqToHom hT)).hom))

/-- The module of an object over a locally Noetherian test scheme is coherent. -/
theorem isCoherent_F (x : CoherentObject D)
    (hN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj x.T.left)) :
    IsCoherent B S hS (D.space x.T).1 (D.space x.T).2 x.F := by
  have := D.fact_space x.T x.properSupport.1 hN
  exact (isCoherent_iff_isFinitePresentationOnSite B S hS _ _ x.F).2 x.finitePresentation

/-- Proper support over `X_T ⟶ Spec A` is the same as proper support over `X_T ⟶ T`. -/
private theorem hasProperSupport_projectionTo_iff (A : Deformation.Artin.FormalBase S)
    (hA : B.Contains (Spec (.of A.R))) {T : SchemesOver D.Y}
    (hT : T.left = Deformation.Artin.baseOver B S hS A hA)
    (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
    (hp' : IsLocallyOfFiniteType B S hS (D.projectionTo A hA hT).hom)
    (F : Sheaf (SmallEtale.topology B S hS (D.space T).1) AddCommGrpCat.{u}) :
    HasProperSupport B S hS (D.space T).2 (schemeSpace _).2 (D.projectionTo A hA hT).hom hp' F ↔
      HasProperSupport B S hS (D.space T).2 ((schemeSpaceFunctor B S hS).obj T.left).2
        (D.projection T).hom hp F :=
  @hasProperSupport_comp_isIso_iff B S hS _ _ _ (D.space T).2
    ((schemeSpaceFunctor B S hS).obj T.left).2 (schemeSpace _).2 (D.projection T).hom
    ((schemeSpaceFunctor B S hS).map (eqToHom hT)).hom
    (isIso_schemeSpaceFunctor_map_eqToHom_hom hT) hp hp' F

/-- The module of an object over a complete local base has support proper over `Spec A`. -/
theorem hasProperSupport_F (x : CoherentObject D)
    (hT : x.T.left = Deformation.Artin.baseOver B S hS A hA)
    (hp : IsLocallyOfFiniteType B S hS (D.projectionTo A hA hT).hom) :
    HasProperSupport B S hS (D.space x.T).2 (schemeSpace _).2 (D.projectionTo A hA hT).hom hp
      ((SheafOfModules.toSheaf _).obj x.F) := by
  obtain ⟨hp', hU, hprop⟩ := x.properSupport
  exact (D.hasProperSupport_projectionTo_iff A hA hT hp' hp _).2 ⟨hU, hprop⟩

/-- The projection of the base change to a complete local base is of finite type. -/
theorem isFiniteType_projectionTo {T : SchemesOver D.Y}
    (hT : T.left = Deformation.Artin.baseOver B S hS A hA) :
    IsFiniteType B S hS (D.projectionTo A hA hT).hom := by
  have h1 := isFiniteType_of_isFinitePresentation B S hS
    (IsFinitePresentation.of_isPullback B S hS (D.space T).2 D.X.2
      ((schemeSpaceFunctor B S hS).obj T.left).2 D.Y.2
      (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeSpace D.f T))
      D.finitePresentation)
  exact (@isFiniteType_comp_isIso_iff B S hS _ _ _ _ _
    (isIso_schemeSpaceFunctor_map_eqToHom_hom hT)).2 h1

/-- The projection of the base change is separated when `f` is. -/
theorem isSeparated_projectionTo {T : SchemesOver D.Y}
    (hT : T.left = Deformation.Artin.baseOver B S hS A hA) (hsep : IsSeparated B S hS D.f.hom) :
    IsSeparated B S hS (D.projectionTo A hA hT).hom := by
  have h1 := isSeparated_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeSpace D.f T)) hsep
  exact (@isSeparated_comp_isIso_iff B S hS _ _ _ _ _
    (isIso_schemeSpaceFunctor_map_eqToHom_hom hT)).2 h1

end Objects

/-! ### Morphisms from a complete local base to `Y` -/

/-- The inclusions of the thickenings into the complete local base are compatible with the
transitions. -/
theorem truncationOverSucc_restrictionToBase (A : Deformation.Artin.FormalBase S)
    (hA : B.Contains (Spec (.of A.R))) (c : ∀ n, B.Contains (A.truncation n)) (n : ℕ) :
    Deformation.Artin.truncationOverSucc B S hS A c n ≫
        Deformation.Artin.restrictionToBase B S hS A hA c (n + 1) =
      Deformation.Artin.restrictionToBase B S hS A hA c n :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (adicThickeningSucc_ι A.R (maximalIdeal A.R) n))

/-- Compatible morphisms to an algebraic space `Y` from objects identified with the
infinitesimal thickenings of a complete local base come from a unique morphism from the base. -/
private theorem existsUnique_hom_of_thickenings (Y : AlgebraicSpaces B S hS)
    (A : Deformation.Artin.FormalBase S) (T : BigFppfOver B S hS)
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of A.R)) (W : ℕ → BigFppfOver B S hS)
    (eW : ∀ n, (BigFppfOver.toScheme B S hS).obj (W n) ≅ adicThickening A.R (maximalIdeal A.R) n)
    (ι : ∀ n, W n ⟶ T)
    (hι : ∀ n, (BigFppfOver.toScheme B S hS).map (ι n) ≫ eT.hom =
      (eW n).hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A.R ^ (n + 1)))))
    (τ : ∀ n, W n ⟶ W (n + 1)) (hτ : ∀ n, τ n ≫ ι (n + 1) = ι n)
    (g : ∀ n, (schemeSpaceFunctor B S hS).obj (W n) ⟶ Y)
    (hg : ∀ n, (schemeSpaceFunctor B S hS).map (τ n) ≫ g (n + 1) = g n) :
    ∃! g₀ : (schemeSpaceFunctor B S hS).obj T ⟶ Y, ∀ n, (schemeSpaceFunctor B S hS).map (ι n) ≫ g₀ =
      g n := by
  have hR : IsNoetherianCompleteLocalRing A.R := ⟨A.noetherian, inferInstance, A.complete⟩
  obtain ⟨y, hy, hyu⟩ := FormalSpace.existsUnique_section_of_compatible_truncations hR
    (fun n => maximalIdeal A.R ^ (n + 1))
    (fun n => Ideal.pow_le_self n.succ_ne_zero) (fun n => Ideal.pow_le_pow_right (Nat.le_succ _))
    (fun n => ⟨n + 1, le_rfl⟩) (fun k => ⟨k, Ideal.pow_le_pow_right (Nat.le_succ k)⟩) Y.2
    T eT W eW ι hι τ hτ
    (fun n => yonedaEquiv (g n).hom) (fun n =>
      (yonedaEquiv_naturality _ _).trans (congrArg (fun k => yonedaEquiv k.hom) (hg n)))
  refine ⟨ObjectProperty.homMk (yonedaEquiv.symm y), fun n => ?_, fun g₀ hg₀ => ?_⟩
  · refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
    change yonedaEquiv (yoneda.map _ ≫ yonedaEquiv.symm y) = _
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
    exact hy n
  · refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
    change yonedaEquiv g₀.hom = yonedaEquiv (yonedaEquiv.symm y)
    rw [Equiv.apply_symm_apply]
    refine hyu _ fun n => ?_
    exact (yonedaEquiv_naturality _ _).trans (congrArg (fun k => yonedaEquiv k.hom) (hg₀ n))

/-- Compatible morphisms to the algebraic space `Y` from objects identified with the
infinitesimal thickenings of a complete local base come from a unique morphism from the base. -/
theorem existsUnique_hom_of_compatible_truncations (Y : AlgebraicSpaces B S hS)
    (A : Deformation.Artin.FormalBase S) (hA : B.Contains (Spec (.of A.R)))
    (c : ∀ n, B.Contains (A.truncation n)) (W : ℕ → BigFppfOver B S hS)
    (hW : ∀ n, W n = Deformation.Artin.truncationOver B S hS A c n)
    (τ : ∀ n, W n ⟶ W (n + 1))
    (hτ : ∀ n, τ n ≫ eqToHom (hW (n + 1)) ≫ Deformation.Artin.restrictionToBase B S hS A hA c
      (n + 1) = eqToHom (hW n) ≫ Deformation.Artin.restrictionToBase B S hS A hA c n)
    (g : ∀ n, (schemeSpaceFunctor B S hS).obj (W n) ⟶ Y)
    (hg : ∀ n, (schemeSpaceFunctor B S hS).map (τ n) ≫ g (n + 1) = g n) :
    ∃! g₀ : (schemeSpaceFunctor B S hS).obj (Deformation.Artin.baseOver B S hS A hA) ⟶ Y,
      ∀ n, (schemeSpaceFunctor B S hS).map (eqToHom (hW n) ≫
        Deformation.Artin.restrictionToBase B S hS A hA c n) ≫ g₀ = g n :=
  existsUnique_hom_of_thickenings Y A _ (Iso.refl _) W
    (fun n => eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj (hW n)))
    (fun n => eqToHom (hW n) ≫ Deformation.Artin.restrictionToBase B S hS A hA c n)
    (fun n => (Category.comp_id _).trans (by rw [Functor.map_comp, eqToHom_map]; rfl))
    τ hτ g hg

/-! ### Effectivity of formal objects -/

/-- A formal object of `Coh_{X/Y}` realized by an object over its complete local base is
effective: the realizing arrows are morphisms of `Coh_{X/Y}` over the inclusions of the
thickenings, compatible with the transitions. -/
theorem isEffective_of_coherentHoms
    (ξ : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      Deformation.Artin.FormalObject B S hS (coherentSiteProjection D.categoryData))
    (hA : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      B.Contains (Spec (.of ξ.base.R))) (x : CoherentObject D)
    (hx : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      x.T.left = Deformation.Artin.baseOver B S hS ξ.base hA)
    (r : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      ∀ n, CoherentHom (ξ.level n) x)
    (hcomp : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      ∀ n, CoherentHom.comp (ξ.transition n) (r (n + 1)) = r n)
    (hmap : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      ∀ n, (r n).base.left = eqToHom (ξ.level_eq n) ≫
        Deformation.Artin.restrictionToBase B S hS ξ.base hA ξ.contains n ≫ eqToHom hx.symm) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.FormalObject.IsEffective B S hS (coherentSiteProjection D.categoryData)
      D.isFiberedInGroupoids_siteProjection ξ :=
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  Deformation.Artin.FormalObject.isEffective_of_realization D.isFiberedInGroupoids_siteProjection
    (Deformation.Artin.FormalObject.Realization.mk (ξ := ξ) (hA := hA) (x := x) (hx := hx) r
      hcomp hmap)

/-- The comparison of inverse images for a composite of test schemes is the comparison at any
proof of `X_b ≫ X_c = X_{b ≫ c}`. -/
theorem compComparison_eq_modulePullbackTriangle {T₁ T₂ T₃ : SchemesOver D.Y} (b : T₁ ⟶ T₂)
    (c : T₂ ⟶ T₃) (hk : D.relativeMap b ≫ D.relativeMap c = D.relativeMap (b ≫ c)) :
    D.compComparison b c = modulePullbackTriangle B S hS hk := rfl

/-- A composite of morphisms of `Coh_{X/Y}` from the fibres, with the comparison of inverse
images taken at any equality `X_b ≫ X_{c₁} = X_{c₀}`. -/
theorem comp_mk_eq_mk {A₀ A₁ X : CoherentObject D} (m : CoherentHom A₀ A₁)
    (c₁ : A₁.T ⟶ X.T) (g₁ : (modulePullback B S hS (D.relativeMap c₁)).obj X.F ⟶ A₁.F)
    (hg₁ : IsIso g₁) (c₀ : A₀.T ⟶ X.T)
    (g₀ : (modulePullback B S hS (D.relativeMap c₀)).obj X.F ⟶ A₀.F) (hg₀ : IsIso g₀)
    (hb : m.base ≫ c₁ = c₀) (hk : D.relativeMap m.base ≫ D.relativeMap c₁ = D.relativeMap c₀)
    (η : modulePullback B S hS (D.relativeMap c₀) ⟶
      modulePullback B S hS (D.relativeMap c₁) ⋙ modulePullback B S hS (D.relativeMap m.base))
    (hη : (modulePullbackTriangle B S hS hk).hom = η)
    (h : η.app X.F ≫ (modulePullback B S hS (D.relativeMap m.base)).map g₁ ≫ m.fibre = g₀) :
    CoherentHom.comp m ⟨c₁, g₁, hg₁⟩ = ⟨c₀, g₀, hg₀⟩ := by
  subst hη
  obtain ⟨b, f, hf⟩ := m
  change b ≫ c₁ = c₀ at hb
  subst hb
  have e : D.compComparison b c₁ = modulePullbackTriangle B S hS hk :=
    D.compComparison_eq_modulePullbackTriangle b c₁ hk
  have hfib : Functor.fibreComp (D.compComparison b c₁) f g₁ = g₀ := by
    rw [Functor.fibreComp, e]
    exact h
  change CoherentHom.mk (b ≫ c₁) (Functor.fibreComp (D.compComparison b c₁) f g₁) _ = _
  congr 1

/-- `comp_mk_eq_mk` for an object given by its components. -/
theorem comp_mk_eq_mk_of {A₀ A₁ : CoherentObject D} (T : SchemesOver D.Y)
    (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) (hGq : G.IsQuasicoherentOnSite)
    (hfp : G.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (D.space T).2 (D.projection T).hom G)
    (hps : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
      (hU : IsClosed (D.support T G)),
      IsProperOver B S hS (D.space T).2 ((schemeSpaceFunctor B S hS).obj T.left).2
        (D.projection T).hom hp (D.support T G) hU)
    (m : CoherentHom A₀ A₁) (c₁ : A₁.T ⟶ T)
    (g₁ : (modulePullback B S hS (D.relativeMap c₁)).obj G ⟶ A₁.F)
    (hg₁ : IsIso g₁) (c₀ : A₀.T ⟶ T)
    (g₀ : (modulePullback B S hS (D.relativeMap c₀)).obj G ⟶ A₀.F) (hg₀ : IsIso g₀)
    (hb : m.base ≫ c₁ = c₀) (hk : D.relativeMap m.base ≫ D.relativeMap c₁ = D.relativeMap c₀)
    (η : modulePullback B S hS (D.relativeMap c₀) ⟶
      modulePullback B S hS (D.relativeMap c₁) ⋙ modulePullback B S hS (D.relativeMap m.base))
    (hη : (modulePullbackTriangle B S hS hk).hom = η)
    (h : η.app G ≫ (modulePullback B S hS (D.relativeMap m.base)).map g₁ ≫ m.fibre = g₀) :
    CoherentHom.comp m (⟨c₁, g₁, hg₁⟩ : CoherentHom A₁ ⟨T, G, hGq, hfp, hflat, hps⟩) =
      ⟨c₀, g₀, hg₀⟩ :=
  D.comp_mk_eq_mk (X := ⟨T, G, hGq, hfp, hflat, hps⟩) m c₁ g₁ hg₁ c₀ g₀ hg₀ hb hk η hη h

section FormalObjectData

variable (A : Deformation.Artin.FormalBase S) (c : ∀ n, B.Contains (A.truncation n))
  (hA : B.Contains (Spec (.of A.R))) (L : ℕ → CoherentObject D)
  (hL : ∀ n, (L n).T.left = Deformation.Artin.truncationOver B S hS A c n)
  (t : ∀ n, CoherentHom (L n) (L (n + 1)))
  (htb : ∀ n, (t n).base.left = eqToHom (hL n) ≫
    Deformation.Artin.truncationOverSucc B S hS A c n ≫ eqToHom (hL (n + 1)).symm)

include htb in
/-- The transitions of the levels are compatible with their maps to the complete local base. -/
theorem transition_base_left_comp (n : ℕ) :
    (t n).base.left ≫ eqToHom (hL (n + 1)) ≫
        Deformation.Artin.restrictionToBase B S hS A hA c (n + 1) =
      eqToHom (hL n) ≫ Deformation.Artin.restrictionToBase B S hS A hA c n := by
  rw [htb n]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    truncationOverSucc_restrictionToBase]

variable (g₀ : (schemeSpaceFunctor B S hS).obj (Deformation.Artin.baseOver B S hS A hA) ⟶ D.Y)
  (hg₀ : ∀ n, (schemeSpaceFunctor B S hS).map (eqToHom (hL n) ≫
    Deformation.Artin.restrictionToBase B S hS A hA c n) ≫ g₀ = (L n).T.hom)

/-- The maps of the levels to the complete local base, over `Y`. -/
def levelMap (n : ℕ) : (L n).T ⟶ CostructuredArrow.mk g₀ :=
  CostructuredArrow.homMk (eqToHom (hL n) ≫
    Deformation.Artin.restrictionToBase B S hS A hA c n) (hg₀ n)

/-- The underlying morphism of schemes of `levelMap`. -/
theorem levelMap_left (n : ℕ) : (D.levelMap A c hA L hL g₀ hg₀ n).left = eqToHom (hL n) ≫
    Deformation.Artin.restrictionToBase B S hS A hA c n := rfl

include htb in
/-- The maps `levelMap` are compatible with the transitions. -/
theorem transition_levelMap (n : ℕ) :
    (t n).base ≫ D.levelMap A c hA L hL g₀ hg₀ (n + 1) = D.levelMap A c hA L hL g₀ hg₀ n := by
  refine CostructuredArrow.hom_ext _ _ ?_
  rw [CostructuredArrow.comp_left, levelMap_left, levelMap_left]
  exact D.transition_base_left_comp A c hA L hL t htb n

/-- The identification of the levels with the thickenings. -/
def levelIso (n : ℕ) : (BigFppfOver.toScheme B S hS).obj (L n).T.left ≅
    adicThickening A.R (maximalIdeal A.R) n :=
  eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj (hL n))

/-- Under `levelIso`, the map of a level to the complete local base is the inclusion of the
thickening. -/
theorem levelIso_spec (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map ((D.levelMap A c hA L hL g₀ hg₀ n).left ≫
        eqToHom (rfl : (CostructuredArrow.mk g₀).left = _)) =
      (D.levelIso A c L hL n).hom ≫ adicThickeningι A.R (maximalIdeal A.R) n := by
  rw [eqToHom_refl, Category.comp_id, levelMap_left, Functor.map_comp, eqToHom_map]
  rfl

include hL in
/-- Every level is locally Noetherian. -/
theorem isLocallyNoetherian_level (n : ℕ) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (L n).T.left) := by
  rw [hL n]
  exact isLocallyNoetherian_truncationOver A c n

variable (T₀ : SchemesOver D.Y) (hT₀ : T₀.left = Deformation.Artin.baseOver B S hS A hA)
  (a : ∀ n, (L n).T ⟶ T₀)
  (ha : ∀ n, (a n).left ≫ eqToHom hT₀ = eqToHom (hL n) ≫
    Deformation.Artin.restrictionToBase B S hS A hA c n)
  (hta : ∀ n, (t n).base ≫ a (n + 1) = a n)

include ha in
/-- Under `levelIso`, the maps `a n` to the complete local base are the inclusions of the
thickenings. -/
theorem levelIso_spec' (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map ((a n).left ≫ eqToHom hT₀) =
      (D.levelIso A c L hL n).hom ≫ adicThickeningι A.R (maximalIdeal A.R) n := by
  rw [ha n, Functor.map_comp, eqToHom_map]
  rfl

include hT₀ in
/-- The projection `X_{T₀} ⟶ T₀` to the complete local base is locally of finite type. -/
theorem isLocallyOfFiniteType_projection_of :
    IsLocallyOfFiniteType B S hS (D.projection T₀).hom := by
  have h := (D.isFiniteType_projectionTo A hA hT₀).1
  have := isLocallyOfFiniteType_respectsIso B S hS
  exact (@MorphismProperty.cancel_right_of_respectsIso _ _
    (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ G) => IsLocallyOfFiniteType B S hS f)
    _ _ _ _ _ _ (isIso_schemeSpaceFunctor_map_eqToHom_hom hT₀)).1 h

include hT₀ in
/-- The base change of `X` to the complete local base is locally Noetherian. -/
theorem fact_space_of : Fact (HasEtaleLocalProperty B S hS (D.space T₀).1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
  D.fact_space _ (D.isLocallyOfFiniteType_projection_of A hA T₀ hT₀)
    (by rw [hT₀]; exact isLocallyNoetherian_baseOver A hA)

include ha hta in
/-- The algebraization of a compatible system of objects. -/
theorem exists_algebraization (hsep : IsSeparated B S hS D.f.hom) :
    ∃ (G : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2) (_ : IsCoherent B S hS _ _ G)
      (_ : HasProperSupport B S hS (D.space T₀).2 (schemeSpace _).2
        (D.projectionTo A hA hT₀).hom (D.isFiniteType_projectionTo A hA hT₀).1
        ((SheafOfModules.toSheaf _).obj G))
      (ψ : ∀ n, (modulePullback B S hS (D.relativeMap (a n))).obj G ≅ (L n).F),
      ∀ n, (modulePullbackTriangle B S hS (D.levelTower_comp (fun n => (L n).T) a
          (fun n => (t n).base) hta n)).hom.app G ≫
        (modulePullback B S hS (D.relativeMap (t n).base)).map (ψ (n + 1)).hom ≫
          (t n).fibre = (ψ n).hom := by
  have : IsNoetherianRing A.R := A.noetherian
  have : IsAdicComplete (maximalIdeal A.R) A.R := A.complete
  have := D.fact_space_of A hA T₀ hT₀
  obtain ⟨G, hG, hGp, ψ, hψ⟩ := (D.levelTower A hA hT₀ (fun n => (L n).T) a (fun n => (t n).base)
    hta (D.levelIso A c L hL) (D.levelIso_spec' A c hA L hL T₀ hT₀ a ha)).exists_of_compatible
    (fun n => (L n).F) (D.isFiniteType_projectionTo A hA hT₀)
    (D.isSeparated_projectionTo A hA hT₀ hsep)
    (fun n => D.isCoherent_F (L n) (D.isLocallyNoetherian_level A c L hL n))
    (fun n => @asIso _ _ _ _ (t n).fibre (t n).isIso_fibre)
    (L 0).properSupport.1 ⟨(L 0).properSupport.2.1, (L 0).properSupport.2.2⟩
  refine ⟨G, hG, hGp, ψ, fun n => ?_⟩
  rw [← D.levelTower_tri A hA hT₀ (fun n => (L n).T) a (fun n => (t n).base) hta
    (D.levelIso A c L hL) (D.levelIso_spec' A c hA L hL T₀ hT₀ a ha) n]
  exact hψ n

include ha hta in
/-- A compatible system of objects over the thickenings is realized by an object over the
complete local base. -/
theorem exists_realization (hsep : IsSeparated B S hS D.f.hom) :
    ∃ (x : CoherentObject D) (hx : x.T = T₀) (r : ∀ n, CoherentHom (L n) x),
      (∀ n, CoherentHom.comp (t n) (r (n + 1)) = r n) ∧
        ∀ n, (r n).base = a n ≫ eqToHom hx.symm := by
  have : IsNoetherianRing A.R := A.noetherian
  have := D.fact_space_of A hA T₀ hT₀
  obtain ⟨G, hG, hGp, ψ, hψ⟩ := D.exists_algebraization A c hA L hL t T₀ hT₀ a ha hta hsep
  have hπft := D.isFiniteType_projectionTo A hA hT₀
  have hGq : G.IsQuasicoherentOnSite := hG.toIsQuasicoherentOnSite
  have hT := D.levelTower A hA hT₀ (fun n => (L n).T) a (fun n => (t n).base) hta
    (D.levelIso A c L hL) (D.levelIso_spec' A c hA L hL T₀ hT₀ a ha)
  have hflatπ : IsFlatOver B S hS (D.space T₀).2 (D.projectionTo A hA hT₀).hom G :=
    hT.isFlatOver_of_isFlatOver_restrictions le_rfl hπft.1 G hG hGp
      fun n => IsFlatOver.of_iso B S hS _ (ψ n).symm (L n).flat
  have hflat : IsFlatOver B S hS (D.space T₀).2 (D.projection T₀).hom G :=
    @isFlatOver_of_isFlatOver_comp_isIso B S hS _ _ _ (D.projection T₀)
      ((schemeSpaceFunctor B S hS).map (eqToHom hT₀)) (isIso_schemeSpaceFunctor_map_eqToHom hT₀)
      G hGq hflatπ
  have hp₀ := D.isLocallyOfFiniteType_projection_of A hA T₀ hT₀
  have hprop := (D.hasProperSupport_projectionTo_iff A hA hT₀ hp₀ hπft.1 _).1 hGp
  have hfp : G.IsFinitePresentationOnSite :=
    (isCoherent_iff_isFinitePresentationOnSite B S hS _ _ G).1 hG
  have hps : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T₀).hom)
      (hU : IsClosed (D.support T₀ G)),
      IsProperOver B S hS (D.space T₀).2 ((schemeSpaceFunctor B S hS).obj T₀.left).2
        (D.projection T₀).hom hp (D.support T₀ G) hU := ⟨hp₀, hprop.1, hprop.2⟩
  refine ⟨⟨T₀, G, hGq, hfp, hflat, hps⟩, rfl, fun n => ⟨a n, (ψ n).hom, Iso.isIso_hom (ψ n)⟩,
    fun n => ?_, fun n => ?_⟩
  · exact D.comp_mk_eq_mk_of T₀ G hGq hfp hflat hps (t n) (a (n + 1))
      (ψ (n + 1)).hom (Iso.isIso_hom _) (a n) (ψ n).hom (Iso.isIso_hom _) (hta n)
      (D.levelTower_comp (fun n => (L n).T) a (fun n => (t n).base) hta n)
      (modulePullbackTriangle B S hS
        (D.levelTower_comp (fun n => (L n).T) a (fun n => (t n).base) hta n)).hom rfl (hψ n)
  · rw [eqToHom_refl, Category.comp_id]

end FormalObjectData

/-- Every formal object of `Coh_{X/Y}` is effective: when `f` is separated, a compatible system
of objects of `Coh_{X/Y}` over the infinitesimal thickenings of a complete local base is the
system of restrictions of an object over the base. -/
theorem isEffective_formalObject (hsep : IsSeparated B S hS D.f.hom)
    (ξ : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      Deformation.Artin.FormalObject B S hS (coherentSiteProjection D.categoryData)) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.FormalObject.IsEffective B S hS (coherentSiteProjection D.categoryData)
      D.isFiberedInGroupoids_siteProjection ξ := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  have hA : B.Contains (Spec (.of ξ.base.R)) := ξ.contains_spec_base
  let t : ∀ n, CoherentHom (ξ.level n) (ξ.level (n + 1)) := ξ.transition
  have hL : ∀ n, (ξ.level n).T.left = Deformation.Artin.truncationOver B S hS ξ.base ξ.contains n :=
    ξ.level_eq
  have htb : ∀ n, (t n).base.left = eqToHom (hL n) ≫
      Deformation.Artin.truncationOverSucc B S hS ξ.base ξ.contains n ≫
        eqToHom (hL (n + 1)).symm := D.formalObject_transition_base ξ
  obtain ⟨g₀, hg₀, -⟩ := existsUnique_hom_of_compatible_truncations D.Y ξ.base hA ξ.contains
    (fun n => (ξ.level n).T.left) hL (fun n => (t n).base.left)
    (D.transition_base_left_comp ξ.base ξ.contains hA ξ.level hL t htb)
    (fun n => (ξ.level n).T.hom) (fun n => CostructuredArrow.w (t n).base)
  obtain ⟨x, hx, r, hr, hrb⟩ := D.exists_realization ξ.base ξ.contains hA ξ.level hL t
    (CostructuredArrow.mk g₀) rfl (D.levelMap ξ.base ξ.contains hA ξ.level hL g₀ hg₀)
    (fun n => by rw [levelMap_left, eqToHom_refl, Category.comp_id])
    (D.transition_levelMap ξ.base ξ.contains hA ξ.level hL t htb g₀ hg₀) hsep
  have hxT : x.T.left = Deformation.Artin.baseOver B S hS ξ.base hA := by rw [hx]; rfl
  refine D.isEffective_of_coherentHoms ξ hA x hxT r hr fun n => ?_
  rw [hrb n, CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left, levelMap_left,
    Category.assoc]
  rfl

/-! ### Unique extension of compatible families of morphisms -/

/-- The module comparison of a composite of morphisms of `Coh_{X/Y}`, read through the
comparison of inverse images at any equality `X_m ≫ X_{c₁} = X_k`: the converse of
`comp_mk_eq_mk`. -/
theorem fibre_eq_of_comp_mk_eq {A₀ A₁ X : CoherentObject D} (m : CoherentHom A₀ A₁)
    (c₁ : A₁.T ⟶ X.T) (g₁ : (modulePullback B S hS (D.relativeMap c₁)).obj X.F ⟶ A₁.F)
    (hg₁ : IsIso g₁) (k : CoherentHom A₀ X) (h : CoherentHom.comp m ⟨c₁, g₁, hg₁⟩ = k)
    (hk : D.relativeMap m.base ≫ D.relativeMap c₁ = D.relativeMap k.base) :
    (modulePullbackTriangle B S hS hk).hom.app X.F ≫
      (modulePullback B S hS (D.relativeMap m.base)).map g₁ ≫ m.fibre = k.fibre := by
  have hb : m.base ≫ c₁ = k.base := congrArg CoherentHom.base h
  have e := D.comp_mk_eq_mk m c₁ g₁ hg₁ k.base
    ((modulePullbackTriangle B S hS hk).hom.app X.F ≫
      (modulePullback B S hS (D.relativeMap m.base)).map g₁ ≫ m.fibre) inferInstance hb hk
    _ rfl rfl
  exact eq_of_heq (heq_fibre_of_eq (e.symm.trans h))

/-- For comparisons `K ≅ G ⋙ F`, `Q ≅ P ⋙ G`, `R ≅ Q ⋙ F` and `R ≅ P ⋙ K` satisfying the
associativity coherence at `M`, a morphism out of `R M` that factors through `F` of a morphism
out of `Q M` also factors through `F` of the induced morphism out of `G (P M)`. -/
theorem Functor.hom_app_map_inv_app_comp {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] [Category* C₃] {P : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₃} {K : C₁ ⥤ C₃}
    {Q : C₀ ⥤ C₂} {R : C₀ ⥤ C₃} (tk : K ≅ G ⋙ F) (tq : Q ≅ P ⋙ G) (tr : R ≅ Q ⋙ F)
    (tkr : R ≅ P ⋙ K) (M : C₀)
    (key : F.map (tq.inv.app M) ≫ tr.inv.app M = tk.inv.app (P.obj M) ≫ tkr.inv.app M)
    {L₀ : C₃} {L₁ : C₂} (μ₁ : Q.obj M ⟶ L₁) (τ : F.obj L₁ ⟶ L₀) (μ₀ : R.obj M ⟶ L₀)
    (h : tr.hom.app M ≫ F.map μ₁ ≫ τ = μ₀) :
    tk.hom.app (P.obj M) ≫ F.map (tq.inv.app M ≫ μ₁) ≫ τ = tkr.inv.app M ≫ μ₀ := by
  have e : F.map (tq.inv.app M) ≫ F.map μ₁ ≫ τ =
      tk.inv.app (P.obj M) ≫ tkr.inv.app M ≫ tr.hom.app M ≫ F.map μ₁ ≫ τ := by
    rw [← reassoc_of% key, Iso.inv_hom_id_app_assoc]
  rw [← h, Functor.map_comp, Category.assoc, e, Iso.hom_inv_id_app_assoc]

/-- A family of comparisons out of the inverse images of `M` along `q` and `r = f ≫ q`, compatible
along `f`, stays compatible after reading the inverse image along `q` as the iterated inverse
image along `g` and `p`. -/
theorem modulePullbackTriangle_hom_app_map_inv_app_comp {W X Y Z : AlgebraicSpaces B S hS}
    {f : W ⟶ X} {g : X ⟶ Y} {p : Y ⟶ Z} {k : W ⟶ Y} {q : X ⟶ Z} {r : W ⟶ Z}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r)
    (M : Modules.{u, u} B S hS Z.1 Z.2) {L₀ : Modules.{u, u} B S hS W.1 W.2}
    {L₁ : Modules.{u, u} B S hS X.1 X.2} (μ₁ : (modulePullback B S hS q).obj M ⟶ L₁)
    (τ : (modulePullback B S hS f).obj L₁ ⟶ L₀) (μ₀ : (modulePullback B S hS r).obj M ⟶ L₀)
    (h : (modulePullbackTriangle B S hS hr).hom.app M ≫ (modulePullback B S hS f).map μ₁ ≫ τ =
      μ₀) :
    (modulePullbackTriangle B S hS hk).hom.app ((modulePullback B S hS p).obj M) ≫
        (modulePullback B S hS f).map ((modulePullbackTriangle B S hS hq).inv.app M ≫ μ₁) ≫ τ =
      (modulePullbackTriangle B S hS hkr).inv.app M ≫ μ₀ :=
  Functor.hom_app_map_inv_app_comp _ _ _ _ M
    (modulePullbackTriangle_inv_app_assoc B S hS hk hq hr hkr M) μ₁ τ μ₀ h

section UniqueExtension

variable (A : Deformation.Artin.FormalBase S) (hA : B.Contains (Spec (.of A.R)))
  (L : ℕ → CoherentObject D) (t : ∀ n, CoherentHom (L n) (L (n + 1)))
  (x : CoherentObject D) (hx : x.T.left = Deformation.Artin.baseOver B S hS A hA)
  (ρ : ∀ n, CoherentHom (L n) x) (hρ : ∀ n, CoherentHom.comp (t n) (ρ (n + 1)) = ρ n)
  (e : ∀ n, (BigFppfOver.toScheme B S hS).obj (L n).T.left ≅
    adicThickening A.R (maximalIdeal A.R) n)
  (he : ∀ n, (BigFppfOver.toScheme B S hS).map ((ρ n).base.left ≫ eqToHom hx) =
    (e n).hom ≫ adicThickeningι A.R (maximalIdeal A.R) n)
  (y : CoherentObject D) (hy : y.T.left = x.T.left) (μ : ∀ n, CoherentHom (L n) y)
  (hμb : ∀ n, (μ n).base.left = (ρ n).base.left ≫ eqToHom hy.symm)
  (hμ : ∀ n, CoherentHom.comp (t n) (μ (n + 1)) = μ n)

include hρ in
/-- The base maps of a compatible family `ρ` are compatible with the transitions. -/
theorem base_comp_base (n : ℕ) : (t n).base ≫ (ρ (n + 1)).base = (ρ n).base :=
  congrArg CoherentHom.base (hρ n)

include hρ he hμb in
/-- Two objects of `Coh_{X/Y}` over the same complete local base receiving compatible families
over the same morphisms of schemes have the same morphism to `Y`. -/
theorem map_eqToHom_comp_hom :
    (schemeSpaceFunctor B S hS).map (eqToHom hy.symm) ≫ y.T.hom = x.T.hom := by
  have hτ : ∀ n, (t n).base.left ≫ (ρ (n + 1)).base.left = (ρ n).base.left := fun n => by
    rw [← CostructuredArrow.comp_left, D.base_comp_base L t x ρ hρ n]
  have hι : ∀ n, (BigFppfOver.toScheme B S hS).map (ρ n).base.left ≫
      (eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj hx)).hom =
        (e n).hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A.R ^ (n + 1)))) :=
    fun n => by
      have h := he n
      rwa [Functor.map_comp, eqToHom_map] at h
  obtain ⟨s, -, hsu⟩ := existsUnique_hom_of_thickenings D.Y A x.T.left
    (eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj hx)) (fun n => (L n).T.left) e
    (fun n => (ρ n).base.left) hι (fun n => (t n).base.left) hτ (fun n => (L n).T.hom)
    (fun n => CostructuredArrow.w (t n).base)
  have hw : ∀ n, (schemeSpaceFunctor B S hS).map (ρ n).base.left ≫
      ((schemeSpaceFunctor B S hS).map (eqToHom hy.symm) ≫ y.T.hom) = (L n).T.hom := fun n => by
    rw [← Category.assoc, ← Functor.map_comp, ← hμb n]
    exact CostructuredArrow.w (μ n).base
  exact (hsu _ hw).trans (hsu _ fun n => CostructuredArrow.w (ρ n).base).symm

variable (φb : x.T ⟶ y.T) (hφb : φb.left = eqToHom hy.symm)

include hφb hμb in
/-- The base map of `ρ n` followed by `φb` is the base map of `μ n`. -/
theorem base_comp_extensionBase (n : ℕ) : (ρ n).base ≫ φb = (μ n).base :=
  CostructuredArrow.hom_ext _ _ (by rw [CostructuredArrow.comp_left, hφb, hμb n])

include hφb hμb in
/-- The base change along `ρ n` followed by the one along `φb` is the base change along `μ n`. -/
theorem relativeMap_comp_extensionBase (n : ℕ) :
    D.relativeMap (ρ n).base ≫ D.relativeMap φb = D.relativeMap (μ n).base := by
  rw [← baseChangeMap_comp, D.base_comp_extensionBase L x ρ y hy μ hμb φb hφb n]

include hφb in
/-- `φb` is an isomorphism. -/
theorem isIso_extensionBase : IsIso φb := by
  have hw : (schemeSpaceFunctor B S hS).map (eqToHom hy) ≫ x.T.hom = y.T.hom := by
    rw [← CostructuredArrow.w φb, hφb, ← Category.assoc, ← Functor.map_comp, eqToHom_trans,
      eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  refine ⟨CostructuredArrow.homMk (eqToHom hy) hw, CostructuredArrow.hom_ext _ _ ?_,
    CostructuredArrow.hom_ext _ _ ?_⟩
  · rw [CostructuredArrow.comp_left, hφb]
    exact (eqToHom_trans hy.symm hy).trans (eqToHom_refl _ _)
  · rw [CostructuredArrow.comp_left, hφb]
    exact (eqToHom_trans hy hy.symm).trans (eqToHom_refl _ _)

include hφb in
/-- The base change along `φb` is an isomorphism. -/
theorem isIso_relativeMap_extensionBase : IsIso (D.relativeMap φb) := by
  have := D.isIso_extensionBase x y hy φb hφb
  exact ⟨⟨D.relativeMap (inv φb), by
    rw [← baseChangeMap_comp, IsIso.hom_inv_id, baseChangeMap_id],
    by rw [← baseChangeMap_comp, IsIso.inv_hom_id, baseChangeMap_id]⟩⟩

include hφb in
/-- The base change along `φb` commutes with the projections to the complete local base. -/
theorem relativeMap_extensionBase_comp_projectionTo :
    D.relativeMap φb ≫ D.projectionTo A hA (hy.trans hx) = D.projectionTo A hA hx := by
  have h1 : D.relativeMap φb ≫ D.projection y.T =
      D.projection x.T ≫ (schemeSpaceFunctor B S hS).map φb.left :=
    baseChangeMap_comp_inclusion D.f φb
  have h2 : (schemeSpaceFunctor B S hS).map φb.left ≫
      (schemeSpaceFunctor B S hS).map (eqToHom (hy.trans hx)) =
        (schemeSpaceFunctor B S hS).map (eqToHom hx) := by
    rw [← Functor.map_comp, hφb, eqToHom_trans]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (schemeSpaceFunctor B S hS).map (eqToHom (hy.trans hx))) h1).trans
      ((Category.assoc _ _ _).trans (congrArg (D.projection x.T ≫ ·) h2)))

include hφb in
/-- The inverse image of the module of `y` along the identification of the base changes has
support proper over the complete local base. -/
theorem hasProperSupport_pullback_extensionBase :
    HasProperSupport B S hS (D.space x.T).2 (schemeSpace _).2 (D.projectionTo A hA hx).hom
      (D.isFiniteType_projectionTo A hA hx).1
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS (D.relativeMap φb)).obj y.F)) := by
  have := D.isIso_relativeMap_extensionBase x y hy φb hφb
  have := D.fact_space_of A hA y.T (hy.trans hx)
  have hyF := D.isCoherent_F y (by rw [hy, hx]; exact isLocallyNoetherian_baseOver A hA)
  have hgy := (D.isFiniteType_projectionTo A hA (hy.trans hx)).1
  have heq := D.relativeMap_extensionBase_comp_projectionTo A hA x hx y hy φb hφb
  have hg₁ : IsLocallyOfFiniteType B S hS (D.relativeMap φb ≫
      D.projectionTo A hA (hy.trans hx)).hom := by
    rw [heq]
    exact (D.isFiniteType_projectionTo A hA hx).1
  have := hyF.toIsCoherentOnSite
  have h := hasProperSupport_modulePullback_iso (D.relativeMap φb)
    (D.projectionTo A hA (hy.trans hx)) hgy hg₁ y.F y.quasicoherent
    (isFiniteTypeOnSite_of_isCoherentOnSite B S hS (D.space y.T) y.F)
    (D.hasProperSupport_F A hA y (hy.trans hx) hgy)
  exact (hasProperSupport_congr_hom B S hS (D.space x.T).2 (schemeSpace _).2
    (by rw [heq]) hg₁ (D.isFiniteType_projectionTo A hA hx).1 _).1 h

include hρ hφb hμb hμ in
/-- The restrictions of the inverse image of the module of `y` are compatible with the
transitions. -/
theorem pullback_extensionBase_compatible (n : ℕ) :
    (modulePullbackTriangle B S hS (D.levelTower_comp (fun n => (L n).T) (fun n => (ρ n).base)
        (fun n => (t n).base) (D.base_comp_base L t x ρ hρ) n)).hom.app
          ((modulePullback B S hS (D.relativeMap φb)).obj y.F) ≫
      (modulePullback B S hS (D.relativeMap (t n).base)).map
        ((modulePullbackTriangle B S hS
          (D.relativeMap_comp_extensionBase L x ρ y hy μ hμb φb hφb (n + 1))).inv.app y.F ≫
            (μ (n + 1)).fibre) ≫ (t n).fibre =
      (modulePullbackTriangle B S hS
        (D.relativeMap_comp_extensionBase L x ρ y hy μ hμb φb hφb n)).inv.app y.F ≫
          (μ n).fibre := by
  have hr : D.relativeMap (t n).base ≫ D.relativeMap (μ (n + 1)).base =
      D.relativeMap (μ n).base := by
    rw [← baseChangeMap_comp, D.base_comp_base L t y μ hμ n]
  exact modulePullbackTriangle_hom_app_map_inv_app_comp _ _ hr _ y.F _ _ _
    (D.fibre_eq_of_comp_mk_eq (t n) (μ (n + 1)).base (μ (n + 1)).fibre inferInstance
      (μ n) (hμ n) hr)

include hρ he hφb hμb hμ in
/-- The compatible family `μ` of morphisms of `Coh_{X/Y}` from the levels to `y` comes from a
unique morphism `x ⟶ y` over `φb`. -/
theorem existsUnique_extension_of_base :
    ∃! φ : CoherentHom x y, φ.base = φb ∧ ∀ n, CoherentHom.comp (ρ n) φ = μ n := by
  have : IsNoetherianRing A.R := A.noetherian
  have : IsAdicComplete (maximalIdeal A.R) A.R := A.complete
  have := D.fact_space_of A hA x.T hx
  have hπ := D.isFiniteType_projectionTo A hA hx
  have hF := D.isCoherent_F x (by rw [hx]; exact isLocallyNoetherian_baseOver A hA)
  have hFp := D.hasProperSupport_F A hA x hx hπ.1
  have := D.fact_space_of A hA y.T (hy.trans hx)
  have hyF := D.isCoherent_F y (by rw [hy, hx]; exact isLocallyNoetherian_baseOver A hA)
  have hG := isCoherent_modulePullback B S hS (D.relativeMap φb) y.F hyF
  have hGp := D.hasProperSupport_pullback_extensionBase A hA x hx y hy φb hφb
  have hT := D.levelTower A hA hx (fun n => (L n).T) (fun n => (ρ n).base)
    (fun n => (t n).base) (D.base_comp_base L t x ρ hρ) e he
  have htri : ∀ n, hT.tri n = modulePullbackTriangle B S hS (D.levelTower_comp
      (fun n => (L n).T) (fun n => (ρ n).base) (fun n => (t n).base)
      (D.base_comp_base L t x ρ hρ) n) := fun n => rfl
  obtain ⟨μ', hμ'⟩ : ∃ μ' : ∀ n, (modulePullback B S hS (D.relativeMap (ρ n).base)).obj
      ((modulePullback B S hS (D.relativeMap φb)).obj y.F) ⟶ (L n).F,
      μ' = fun n => (modulePullbackTriangle B S hS
        (D.relativeMap_comp_extensionBase L x ρ y hy μ hμb φb hφb n)).inv.app y.F ≫
          (μ n).fibre := ⟨_, rfl⟩
  have : ∀ n, IsIso (μ' n) := fun n => by rw [hμ']; infer_instance
  have hρ' : ∀ n, (hT.tri n).hom.app x.F ≫
      (modulePullback B S hS (D.relativeMap (t n).base)).map (ρ (n + 1)).fibre ≫ (t n).fibre =
        (ρ n).fibre := fun n => by
    rw [htri]
    exact D.fibre_eq_of_comp_mk_eq (t n) (ρ (n + 1)).base (ρ (n + 1)).fibre inferInstance (ρ n)
      (hρ n) _
  have hμc : ∀ n, (hT.tri n).hom.app ((modulePullback B S hS (D.relativeMap φb)).obj y.F) ≫
      (modulePullback B S hS (D.relativeMap (t n).base)).map (μ' (n + 1)) ≫ (t n).fibre =
        μ' n := fun n => by
    rw [htri, hμ']
    exact D.pullback_extensionBase_compatible L t x ρ hρ y hy μ hμb hμ φb hφb n
  obtain ⟨ψ, hψ, hψu⟩ := hT.existsUnique_hom_of_compatible_levels hπ.1 x.F _ hF hG hFp hGp
    (fun n => (L n).F) (fun n => (t n).fibre) (fun n => (ρ n).fibre) μ' hρ' hμc
  obtain ⟨ψ', hψ', -⟩ := hT.existsUnique_hom_of_compatible_levels hπ.1 _ x.F hG hF hGp hFp
    (fun n => (L n).F) (fun n => (t n).fibre) μ' (fun n => (ρ n).fibre) hμc hρ'
  obtain ⟨w₁, -, u₁⟩ := hT.existsUnique_hom_of_compatible_levels hπ.1 x.F x.F hF hF hFp hFp
    (fun n => (L n).F) (fun n => (t n).fibre) (fun n => (ρ n).fibre) (fun n => (ρ n).fibre)
    hρ' hρ'
  obtain ⟨w₂, -, u₂⟩ := hT.existsUnique_hom_of_compatible_levels hπ.1 _ _ hG hG hGp hGp
    (fun n => (L n).F) (fun n => (t n).fibre) μ' μ' hμc hμc
  have e₁ : ψ' ≫ ψ = 𝟙 _ :=
    (u₁ _ fun n => by rw [Functor.map_comp, Category.assoc, hψ n, hψ' n]).trans
      (u₁ _ fun n => by rw [CategoryTheory.Functor.map_id, Category.id_comp]).symm
  have e₂ : ψ ≫ ψ' = 𝟙 _ :=
    (u₂ _ fun n => by rw [Functor.map_comp, Category.assoc, hψ' n, hψ n]).trans
      (u₂ _ fun n => by rw [CategoryTheory.Functor.map_id, Category.id_comp]).symm
  have hiso : IsIso ψ := ⟨ψ', e₂, e₁⟩
  refine ⟨⟨φb, ψ, hiso⟩, ⟨rfl, fun n => ?_⟩, ?_⟩
  · refine D.comp_mk_eq_mk (ρ n) φb ψ hiso (μ n).base (μ n).fibre inferInstance
      (D.base_comp_extensionBase L x ρ y hy μ hμb φb hφb n)
      (D.relativeMap_comp_extensionBase L x ρ y hy μ hμb φb hφb n) _ rfl ?_
    rw [hψ n, hμ']
    exact Iso.hom_inv_id_app_assoc _ _ _
  · rintro ⟨b', f', hf'⟩ ⟨hb', hc⟩
    change b' = φb at hb'
    subst b'
    have : f' = ψ := hψu f' fun n => by
      have h₁ := D.fibre_eq_of_comp_mk_eq (ρ n) φb f' hf' (μ n) (hc n)
        (D.relativeMap_comp_extensionBase L x ρ y hy μ hμb φb hφb n)
      simp only [hμ']
      rw [← h₁, Iso.inv_hom_id_app_assoc]
    subst this
    rfl

omit hφb in
include hρ he hμb hμ in
/-- A compatible family of morphisms of `Coh_{X/Y}` from the levels to an object `y` over the
same scheme as `x`, lying over the restrictions, comes from a unique morphism `x ⟶ y` over the
identity of that scheme. -/
theorem existsUnique_extension :
    ∃! φ : CoherentHom x y, φ.base.left = eqToHom hy.symm ∧
      ∀ n, CoherentHom.comp (ρ n) φ = μ n := by
  have hw := D.map_eqToHom_comp_hom A hA L t x hx ρ hρ e he y hy μ hμb
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, hu⟩ := D.existsUnique_extension_of_base A hA L t x hx ρ hρ e he y hy μ
    hμb hμ (CostructuredArrow.homMk (eqToHom hy.symm) hw) rfl
  refine ⟨φ, ⟨by rw [hφ₁]; rfl, hφ₂⟩, fun φ' ⟨h₁, h₂⟩ => hu φ' ⟨?_, h₂⟩⟩
  exact CostructuredArrow.hom_ext _ _ (by rw [h₁]; rfl)

end UniqueExtension

/-- The identification of a level of a formal object with the thickening of its own complete
local base, transported to an equal complete local base. -/
theorem toScheme_map_eq_eqToIso_comp_adicThickeningι {A' A : Deformation.Artin.FormalBase S}
    (h : A' = A) (hA : B.Contains (Spec (.of A.R))) (c : ∀ n, B.Contains (A'.truncation n))
    (n : ℕ) {W : BigFppfOver B S hS} (hW : W = Deformation.Artin.truncationOver B S hS A' c n)
    (f : W ⟶ Deformation.Artin.baseOver B S hS A hA)
    (hf : (BigFppfOver.toScheme B S hS).map (eqToHom hW.symm ≫ f) =
      adicThickeningι A'.R (maximalIdeal A'.R) n ≫
        eqToHom (congrArg (fun A : Deformation.Artin.FormalBase S => Spec (.of A.R)) h)) :
    (BigFppfOver.toScheme B S hS).map f =
      (eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj hW) ≪≫
        eqToIso (congrArg (fun A : Deformation.Artin.FormalBase S =>
          adicThickening A.R (maximalIdeal A.R) n) h)).hom ≫
        adicThickeningι A.R (maximalIdeal A.R) n := by
  subst h hW
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Iso.trans_hom,
    eqToIso.hom] at hf ⊢
  exact hf

/-- The functor of Equation 07X6 at `Coh_{X/Y}` has unique extensions. -/
theorem hasUniqueExtensions_approximationFunctor :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.HasUniqueExtensions D.approximationFunctor := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  intro r hb htrans hι x y hy m hml hm
  have he := fun n => toScheme_map_eq_eqToIso_comp_adicThickeningι (hb x)
    (Deformation.Artin.chosenContains B S hS _ x.obj) (D.approximationFunctor.obj x).contains n
    ((D.approximationFunctor.obj x).level_eq n) _ (hι x n)
  have hμb : ∀ n, (m n).base.left = (r x n).base.left ≫ eqToHom hy.symm := fun n => by
    have := hml n
    have h := IsHomLift.fac' (coherentSiteProjection D.categoryData)
      ((coherentSiteProjection D.categoryData).map (r x n)) (m n)
    rwa [eqToHom_refl, Category.id_comp] at h
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, hu⟩ := D.existsUnique_extension
    (Deformation.Artin.chosenBase B S hS _ x.obj) (Deformation.Artin.chosenContains B S hS _ x.obj)
    (fun n => (D.approximationFunctor.obj x).level n)
    (fun n => (D.approximationFunctor.obj x).transition n) x.obj.1
    (Deformation.Artin.chosenBase_eq B S hS _ x.obj) (fun n => r x n) (htrans x) _ he y hy
    (fun n => m n) hμb hm
  refine ⟨φ, ⟨IsHomLift.of_fac' _ _ _ rfl hy ?_, hφ₂⟩, fun φ' ⟨h₁, h₂⟩ => hu φ' ⟨?_, h₂⟩⟩
  · rw [eqToHom_refl, Category.id_comp, Category.id_comp]
    exact hφ₁
  · have := h₁
    have h := IsHomLift.fac' (coherentSiteProjection D.categoryData)
      (𝟙 ((coherentSiteProjection D.categoryData).obj x.obj.1)) φ'
    rwa [eqToHom_refl, Category.id_comp, Category.id_comp] at h

/-- The functor of Equation 07X6 at `Coh_{X/Y}` is full. -/
theorem full_approximationFunctor :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    D.approximationFunctor.Full := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  have : (coherentSiteProjection D.categoryData).IsFibered :=
    D.isFiberedInGroupoids_siteProjection.isFibered
  exact Deformation.Artin.full_of_isApproximationFunctor_of_hasUniqueExtensions
    D.isFiberedInGroupoids_siteProjection D.hasUniqueExtensions_approximationFunctor
    D.isApproximationFunctor_approximationFunctor

/-- The functor of Equation 07X6 at `Coh_{X/Y}` is faithful. -/
theorem faithful_approximationFunctor :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    D.approximationFunctor.Faithful := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  have : (coherentSiteProjection D.categoryData).IsFibered :=
    D.isFiberedInGroupoids_siteProjection.isFibered
  exact Deformation.Artin.faithful_of_isApproximationFunctor_of_hasUniqueExtensions
    D.isFiberedInGroupoids_siteProjection D.hasUniqueExtensions_approximationFunctor
    D.isApproximationFunctor_approximationFunctor

/-- In Situation 08KB, with `f : X ⟶ Y` separated, the functor of Artin's Axioms, Equation 07X6,
at `Coh_{X/Y}` — from objects over spectra of Noetherian complete local rings with residue field
of finite type over `S` to formal objects — is an equivalence. No Noetherian hypothesis on `S` is
assumed. -/
@[stacks 08W9]
theorem isEquivalence_approximationFunctor (hsep : IsSeparated B S hS D.f.hom) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    D.approximationFunctor.IsEquivalence :=
  D.isEquivalence_approximationFunctor_of_full_of_faithful_of_forall_isEffective
    D.full_approximationFunctor D.faithful_approximationFunctor
    (fun ξ => D.isEffective_formalObject hsep ξ)

end CoherentSituation

end AlgebraicGeometry.Space

end
