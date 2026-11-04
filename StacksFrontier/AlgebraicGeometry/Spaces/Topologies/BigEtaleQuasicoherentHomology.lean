module

public import StacksFrontier.Algebra.Homology.RightDerivedPreservesHomology
public import StacksFrontier.CategoryTheory.KanExtension.PointwiseOfIsEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.PushforwardVanishingOnACover
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleRightAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfQuasicoherentHomologyCohomology

/-!
# The homology of a complex of pulled back quasi-coherent modules on the big étale site

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site over the
same big fppf site of schemes, `X` an object of `T` and `𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃` a complex of
quasi-coherent `𝒪_X`-modules on the spaces-étale site of `X`. Write `𝓗_et` for the homology of
`π_X^*𝓕₁ ⟶ π_X^*𝓕₂ ⟶ π_X^*𝓕₃` on `(Spaces/X)_étale` and `𝓗_fppf` for that of
`a_X^*𝓕₁ ⟶ a_X^*𝓕₂ ⟶ a_X^*𝓕₃` on `(Spaces/X)_fppf`. Then `𝓗_et ≅ ε_{X,*}𝓗_fppf`, and both
have vanishing higher cohomology on affine objects (Stacks 0DGQ).

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isZero_rightDerived_fppfToBigEtale_pushforward_of_isZero_H'`:
  `R^pε_{X,*}M = 0` for `p > 0` when the higher cohomology of `M` vanishes on affine objects.
* `AlgebraicGeometry.BigFppfSpaceSite.nonempty_homology_pullback_iso`: `𝓗_et ≅ ε_{X,*}𝓗_fppf`.
* `AlgebraicGeometry.BigFppfSpaceSite.isZero_H'_homology_etale`: `H^p_et(U, 𝓗_et) = 0` for
  `p > 0` and `U` affine.
* `AlgebraicGeometry.BigFppfSpaceSite.homology_pullback_of_quasicoherent`: `𝓗_et ≅ ε_{X,*}𝓗_fppf`,
  and `H^p_et(U, 𝓗_et) = 0`, `H^p_fppf(U, 𝓗_fppf) = 0` for `p > 0` and `U` affine.

## References

* [Stacks Project, Tag 0DGQ](https://stacks.math.columbia.edu/tag/0DGQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces}
  (E : BigEtaleSpaceSite S) (h : T.schemeSite = E.fppfSite)

/-- The objects `W` of the big étale site of `X` whose image under `ε_X` is affine. -/
def epsilonAffinePresieve (V : Over (etaleSpace T E h X)) : Presieve V :=
  fun W _ ↦ BigFppfSpaceOver.IsAffineSchemeOver T X
    ((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u.obj W)

/-- **The objects of the big étale site of `X` with affine image under `ε_X` cover.** -/
theorem generate_epsilonAffinePresieve_mem (V : Over (etaleSpace T E h X)) :
    Sieve.generate (epsilonAffinePresieve E h V) ∈ E.bigEtaleTopology (etaleSpace T E h X) V := by
  obtain ⟨_, _, F, _⟩ := E
  change T.schemeSite = F at h
  cases h
  exact GrothendieckTopology.superset_covering _
    (by rw [Sieve.generate_le_iff]; exact fun W g hg ↦ Sieve.le_generate _ _ _ hg)
    (BigEtaleSpaceSite.generate_affineSchemePresieve_mem _ V)

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- **The higher direct images along `ε_X` of a module with vanishing higher cohomology on affine
objects vanish**: `R^pε_{X,*}M = 0` for `p > 0`. -/
theorem isZero_rightDerived_fppfToBigEtale_pushforward_of_isZero_H'
    (M : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X)).O))
    (hM : ∀ U : Over X, BigFppfSpaceOver.IsAffineSchemeOver T X U → ∀ p : ℕ, 0 < p →
      IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj M) p U))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos).rightDerived
      p).obj M) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve.{
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u _ _
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.fSharpRing (q + 1) _ (fun V ↦ ?_)
  refine ⟨epsilonAffinePresieve E h V, generate_epsilonAffinePresieve_mem E h V,
    fun W g hW ↦ ?_⟩
  exact
   Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'_chgUniv.{
    u + 1, u + 1, u + 1} _ _ _ q _ (hM _ hW (q + 1) q.succ_pos)

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- **The kernel of `a_X^*𝓕₁ ⟶ a_X^*𝓕₂` has no higher cohomology on affine objects.** -/
theorem isZero_H'_kernel_pullback
    (Q : ShortComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)))
    [Q.X₁.IsQuasicoherentOnSite] [Q.X₂.IsQuasicoherentOnSite]
    (U : Over X) (hU : BigFppfSpaceOver.IsAffineSchemeOver T X U) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj
      (kernel (Q.map (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos).f))
      p U) := by
  let a := (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos
  let Q' : ShortComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)) :=
    ShortComplex.mk (0 : Q.X₁ ⟶ Q.X₁) Q.f zero_comp
  have : Q'.X₁.IsQuasicoherentOnSite := inferInstanceAs Q.X₁.IsQuasicoherentOnSite
  have : Q'.X₂.IsQuasicoherentOnSite := inferInstanceAs Q.X₁.IsQuasicoherentOnSite
  have : Q'.X₃.IsQuasicoherentOnSite := inferInstanceAs Q.X₂.IsQuasicoherentOnSite
  let e : (Q'.map a).homology ≅ kernel (Q.map a).f :=
    ((Q'.map a).asIsoHomologyπ (a.map_zero _ _)).symm ≪≫ (Q'.map a).cyclesIsoKernel
  exact (isZero_H'_homology_pullback Q' U hU p hp).of_iso
    (((Sheaf.cohomologyPresheafFunctor _ p).mapIso
      ((SheafOfModules.toSheaf _).mapIso e)).app (op U)).symm

/-- The direct image `ε_{X,*}` is left exact. -/
instance fppfToBigEtale_pushforwardTopos_preservesFiniteLimits :
    PreservesFiniteLimits
      (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos :=
  have := (fppfToBigEtaleRingedHom T E h
    X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.isRightAdjoint
  inferInstance

/-- **`ε_{X,*}` preserves the homology of `a_X^*𝓕₁ ⟶ a_X^*𝓕₂ ⟶ a_X^*𝓕₃`** for a complex of
quasi-coherent modules. -/
theorem fppfToBigEtale_preservesLeftHomologyOf_pullback
    (Q : ShortComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)))
    [Q.X₁.IsQuasicoherentOnSite] [Q.X₂.IsQuasicoherentOnSite] :
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.PreservesLeftHomologyOf
      (Q.map (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos) := by
  have := enoughInjectives_bigFppfModules (T := T) (X := X)
  have hker := isZero_rightDerived_fppfToBigEtale_pushforward_of_isZero_H' E h _
    (fun U hU p hp ↦ isZero_H'_kernel_pullback Q U hU p hp)
  exact Stacks.Cohomology.RightDerivedDelta.preservesLeftHomologyOf_of_isZero_rightDerived _ _
    (isZero_rightDerived_fppfToBigEtale_pushforward_pullback E h Q.X₁ 1 one_pos)
    (hker 1 one_pos) (hker 2 two_pos)

/-- Reading an `𝒪_X`-module on the spaces-étale site of `X` as one on the spaces-étale site of
`X` seen in the big étale site keeps quasi-coherence. -/
instance isQuasicoherentOnSite_toEtaleSpaceModules_obj
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [hF : F.IsQuasicoherentOnSite] :
    ((toEtaleSpaceModules T E h X).obj F).IsQuasicoherentOnSite := by
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    exact hF

/-- Reading modules on the spaces-étale site through `toEtaleSpaceModules` preserves zero
morphisms. -/
instance toEtaleSpaceModules_preservesZeroMorphisms :
    (toEtaleSpaceModules T E h X).PreservesZeroMorphisms := by
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    exact inferInstanceAs (𝟭 _).PreservesZeroMorphisms

/-- The direct image `π_{X,*}` of sheaves of modules is additive. -/
instance spacesEtaleRestriction_pushforwardTopos_additive :
    (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
      (etaleSpace T E h X)).toRingedToposSiteHom.pushforwardTopos.Additive where
  map_add := by intros; rfl

/-- The pullback `π_X^*` of sheaves of modules is additive. -/
instance spacesEtaleRestriction_pullbackTopos_additive :
    (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
      (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos.Additive :=
  (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
    (etaleSpace T E h
      X)).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.left_adjoint_additive

/-- **Stacks 0DGQ (a): `𝓗_et ≅ ε_{X,*}𝓗_fppf`.** For a complex `𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃` of
quasi-coherent `𝒪_X`-modules, the homology of `π_X^*𝓕₁ ⟶ π_X^*𝓕₂ ⟶ π_X^*𝓕₃` on
`(Spaces/X)_étale` is the direct image along `ε_X` of the homology of
`a_X^*𝓕₁ ⟶ a_X^*𝓕₂ ⟶ a_X^*𝓕₃` on `(Spaces/X)_fppf`. -/
theorem nonempty_homology_pullback_iso
    (Q : ShortComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)))
    [Q.X₁.IsQuasicoherentOnSite] [Q.X₂.IsQuasicoherentOnSite] [Q.X₃.IsQuasicoherentOnSite] :
    Nonempty ((Q.map (toEtaleSpaceModules T E h X ⋙
        (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
          (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos)).homology ≅
      (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.obj
        (Q.map
          (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos).homology) := by
  obtain ⟨c⟩ := nonempty_pullbackTopos_iso_comp T E h X
  let ι := toEtaleSpaceModules T E h X
  let π := (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
    (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos
  let ε := (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom
  let a := (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos
  let η := ε.pullbackPushforwardAdjunctionTopos.unit
  let τ : ι ⋙ π ⟶ a ⋙ ε.pushforwardTopos :=
    { app := fun F ↦ η.app (π.obj (ι.obj F)) ≫ ε.pushforwardTopos.map (c.inv.app F)
      naturality := fun F G φ ↦ by
        have h₁ := η.naturality (π.map (ι.map φ))
        have h₂ : ε.pullbackTopos.map (π.map (ι.map φ)) ≫ c.inv.app G = c.inv.app F ≫ a.map φ :=
          c.inv.naturality φ
        dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ ⊢
        rw [reassoc_of% h₁, ← ε.pushforwardTopos.map_comp, h₂, Functor.map_comp,
          Category.assoc] }
  have hτ : ∀ F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O),
      F.IsQuasicoherentOnSite → IsIso (τ.app F) := by
    intro F hF
    have := isIso_fppfToBigEtale_unit_app_pullback T E h X (ι.obj F)
    exact IsIso.comp_isIso
  have : IsIso (Q.mapNatTrans τ) := by
    have : IsIso (Q.mapNatTrans τ).τ₁ := hτ Q.X₁ inferInstance
    have : IsIso (Q.mapNatTrans τ).τ₂ := hτ Q.X₂ inferInstance
    have : IsIso (Q.mapNatTrans τ).τ₃ := hτ Q.X₃ inferInstance
    exact ShortComplex.isIso_of_isIso _
  have := fppfToBigEtale_preservesLeftHomologyOf_pullback E h Q
  exact ⟨ShortComplex.homologyMapIso (asIso (Q.mapNatTrans τ)) ≪≫
    (Q.map a).mapHomologyIso ε.pushforwardTopos⟩

/-! ### The étale vanishing -/

/-- The functor of `ε_X` is an equivalence of categories. -/
instance fppfToBigEtaleRingedHom_u_isEquivalence :
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u.IsEquivalence :=
  inferInstanceAs
    (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse.IsEquivalence

/-- An affine object of the big étale site of `X` has affine image under `ε_X`. -/
theorem isAffineSchemeOver_fppfToBigEtale_obj {U : Over (etaleSpace T E h X)}
    (hU : BigEtaleSpaceSite.IsAffineSchemeOver E (etaleSpace T E h X) U) :
    BigFppfSpaceOver.IsAffineSchemeOver T X
      ((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u.obj U) := by
  obtain ⟨_, _, F, _⟩ := E
  change T.schemeSite = F at h
  cases h
  exact hU

/-- **Restriction of abelian sheaves along `ε_X` preserves injective objects.** -/
theorem fppfToBigEtale_sheafPushforwardContinuous_preservesInjectiveObjects :
    ((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace T E h X))
      (BigFppfSpaceOver.topology T X)).PreservesInjectiveObjects := by
  have : ∀ P : (Over (etaleSpace T E h X))ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u.op.HasPointwiseLeftKanExtension P :=
    fun P ↦ Functor.hasPointwiseLeftKanExtension_of_isEquivalence _ P
  exact Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous _ _ _

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- **The higher direct images along `ε_X` of an abelian sheaf with vanishing higher cohomology
on affine objects vanish.** -/
theorem isZero_rightDerived_fppfToBigEtale_sheafPushforward_of_isZero_H'
    (G : Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1})
    (hG : ∀ U : Over X, BigFppfSpaceOver.IsAffineSchemeOver T X U → ∀ p : ℕ, 0 < p →
      IsZero (Sheaf.H' G p U))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace T E h X))
      (BigFppfSpaceOver.topology T X)).rightDerived p).obj G) := by
  refine Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u p G (fun V ↦ ?_)
  refine ⟨epsilonAffinePresieve E h V, generate_epsilonAffinePresieve_mem E h V,
    fun W g hW ↦ ?_⟩
  exact (hG _ hW p hp).of_iso
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
      (BigFppfSpaceOver.topology T X) G p _).symm

end AlgebraicGeometry.BigFppfSpaceSite

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}}

/-- `Ext` for abelian sheaves on `(Spaces/X)_étale`, at the universe of the morphisms of the
site. -/
theorem hasExt_bigEtaleSpaceOver (E : BigEtaleSpaceSite S) (Y : E.Spaces) :
    HasExt.{u + 1} (Sheaf (E.bigEtaleTopology Y) AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse _

end AlgebraicGeometry.BigEtaleSpaceSite

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces}
  (E : BigEtaleSpaceSite S) (h : T.schemeSite = E.fppfSite)

attribute [local instance] hasExt_bigFppfSpaceOver BigEtaleSpaceSite.hasExt_bigEtaleSpaceOver in
/-- For a complex `𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃` of quasi-coherent `𝒪_X`-modules, the homology `𝓗_et` of
`π_X^*𝓕₁ ⟶ π_X^*𝓕₂ ⟶ π_X^*𝓕₃` has `H^p((Spaces/X)_étale / U, 𝓗_et) = 0` for `p > 0` and every
affine object `U`. -/
theorem isZero_H'_homology_etale
    (Q : ShortComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)))
    [Q.X₁.IsQuasicoherentOnSite] [Q.X₂.IsQuasicoherentOnSite] [Q.X₃.IsQuasicoherentOnSite]
    (U : Over (etaleSpace T E h X))
    (hU : BigEtaleSpaceSite.IsAffineSchemeOver E (etaleSpace T E h X) U) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj
      (Q.map (toEtaleSpaceModules T E h X ⋙
        (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
          (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos)).homology) p U) := by
  have := fppfToBigEtale_sheafPushforwardContinuous_preservesInjectiveObjects E h (X := X)
  obtain ⟨e⟩ := nonempty_homology_pullback_iso E h Q
  let G := (SheafOfModules.toSheaf _).obj
    (Q.map (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos).homology
  let e' : (SheafOfModules.toSheaf _).obj
      (Q.map (toEtaleSpaceModules T E h X ⋙
        (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
          (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos)).homology ≅
      ((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace T E h X))
        (BigFppfSpaceOver.topology T X)).obj G :=
    (SheafOfModules.toSheaf _).mapIso e
  have h₀ : IsZero (Sheaf.H' G p
      ((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u.obj U)) :=
    isZero_H'_homology_pullback Q _ (isAffineSchemeOver_fppfToBigEtale_obj E h hU) p hp
  have h₁ := h₀.of_iso (Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso
    (E.bigEtaleTopology (etaleSpace T E h X)) (BigFppfSpaceOver.topology T X)
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u G U p
    (fun q hq _ ↦ isZero_rightDerived_fppfToBigEtale_sheafPushforward_of_isZero_H' E h G
      (fun V hV q hq ↦ isZero_H'_homology_pullback Q V hV q hq) q hq))
  exact h₁.of_iso (((Sheaf.cohomologyPresheafFunctor _ p).mapIso e').app (op U))

attribute [local instance] hasExt_bigFppfSpaceOver BigEtaleSpaceSite.hasExt_bigEtaleSpaceOver in
/-- **Stacks 0DGQ.** Let `X` be an algebraic space and `𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃` a complex of
quasi-coherent `𝒪_X`-modules. Let `𝓗_et` be the homology of
`π_X^*𝓕₁ ⟶ π_X^*𝓕₂ ⟶ π_X^*𝓕₃` on `(Spaces/X)_étale` and `𝓗_fppf` that of
`a_X^*𝓕₁ ⟶ a_X^*𝓕₂ ⟶ a_X^*𝓕₃` on `(Spaces/X)_fppf`. Then `𝓗_et ≅ ε_{X,*}𝓗_fppf`, and
`H^p_et(U, 𝓗_et) = 0` and `H^p_fppf(U, 𝓗_fppf) = 0` for `p > 0` and every affine object `U`. -/
theorem homology_pullback_of_quasicoherent
    (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S) (h : T.schemeSite = E.fppfSite)
    (X : T.Spaces)
    (Q : ShortComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)))
    [Q.X₁.IsQuasicoherentOnSite] [Q.X₂.IsQuasicoherentOnSite] [Q.X₃.IsQuasicoherentOnSite] :
    Nonempty ((Q.map (toEtaleSpaceModules T E h X ⋙
        (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
          (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos)).homology ≅
      (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.obj
        (Q.map (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos).homology) ∧
    (∀ U : Over (etaleSpace T E h X),
      BigEtaleSpaceSite.IsAffineSchemeOver E (etaleSpace T E h X) U → ∀ p : ℕ, 0 < p →
        IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj
          (Q.map (toEtaleSpaceModules T E h X ⋙
            (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
              (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos)).homology) p U)) ∧
    (∀ U : Over X, BigFppfSpaceOver.IsAffineSchemeOver T X U → ∀ p : ℕ, 0 < p →
      IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj
        (Q.map (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos).homology)
        p U)) :=
  ⟨nonempty_homology_pullback_iso E h Q,
    fun U hU p hp ↦ isZero_H'_homology_etale E h Q U hU p hp,
    fun U hU p hp ↦ isZero_H'_homology_pullback Q U hU p hp⟩

end AlgebraicGeometry.BigFppfSpaceSite

end
