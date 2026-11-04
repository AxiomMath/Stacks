module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfQuasicoherentCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleRestrictModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedComparisonAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedComparisonEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalenceAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LocallyQuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity

/-!
# Quasi-coherent modules on a category fibred in groupoids (Stacks 06WK)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `F` a presheaf of modules over
its structure sheaf. Stacks 06WK says that `F` is quasi-coherent (Stacks 06WG) if and only if

1. `F` is locally quasi-coherent (Stacks 06WJ), and
2. for every arrow `φ : x ⟶ y` of `𝒳` lying over a morphism of schemes `f : U ⟶ V`, the comparison
   map `c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of Stacks 06WC is an isomorphism.

Both sides are read on the affine subcategory `𝒳_{affine}` of Stacks 0H0A, through the
*cartesian* condition: `F` is cartesian along an arrow `y ⟶ y'` when the base-change map
`𝒪(y) ⊗_{𝒪(y')} F(y') ⟶ F(y)` of its restriction map is bijective.

* A module quasi-coherent on `𝒳` is cartesian along every arrow of `𝒳_{affine}`, by the content
  of Descent, Proposition 03DX in the form of Stacks 0H0E; conversely an étale sheaf cartesian
  along every arrow of `𝒳_{affine}` is quasi-coherent on the inherited étale site, by Stacks 0H0C
  and 0H0E, hence quasi-coherent on `𝒳` by Stacks 0EM8.
* An étale sheaf cartesian along the arrows of `𝒳_{affine}` lying over étale morphisms is locally
  quasi-coherent, by Stacks 0H0F.
* Between affine objects, the comparison map `c_φ` is an isomorphism exactly when `F` is cartesian
  along `φ`, by
  `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparison_iff_bijective_restrictionBaseChange`.
  For a general arrow, cover the source by affine opens mapping into affine opens of the target:
  the comparison maps along the arrows lying over the open immersions are isomorphisms
  (Stacks 075D (2)), the composition law of Stacks 075D (1) reduces `c_φ` over each member of
  the cover to the comparison map between affine objects, and a morphism of sheaves which is an
  isomorphism over a cover is one.

## Main definitions

* `AlgebraicGeometry.Stack.IsCartesianOnAffineObjects`: the cartesian condition on `𝒳_{affine}`.

## Main results

* `AlgebraicGeometry.Stack.isCartesianOnAffineObjects_of_isQuasicoherentFppf` and
  `AlgebraicGeometry.Stack.isQuasicoherentFppf_of_isCartesianOnAffineObjects`: quasi-coherence on
  `𝒳` is the cartesian condition on `𝒳_{affine}`, for an étale sheaf.
* `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparison_of_isCartesianOnAffineObjects`:
  for a locally quasi-coherent module cartesian on `𝒳_{affine}`, every `c_φ` is an isomorphism.
* `Stack.isQuasicoherentFppf_iff_isLocallyQuasicoherent_and_isIso_sheafifiedRestrictComparison`:
  **Stacks 06WK**, in the namespace `AlgebraicGeometry`.

## Implementation notes

The comparison map of clause (2) is `AlgebraicGeometry.Stack.sheafifiedRestrictComparison`, the
map of sheaves of modules adjunct, under sheafification, to the comparison of presheaves of
modules of Stacks 06WC: the pullback `f_{small}^*` of sheaves of modules is the sheafification of
the pullback of presheaves of modules. It is defined using the étale sheaf condition of `F|_{U_ét}`
which local quasi-coherence provides. The modules have sections in the universe of the schemes,
which is the universe in which the pullback of Stacks 06WC exists.

## References

* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
* [Stacks Project, Tag 0H0F](https://stacks.math.columbia.edu/tag/0H0F)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The index type of the cover of a scheme `S` by affine opens mapping, under a morphism
`g : S ⟶ T`, into affine opens of `T`. -/
abbrev AffineOpensOver {T : Scheme.{u}} (g : S ⟶ T) : Type (u + 1) :=
  ULift.{u + 1} (Σ V : S.affineOpens, {U : T.affineOpens // V.1 ≤ g ⁻¹ᵁ U.1})

/-- **The affine opens of `S` mapping into affine opens of `T` cover the final object of the
small étale site of `S`.** They are open immersions and jointly surjective, every point of `S`
having an affine open neighbourhood inside the preimage of an affine open neighbourhood of its
image. -/
theorem coversTop_openSubObj_affineOpensOver {T : Scheme.{u}} (g : S ⟶ T) :
    (topology B S hS).CoversTop
      (fun i : AffineOpensOver S g => openSubObj B S hS (final B S hS) i.down.1.1) := by
  let D : PreZeroHypercover.{u + 1} (final B S hS) :=
    { I₀ := AffineOpensOver S g
      X := fun i => openSubObj B S hS (final B S hS) i.down.1.1
      f := fun i => openSubHom B S hS (final B S hS) i.down.1.1 }
  have hD : D.sieve₀ ∈ topology B S hS (final B S hS) := by
    refine Precoverage.generate_mem_toGrothendieck
      (presieve₀_mem_precoverage_of_isOpenImmersion B S hS D (fun x => ?_)
        (fun i => inferInstanceAs (IsOpenImmersion (i.down.1.1.ι))))
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := T) (x := g.base x) (U := (⊤ : T.Opens)) trivial
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (X := S) (x := x) (U := g ⁻¹ᵁ U) hxU
    exact ⟨⟨⟨⟨V, hV⟩, ⟨U, hU⟩, hVU⟩⟩, ⟨⟨x, hxV⟩, rfl⟩⟩
  refine (GrothendieckTopology.coversTop_iff_of_isTerminal _ (final B S hS)
    (finalIsTerminal B S hS) _).2 ?_
  exact (topology B S hS).superset_covering (Sieve.ofArrows_le_ofObjects D.X D.f) hD

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- A presheaf of modules on `𝒳` is *cartesian along the arrows of the affine subcategory* when
for every arrow `y ⟶ y'` of `𝒳` between objects lying over affine schemes the base-change map
`𝒪(y) ⊗_{𝒪(y')} F(y') ⟶ F(y)` of its restriction map is bijective. -/
abbrev IsCartesianOnAffineObjects
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) : Prop :=
  ∀ ⦃y y' : AffineCategory B S hS p⦄ (f : y ⟶ y'),
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F f.hom.op)

/-- **A quasi-coherent module on `𝒳` is cartesian along the arrows of the affine subcategory.**
Its restriction to `𝒳_{affine, fppf}` is quasi-coherent there (Stacks 0H0C), and a quasi-coherent
module on `𝒳_{affine, fppf}` is cartesian (Stacks 0H0E). -/
theorem isCartesianOnAffineObjects_of_isQuasicoherentFppf
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : IsQuasicoherentFppf B S hS p hp F) : IsCartesianOnAffineObjects B S hS p hp F := by
  obtain ⟨hs, hq⟩ := hF
  let M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf) := ⟨F, hs⟩
  have := AffineCategory.isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  have := AffineCategory.isCocontinuous_inclusion_siteKind B S hS p hp .fppf
  have hres := Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite
    (J := associatedAffineTopology B S hS p
      (BigAffineFppf.siteKindTopology B S hS .fppf))
    (K := BigFppfOver.associatedTopology B S hS p .fppf)
    (AffineCategory.inclusion B S hS p) (FibredSite.ringStructureSheafCore B S hS p hp .fppf)
    M hq
  intro y y' f
  have := AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite
    B S hS p _ rfl hp .fppf _ _ hres f.op
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

/-- Cartesianness along an arrow of the affine subcategory, as `IsIso` of the base-change map. -/
private theorem isIso_restrictionBaseChange_of_isCartesianOnAffineObjects
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hc : IsCartesianOnAffineObjects B S hS p hp F) {y y' : AffineCategory B S hS p}
    (f : y ⟶ y') :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F f.hom.op) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (hc f)

/-- **An étale sheaf cartesian along the arrows of the affine subcategory is quasi-coherent on
`𝒳`.** Its restriction to `𝒳_{affine, ét}` is cartesian, hence quasi-coherent (Stacks 0H0E), so
it is quasi-coherent on the inherited étale site (Stacks 0H0C), hence on `𝒳` (Stacks 0EM8). -/
theorem isQuasicoherentFppf_of_isCartesianOnAffineObjects
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hs : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf)
    (hc : IsCartesianOnAffineObjects B S hS p hp F) : IsQuasicoherentFppf B S hS p hp F := by
  let M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .etale) := ⟨F, hs⟩
  have := AffineCategory.isDenseSubsite_inclusion_siteKind B S hS p hp .etale
  have hcart : ∀ {X Y : (AffineCategory B S hS p)ᵒᵖ} (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (AffineCategory.toScheme B S hS p).op ⋙ Scheme.Γ)
        ((Stacks.DenseSubsiteModules.moduleRestriction
          (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .etale))
          (BigFppfOver.associatedTopology B S hS p .etale) (AffineCategory.inclusion B S hS p)
          (FibredSite.ringStructureSheafCore B S hS p hp .etale)).obj M).val f) :=
    fun f => isIso_restrictionBaseChange_of_isCartesianOnAffineObjects B S hS p hp F hc f.unop
  have hq : M.IsQuasicoherentOnSite := by
    refine AffineCategory.isQuasicoherentOnSite_of_moduleRestriction B S hS p
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .etale))
      (BigFppfOver.associatedTopology B S hS p .etale) hp _ _ ?_
    exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso
      (AffineCategory.siteKindRingedSite B S hS p hp .etale) _ (fun _ _ f => hcart f.op)
  exact FibredSite.isQuasicoherentClause_fppf_of_isQuasicoherentClause B S hS p hp .etale
    (FibredSite.isSheafFppfOfQuasicoherentOnSite_etale B S hS p hp) ⟨hs, hq⟩

/-- **An étale sheaf cartesian along the arrows of the affine subcategory is locally
quasi-coherent**, by Stacks 0H0F: it is cartesian along the arrows lying over étale morphisms of
affine schemes, so its restriction to the small étale site below every object is cartesian
between affine objects, hence quasi-coherent. -/
theorem isLocallyQuasicoherent_of_isCartesianOnAffineObjects
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hs : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf)
    (hc : IsCartesianOnAffineObjects B S hS p hp F) :
    IsLocallyQuasicoherent B E h S hS p hp F := by
  let G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)) := ⟨F, hs⟩
  have hF : IsEtaleCartesian B S hS p
      ((PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS p) _).obj G.val) :=
    fun _ _ f _ => isIso_restrictionBaseChange_of_isCartesianOnAffineObjects B S hS p hp F hc f
  refine ⟨hs, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F hs, ?_⟩⟩
  exact SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines E _ _ _
    (isCartesianOnAffines_restrictModuleToSmallEtale B E h S hS p hp G _ (Iso.refl _) hF x)

/-! ### Lifts of small étale objects -/

/-- The morphism of schemes below the canonical arrow from the lift of a small étale object `T`
over the scheme below `x` is, up to the identification `AlgebraicGeometry.Stack.etaleIndexIso`,
the structure morphism of `T`. -/
theorem toScheme_map_smallEtaleLiftHom (x : 𝒳)
    (T : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    (BigFppfOver.toScheme B S hS).map (p.map (smallEtaleLiftHom B E h S hS p hp x T)) =
      (etaleIndexIso B E h S hS p hp x T).hom ≫ E.inclusion.map T.obj.hom := by
  let := isEquivalence_overPost B S hS p hp x
  have hw := Over.w
    ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.hom.app
      ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).obj T))
  exact (congrArg B.inclusion.map hw).symm.trans (B.inclusion.map_comp _ _)

/-- The canonical arrow from the lift of a small étale object lies over an étale morphism of
schemes. -/
theorem etale_smallEtaleLiftHom (x : 𝒳)
    (T : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    Etale (B.inclusion.map (p.map (smallEtaleLiftHom B E h S hS p hp x T)).left) := by
  have hT : Etale (E.inclusion.map T.obj.hom) := T.property
  show Etale ((BigFppfOver.toScheme B S hS).map (p.map (smallEtaleLiftHom B E h S hS p hp x T)))
  rw [toScheme_map_smallEtaleLiftHom]
  infer_instance

/-- A small étale object maps to the chart of the canonical arrow from its lift. -/
noncomputable def toEtaleChartSmallEtaleLiftHom (x : 𝒳)
    (T : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    T ⟶ etaleChart B E h S hS p (smallEtaleLiftHom B E h S hS p hp x T)
      (etale_smallEtaleLiftHom B E h S hS p hp x T) :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (etaleIndexIso B E h S hS p hp x T).inv)
    (by
      apply ObjectProperty.hom_ext
      change (etaleIndexIso B E h S hS p hp x T).inv ≫
          (BigFppfOver.toScheme B S hS).map (p.map (smallEtaleLiftHom B E h S hS p hp x T)) =
        E.inclusion.map T.obj.hom
      rw [toScheme_map_smallEtaleLiftHom, Iso.inv_hom_id_assoc]))

/-- **The comparison map along a composite, when the comparison along the first arrow is an
isomorphism.** By the composition law of Stacks 075D (1), if `c_ψ` is an isomorphism then
`c_{ψ ≫ φ}` is an isomorphism exactly when the sheafified pullback along `ψ` of `c_φ` is. -/
theorem isIso_sheafifiedPullbackComparison_map_iff {x z z' : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz' : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z').left.1
        (contains_base B E h S hS p z'))
      (restrictModuleToSmallEtale B E h S hS p hp z' (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hψ : IsIso (sheafifiedRestrictComparison B E h S hS p hp F ψ hMz')) :
    IsIso ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) ψ).map
          (sheafifiedRestrictComparison B E h S hS p hp F φ hMz)) ↔
      IsIso (sheafifiedRestrictComparison B E h S hS p hp F (ψ ≫ φ) hMz') := by
  have hcomp := sheafifiedRestrictComparison_comp B E h S hS p hp F ψ φ hMx hMz hMz'
  have hI : IsIso ((sheafifiedPullbackComparisonCompIso B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) ψ φ).hom.app
      (restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx)) :=
    Iso.isIso_hom ((sheafifiedPullbackComparisonCompIso B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) ψ φ).app _)
  refine (isIso_comp_right_iff _
    (sheafifiedRestrictComparison B E h S hS p hp F ψ hMz')).symm.trans ?_
  refine (congrArg IsIso hcomp).to_iff.trans ?_
  exact @isIso_comp_left_iff _ _ _ _ _ _ _ hI

/-- **Factorization through affine charts.** Let `φ : z ⟶ x` lie over `g : W ⟶ U`, and let
`V ⊆ W` and `U' ⊆ U` be affine opens with `g(V) ⊆ U'`. The composite of the canonical arrow from
the lift of `V` with `φ` factors through the canonical arrow from the lift of `U'`, which lies
over an étale morphism, by an arrow between objects lying over affine schemes. -/
theorem exists_comp_eq_smallEtaleLiftHom_comp {x z : 𝒳} (φ : z ⟶ x)
    (i : SmallEtale.AffineOpensOver (p.obj z).left.1 (B.inclusion.map (p.map φ).left)) :
    ∃ (w' : 𝒳) (φi : smallEtaleLiftObject B E h S hS p hp z
        (SmallEtale.openSubObj E _ _ (SmallEtale.final E _ _) i.down.1.1) ⟶ w') (κ : w' ⟶ x),
      φi ≫ κ = smallEtaleLiftHom B E h S hS p hp z
          (SmallEtale.openSubObj E _ _ (SmallEtale.final E _ _) i.down.1.1) ≫ φ ∧
        Etale (B.inclusion.map (p.map κ).left) ∧
        AlgebraicGeometry.IsAffine (p.obj w').left.1 ∧
        AlgebraicGeometry.IsAffine (p.obj (smallEtaleLiftObject B E h S hS p hp z
          (SmallEtale.openSubObj E _ _ (SmallEtale.final E _ _) i.down.1.1))).left.1 := by
  obtain ⟨⟨⟨V, hV⟩, ⟨U', hU'⟩, hVU⟩⟩ := i
  let g := B.inclusion.map (p.map φ).left
  let f := smallEtaleBaseMorphism B E h S hS p φ
  let X := SmallEtale.openSubObj E _ _ (SmallEtale.final E (p.obj z).left.1
    (contains_base B E h S hS p z)) V
  let W'' := SmallEtale.openSubObj E _ _ (SmallEtale.final E (p.obj x).left.1
    (contains_base B E h S hS p x)) U'
  obtain ⟨φ', hφ', -⟩ := exists_restrictionComparisonLift B E h S hS p hp φ W''
  let k : X.obj.left ⟶ W''.obj.left := ObjectProperty.homMk (g.resLE U' V hVU)
  have hk : k ≫ W''.obj.hom = X.obj.hom ≫ f := by
    apply ObjectProperty.hom_ext
    show g.resLE U' V hVU ≫ U'.ι ≫ 𝟙 _ = (V.ι ≫ 𝟙 _) ≫ g
    rw [Category.comp_id, Category.comp_id, Scheme.Hom.resLE_comp_ι]
  let j := smallEtaleBaseChangeLift E f W'' X k hk
  refine ⟨smallEtaleLiftObject B E h S hS p hp x W'',
    (etaleIndex B E h S hS p hp z).map j ≫ φ', smallEtaleLiftHom B E h S hS p hp x W'',
    ?_, etale_smallEtaleLiftHom B E h S hS p hp x W'', ?_, ?_⟩
  · let := isEquivalence_overPost B S hS p hp z
    rw [Category.assoc, hφ', ← Category.assoc]
    congr 1
    exact Over.w ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv.map
      ((smallEtaleInclusion B E h (p.obj z).left.1 (contains_base B E h S hS p z)).map j))
  · have : AlgebraicGeometry.IsAffine (U' : Scheme.{u}) := hU'
    exact isAffine_etaleIndex_obj B E h S hS p hp x W'' (inferInstanceAs
      (AlgebraicGeometry.IsAffine (U' : Scheme.{u})))
  · have : AlgebraicGeometry.IsAffine (V : Scheme.{u}) := hV
    exact isAffine_etaleIndex_obj B E h S hS p hp z X (inferInstanceAs
      (AlgebraicGeometry.IsAffine (V : Scheme.{u})))

/-- **For a locally quasi-coherent module cartesian along the arrows of the affine subcategory,
every comparison map `c_φ` of Stacks 06WC is an isomorphism.** Cover the scheme `W` below the
source of `φ : z ⟶ x` by affine opens `V` mapping into affine opens `U'` of the scheme below `x`,
and let `ι_V` and `κ_{U'}` be the canonical arrows from the lifts of `V` and `U'`; then
`ι_V ≫ φ = φ_V ≫ κ_{U'}` with `φ_V` an arrow of the affine subcategory. The comparison maps
along `ι_V` and `κ_{U'}` are isomorphisms, the arrows lying over étale morphisms (Stacks 075D (2)),
and the one along `φ_V` is, `F` being cartesian along it, so by the composition law of
Stacks 075D (1) the pullback of `c_φ` to each `V` is an isomorphism, hence so is `c_φ`. -/
theorem isIso_sheafifiedRestrictComparison_of_isCartesianOnAffineObjects
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hc : IsCartesianOnAffineObjects B S hS p hp F) {x z : 𝒳} (φ : z ⟶ x) :
    IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 z).1) := by
  let I := SmallEtale.AffineOpensOver (p.obj z).left.1 (B.inclusion.map (p.map φ).left)
  let X : I → SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z) := fun i =>
    SmallEtale.openSubObj E _ _ (SmallEtale.final E (p.obj z).left.1
      (contains_base B E h S hS p z)) i.down.1.1
  refine isIso_of_isIso_sheafifiedPullbackComparison_map_of_coversTop B E h S hS p hp
    (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 z).1) X
    (SmallEtale.coversTop_openSubObj_affineOpensOver E _ _ (B.inclusion.map (p.map φ).left))
    (fun i => smallEtaleLiftObject B E h S hS p hp z (X i))
    (fun i => smallEtaleLiftHom B E h S hS p hp z (X i))
    (fun i => etale_smallEtaleLiftHom B E h S hS p hp z (X i))
    (fun i => ⟨toEtaleChartSmallEtaleLiftHom B E h S hS p hp z (X i)⟩) (fun i => ?_)
  rw [isIso_sheafifiedPullbackComparison_map_iff B E h S hS p hp _ φ F (hlqc.2 x).1
    (hlqc.2 z).1 (hlqc.2 _).1 (isIso_sheafifiedRestrictComparison_of_etale B E h S hS p hp _
      (etale_smallEtaleLiftHom B E h S hS p hp z _) F (hlqc.2 _).1)]
  obtain ⟨w', φi, κ, hfac, hκ, hw', hwi⟩ :=
    exists_comp_eq_smallEtaleLiftHom_comp B E h S hS p hp φ i
  rw [← hfac]
  have hφi : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φi (hlqc.2 _).1) := by
    have := hw'
    have := hwi
    exact (isIso_sheafifiedRestrictComparison_iff_bijective_restrictionBaseChange B E h S hS p hp
      φi F (hlqc.2 w').1 (hlqc.2 _).1 (hlqc.2 w').2 (hlqc.2 _).2).2
        (hc (y := ⟨_, hwi⟩) (y' := ⟨w', hw'⟩) (ObjectProperty.homMk φi))
  rw [← isIso_sheafifiedPullbackComparison_map_iff B E h S hS p hp φi κ F (hlqc.2 x).1
    (hlqc.2 w').1 (hlqc.2 _).1 hφi]
  have := isIso_sheafifiedRestrictComparison_of_etale B E h S hS p hp κ hκ F (hlqc.2 w').1
  infer_instance

/-- **A locally quasi-coherent module all of whose comparison maps are isomorphisms is cartesian
along the arrows of the affine subcategory**: between objects lying over affine schemes, the
comparison map `c_φ` is an isomorphism exactly when `F` is cartesian along `φ`. -/
theorem isCartesianOnAffineObjects_of_isIso_sheafifiedRestrictComparison
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hiso : ∀ {x y : 𝒳} (φ : x ⟶ y),
      IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 x).1)) :
    IsCartesianOnAffineObjects B S hS p hp F := by
  intro y y' f
  have : AlgebraicGeometry.IsAffine (p.obj y.obj).left.1 := y.property
  have : AlgebraicGeometry.IsAffine (p.obj y'.obj).left.1 := y'.property
  exact (isIso_sheafifiedRestrictComparison_iff_bijective_restrictionBaseChange B E h S hS p hp
    f.hom F (hlqc.2 y'.obj).1 (hlqc.2 y.obj).1 (hlqc.2 y'.obj).2 (hlqc.2 y.obj).2).1
      (hiso f.hom)

/-- **Stacks 06WK.** A presheaf of modules `F` on a category fibred in groupoids `𝒳` over
`(Sch/S)_{fppf}` is quasi-coherent (Stacks 06WG) if and only if

1. `F` is locally quasi-coherent (Stacks 06WJ), and
2. for every arrow `φ : x ⟶ y` of `𝒳` the comparison map
   `c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of Stacks 06WC, read on sheaves of modules on the
   small étale site of the scheme `U` below `x`, is an isomorphism. -/
@[stacks 06WK]
theorem isQuasicoherentFppf_iff_isLocallyQuasicoherent_and_isIso_sheafifiedRestrictComparison
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    IsQuasicoherentFppf B S hS p hp F ↔
      ∃ hlqc : IsLocallyQuasicoherent B E h S hS p hp F,
        ∀ {x y : 𝒳} (φ : x ⟶ y),
          IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 x).1) := by
  constructor
  · intro hF
    have hc := isCartesianOnAffineObjects_of_isQuasicoherentFppf B S hS p hp F hF
    have hlqc := isLocallyQuasicoherent_of_isCartesianOnAffineObjects B E h S hS p hp F
      (isSheaf_etale_of_isQuasicoherentFppf B S hS p hp F hF) hc
    exact ⟨hlqc, fun φ =>
      isIso_sheafifiedRestrictComparison_of_isCartesianOnAffineObjects B E h S hS p hp F hlqc hc φ⟩
  · rintro ⟨hlqc, hiso⟩
    exact isQuasicoherentFppf_of_isCartesianOnAffineObjects B S hS p hp F hlqc.1
      (isCartesianOnAffineObjects_of_isIso_sheafifiedRestrictComparison B E h S hS p hp F hlqc
        hiso)

end AlgebraicGeometry.Stack

end
