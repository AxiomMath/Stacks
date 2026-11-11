module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.ShortExactOnInjectivesTriangleToTarget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RelativeMayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSectionsWithSupportEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsWithSupportEtaleExcision
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportLeftExact

/-!
# The distinguished triangle of cohomology with support in a closed subspace

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` and let `U ⊆ X` be
the open complement of `Z`. Stacks 0A4L defines the derived functor
`RΓ_Z(X, -) : D(X_étale) ⟶ D(Ab)` of the sections with support `Γ_Z(X, -)` and the cohomology
groups with support `H^q_Z(X, -)`, and shows that for every `K` in `D(X_étale)` there is a
distinguished triangle

`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`

in `D(Ab)`, hence a long exact cohomology sequence
`… ⟶ H^i_Z(X, K) ⟶ H^i(X, K) ⟶ H^i(U, K) ⟶ H^{i+1}_Z(X, K) ⟶ …`. This file proves all of it.

## Main definitions

* `AlgebraicGeometry.Space.sectionsOnComplement` and
  `AlgebraicGeometry.Space.restrictionToComplement`: the functor `F ↦ Γ(U, F|_U)` and the
  restriction map `Γ(X, F) ⟶ Γ(U, F|_U)`.
* `AlgebraicGeometry.Space.derivedGlobalSectionsWithSupport`,
  `AlgebraicGeometry.Space.derivedSmallEtaleGlobalSections` and
  `AlgebraicGeometry.Space.derivedSectionsOnComplement`: `RΓ_Z(X, -)`, `RΓ(X, -)` and
  `RΓ(U, -)` on the unbounded derived category `D(X_étale)`.
* `AlgebraicGeometry.Space.derivedCohomologyWithSupport`: `H^q_Z(X, K)` for `K` in `D(X_étale)`.
* `AlgebraicGeometry.Space.derivedCohomologyWithSupportSingleIso`: for a sheaf `F`, the
  cohomology of `RΓ_Z(X, F)` is `R^q Γ_Z(X, F)`.

## Main results

* `AlgebraicGeometry.Space.shortExact_sectionsWithSupport_restrictionToComplement`: for an
  injective abelian sheaf `I`, `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0` is short exact.
* `AlgebraicGeometry.Space.exists_distTriang_derivedGlobalSectionsWithSupport`: the
  distinguished triangle and the long exact sequence.

## Implementation notes

The restriction `I(X) ⟶ I(U)` of an injective sheaf is surjective by Cohomology on Sites,
Lemma 093X, which needs `U ⟶ X` to be a monomorphism of a site. The small étale site of `X` has
neither `X` nor `U` among its objects, so the argument is run on the spaces-étale site of
Stacks 03G0, which has the same topos by Stacks 03G1 and in which `X` is the terminal object and
`U` is an object: global sections over `X` are the sections at the terminal object
(`AlgebraicGeometry.Space.globalSectionsTerminalIso`) and global sections of `F|_U` are the
sections at `U` (`AlgebraicGeometry.Space.etaleObjectSectionsIso`). The kernel of the
restriction is identified with `Γ_Z(X, F)` on étale charts: a chart whose points miss `|Z|`
factors through `U`, so a global section restricting to zero on `U` restricts to zero on every
such chart, which is the condition that its support lies in `|Z|`.

The triangle itself is then the distinguished triangle of a short complex of functors which is
short exact at injective objects,
`Stacks.ShortExactOnInjectivesToTarget.exists_derivedTriangle_of_shortExactOnInjectives`, and the
long exact sequence is Mathlib's homology sequence of a distinguished triangle.

## References

* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 093X](https://stacks.math.columbia.edu/tag/093X)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Global sections as sections at the terminal object of the spaces-étale site -/

section Terminal

variable (X : AlgebraicSpaces B S hS)

/-- **Global sections are the sections at the terminal spaces-étale object.**  For an abelian
sheaf `F` on `X_étale`, the global sections of `F` are the sections at `X` itself of the
corresponding sheaf on the spaces-étale site of Stacks 03G0, naturally in `F`. -/
def globalSectionsTerminalIso :
    (spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).inv ⋙
        (sheafSections (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1}).obj
          (op (SpacesEtale.idObj B S hS X)) ≅
      Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft (spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).inv
      (ΓTerminalNatIso B S hS X) ≪≫
    Functor.isoWhiskerRight
      (spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).asEquivalence.counitIso
      (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) ≪≫
    (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).leftUnitor

/-- The restriction to an étale chart `V` of the global section corresponding to a section `s`
at the terminal object is the restriction of `s` to `V`, read through the counit of the
equivalence of Stacks 03G1. -/
theorem globalSectionsTerminalIso_hom_app_comp_ΓRes
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
    (V : SmallEtale B S hS X.1) :
    (globalSectionsTerminalIso B S hS X).hom.app F ≫ F.ΓRes (op V) =
      ((spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).inv.obj F).obj.map
          ((SpacesEtale.isTerminal_idObj B S hS X).from
            ((comparisonFunctor B S hS X).obj V)).op ≫
        ((spacesEtaleChartRestriction B S hS X
          (A := AddCommGrpCat.{u + 1})).asEquivalence.counitIso.hom.app F).hom.app (op V) := by
  set G := (spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).inv.obj F
  set φ := (spacesEtaleChartRestriction B S hS X
    (A := AddCommGrpCat.{u + 1})).asEquivalence.counitIso.hom.app F
  have h1 : (ΓTerminalNatIso B S hS X).hom.app G ≫
      ((spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).obj G).ΓRes (op V) =
      (coneChartsSheaf B S hS X G).π.app (op V) :=
    IsLimit.conePointUniqueUpToIso_hom_comp (isLimitConeChartsSheaf B S hS X G)
      (isLimitConeΓSheaf B S hS X G) (op V)
  have h2 : (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).map φ ≫
      F.ΓRes (op V) =
      ((spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).obj G).ΓRes (op V) ≫
        φ.hom.app (op V) :=
    Sheaf.ΓRes_naturality φ (op V)
  have h0 : (globalSectionsTerminalIso B S hS X).hom.app F =
      (ΓTerminalNatIso B S hS X).hom.app G ≫
        (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).map φ ≫ 𝟙 _ :=
    rfl
  rw [h0, Category.comp_id, Category.assoc]
  exact (congrArg (fun m => (ΓTerminalNatIso B S hS X).hom.app G ≫ m) h2).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ.hom.app (op V)) h1))

end Terminal

/-! ### Restriction of global sections to the open complement -/

section Restriction

variable {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)

/-- **Sections over the open complement `U = X ∖ Z`.**  The functor `F ↦ Γ(U, F|_U)` from
abelian sheaves on `X_étale` to abelian groups: restriction to the small étale site of the open
subspace `U`, followed by global sections there. -/
abbrev sectionsOnComplement :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  etaleAbelianRestriction.{u + 1} B S hS (complementHom B S hS i hi)
      (isEtale_complementHom B S hS i hi) ⋙
    Sheaf.Γ (SmallEtale.topology B S hS (complementSpace B S hS i hi).1) AddCommGrpCat.{u + 1}

/-- **The restriction map `Γ(X, F) ⟶ Γ(U, F|_U)`** to the open complement of `Z`, natural in
`F`.  On the spaces-étale site of Stacks 03G0, where `X` is the terminal object and `U` is an
object, it is restriction of sections along `U ⟶ X`. -/
def restrictionToComplement :
    Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⟶
      sectionsOnComplement B S hS i hi :=
  (globalSectionsTerminalIso B S hS X).inv ≫
    Functor.whiskerLeft (spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).inv
      (terminalToEtaleObjectRestriction B S hS (complementHom B S hS i hi)
        (isEtale_complementHom B S hS i hi)) ≫
    (etaleObjectSectionsIso B S hS (complementHom B S hS i hi)
      (isEtale_complementHom B S hS i hi)).hom

/-- An étale chart of `X` whose points all miss `|Z|` factors through the open complement of
`Z`, as a morphism of the spaces-étale site. -/
def chartHomToComplementObj (V : SmallEtale B S hS X.1)
    (hV : Set.range (pointsMap B S hS _ V.obj.hom) ⊆ (Set.range (pointsMap B S hS Z.1 i.hom))ᶜ) :
    (comparisonFunctor B S hS X).obj V ⟶ complementObj B S hS i hi :=
  have hle : Subfunctor.range V.obj.hom ≤
      openSubspaceOfPoints B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom))ᶜ :=
    fun T' _ hx => Set.Subset.trans
      (range_le_openSubspaceOfPoints_range_pointsMap (B := B) (S := S) (hS := hS)
        V.obj.hom T' hx) hV
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (Subfunctor.lift V.obj.hom hle))
    (ObjectProperty.hom_ext _ (Subfunctor.lift_ι V.obj.hom hle)))

/-- The point-set condition of an étale chart over a chart whose image misses `|Z|`. -/
theorem range_pointsMap_subset_of_imageInOpen {V W : SmallEtale B S hS X.1} (f : W ⟶ V)
    (hf : ImageInOpen B S hS X.1
      (pointsMap B S hS _ V.obj.hom ⁻¹' (Set.range (pointsMap B S hS Z.1 i.hom))ᶜ) f) :
    Set.range (pointsMap B S hS _ W.obj.hom) ⊆ (Set.range (pointsMap B S hS Z.1 i.hom))ᶜ := by
  rintro _ ⟨y, rfl⟩
  have h : pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.obj.hom
      (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W))
        (yoneda.map ((SmallEtale.toOver B S hS X.1).map f)) y) =
      pointsMap B S hS (yoneda.obj W.obj.left) W.obj.hom y :=
    pointsMap_chart_hom B S hS X.1 f y
  have := hf y
  rwa [Set.mem_preimage, h] at this

/-- **The sections supported on `Z` restrict to zero on the open complement.** -/
theorem globalSectionsWithSupportInclusion_comp_restrictionToComplement :
    globalSectionsWithSupportInclusion B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom)) ≫
      restrictionToComplement B S hS i hi = 0 := by
  refine NatTrans.ext (funext fun F => ?_)
  set e := (spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).inv
  set ρ := terminalToEtaleObjectRestriction B S hS (complementHom B S hS i hi)
    (isEtale_complementHom B S hS i hi)
  set ι := (sectionsWithSupportInclusion.{u + 1} B S hS X.1
    (Set.range (pointsMap B S hS Z.1 i.hom))).app F
  have hz : IsZero ((e.obj ((closedSectionsWithSupport.{u + 1} B S hS i).obj F)).obj.obj
      (op (complementObj B S hS i hi))) :=
    isZero_obj_spacesSectionsWithSupportInClosedSubspace B S hS i F _
      (le_of_eq (range_pointsMap_complementHom B S hS i hi))
  have hρ : ρ.app (e.obj ((closedSectionsWithSupport.{u + 1} B S hS i).obj F)) = 0 :=
    hz.eq_of_tgt _ _
  have hn1 := (globalSectionsTerminalIso B S hS X).inv.naturality ι
  have hn2 := ρ.naturality (e.map ι)
  simp only [NatTrans.comp_app, restrictionToComplement, Functor.whiskerLeft_app,
    NatTrans.app_zero]
  change (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).map ι ≫ _ = 0
  rw [reassoc_of% hn1]
  rw [reassoc_of% hn2, hρ]
  simp

/-- **Exactness in the middle.**  A global section of `F` which restricts to zero on the open
complement `U` of `Z` has support in `Z`: it comes from `Γ_Z(X, F)`.  This holds for every
abelian sheaf `F`, injective or not. -/
theorem exists_globalSectionsWithSupport_of_restrictionToComplement_eq_zero
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
    (x : (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).obj F)
    (hx : (restrictionToComplement B S hS i hi).app F x = 0) :
    ∃ y : (closedGlobalSectionsWithSupport B S hS i).obj F,
      globalSectionsWithSupportι B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom)) F y = x := by
  set e := (spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).inv
  set Ψ := globalSectionsTerminalIso B S hS X
  set E := etaleObjectSectionsIso B S hS (complementHom B S hS i hi)
    (isEtale_complementHom B S hS i hi)
  set x' := Ψ.inv.app F x
  have hx' : (e.obj F).obj.map ((SpacesEtale.isTerminal_idObj B S hS X).from
      (complementObj B S hS i hi)).op x' = 0 := by
    have h : E.hom.app F ((e.obj F).obj.map ((SpacesEtale.isTerminal_idObj B S hS X).from
        (complementObj B S hS i hi)).op x') = 0 := hx
    have h2 : E.inv.app F (E.hom.app F ((e.obj F).obj.map
        ((SpacesEtale.isTerminal_idObj B S hS X).from (complementObj B S hS i hi)).op x')) =
        E.inv.app F 0 := congrArg _ h
    rw [map_zero] at h2
    exact (ConcreteCategory.congr_hom (E.hom_inv_id_app F) _).symm.trans h2
  have hxx : Ψ.hom.app F x' = x := ConcreteCategory.congr_hom (Ψ.inv_hom_id_app F) x
  refine exists_globalSectionsWithSupport B S hS X.1 _ F x (fun V => ?_)
  have hTclosed : IsClosed (Set.range (pointsMap B S hS Z.1 i.hom)) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS X.property i.hom hi
  have hopen : IsOpen (pointsMap B S hS _ V.obj.hom ⁻¹'
      (Set.range (pointsMap B S hS Z.1 i.hom))ᶜ) :=
    (continuous_pointsMap B S hS V.obj.hom).isOpen_preimage _ hTclosed.isOpen_compl
  have hmax := largestOpenZeroLocus_maximal B S hS X.1 F V (F.ΓRes (op V) x) ⟨_, hopen⟩ ?_
  · intro y hy
    by_contra hnot
    exact hy (hmax hnot)
  intro W f hf
  have hW := range_pointsMap_subset_of_imageInOpen B S hS i f hf
  have hfac : (SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj W) =
      chartHomToComplementObj B S hS i hi W hW ≫
        (SpacesEtale.isTerminal_idObj B S hS X).from (complementObj B S hS i hi) :=
    (SpacesEtale.isTerminal_idObj B S hS X).hom_ext _ _
  have hres : F.obj.map f.op (F.ΓRes (op V) x) = F.ΓRes (op W) x :=
    ConcreteCategory.congr_hom (F.ΓRes_map f.op) x
  have hA := ConcreteCategory.congr_hom
    (globalSectionsTerminalIso_hom_app_comp_ΓRes B S hS X F W) x'
  have h3 : (e.obj F).obj.map ((SpacesEtale.isTerminal_idObj B S hS X).from
      ((comparisonFunctor B S hS X).obj W)).op x' = 0 := by
    rw [hfac, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hx', map_zero]
  rw [hres, ← hxx]
  refine hA.trans ?_
  exact (congrArg (fun t => ConcreteCategory.hom (((spacesEtaleChartRestriction B S hS X
    (A := AddCommGrpCat.{u + 1})).asEquivalence.counitIso.hom.app F).hom.app (op W)) t) h3).trans
    (map_zero _)

/-- The open complement of `Z` maps to `X` by a monomorphism of the spaces-étale site. -/
instance mono_from_complementObj :
    Mono ((SpacesEtale.isTerminal_idObj B S hS X).from (complementObj B S hS i hi)) := by
  refine (SpacesEtale.toSpaces B S hS X).mono_of_mono_map ?_
  rw [SpacesEtale.toSpaces_map_from_idObj]
  change Mono (complementHom B S hS i hi)
  refine (ObjectProperty.ι _).mono_of_mono_map ?_
  change Mono (openSubspaceOfPoints B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom))ᶜ).ι
  infer_instance

/-- **Restriction of an injective abelian sheaf to the open complement is surjective on global
sections**: an injective abelian sheaf on `X_étale` corresponds to an injective sheaf on the
spaces-étale site, where `U ⟶ X` is a monomorphism of the site (Cohomology on Sites, Lemma
093X). -/
theorem surjective_restrictionToComplement_app
    (I : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) [Injective I] :
    Function.Surjective ((restrictionToComplement B S hS i hi).app I) := by
  set e := (spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).inv
  have : Injective (e.obj I) :=
    Injective.injective_of_adjoint
      (spacesEtaleChartRestriction B S hS X (A := AddCommGrpCat.{u + 1})).asEquivalence.toAdjunction
      I
  have hs := Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective
    (SpacesEtale.topology B S hS X) (e.obj I)
    ((SpacesEtale.isTerminal_idObj B S hS X).from (complementObj B S hS i hi))
  have h1 : Function.Surjective ((globalSectionsTerminalIso B S hS X).inv.app I) :=
    ((forget AddCommGrpCat).mapIso
      ((globalSectionsTerminalIso B S hS X).app I).symm).toEquiv.surjective
  have h3 : Function.Surjective ((etaleObjectSectionsIso B S hS (complementHom B S hS i hi)
      (isEtale_complementHom B S hS i hi)).hom.app I) :=
    ((forget AddCommGrpCat).mapIso ((etaleObjectSectionsIso B S hS (complementHom B S hS i hi)
      (isEtale_complementHom B S hS i hi)).app I)).toEquiv.surjective
  exact h3.comp (hs.comp h1)

/-- **The short exact sequence `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0`** for an injective
abelian sheaf `I` on `X_étale`. -/
theorem shortExact_sectionsWithSupport_restrictionToComplement
    (I : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) [Injective I] :
    (ShortComplex.mk
      ((globalSectionsWithSupportInclusion B S hS X.1
        (Set.range (pointsMap B S hS Z.1 i.hom))).app I)
      ((restrictionToComplement B S hS i hi).app I)
      (NatTrans.congr_app
        (globalSectionsWithSupportInclusion_comp_restrictionToComplement B S hS i hi) I)).ShortExact
    where
  exact := by
    rw [ShortComplex.ab_exact_iff]
    exact fun x hx =>
      exists_globalSectionsWithSupport_of_restrictionToComplement_eq_zero B S hS i hi I x hx
  mono_f := globalSectionsWithSupportι_mono B S hS X.1 _ I
  epi_g := (AddCommGrpCat.epi_iff_surjective _).2
    (surjective_restrictionToComplement_app B S hS i hi I)

end Restriction

/-! ### The derived functors and the distinguished triangle -/

section Derived

open CategoryTheory.Pretriangulated

-- `smallEtaleDerivedCategory` is stated at `HasDerivedCategory.standard`.
attribute [local instance 100000] HasDerivedCategory.standard

variable {X : AlgebraicSpaces B S hS} [HasDerivedCategory AddCommGrpCat.{u + 1}]

/-- Every additive functor from abelian sheaves on `X_étale` to abelian groups, taken degreewise
on the homotopy category and followed by the localization, has a pointwise right derived functor
on the unbounded derived category: K-injective complexes compute it (Stacks 070K), and every
complex has a K-injective resolution (Stacks 079P). -/
instance hasPointwiseRightDerivedFunctor_smallEtaleSections
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})
    [F.Additive] :
    Functor.HasPointwiseRightDerivedFunctor
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS X) (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, _, u + 2, u + 2, u + 2, u + 2}
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B S hS X.1)).1

/-- The total right derived functor `RF : D(X_étale) ⥤ D(Ab)` of an additive functor `F` from
abelian sheaves on `X_étale` to abelian groups, on unbounded derived categories. -/
abbrev smallEtaleSectionsDerived
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})
    [F.Additive] :
    smallEtaleDerivedCategory.{u + 1} B S hS X ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  Functor.totalRightDerived (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS X) (ComplexShape.up ℤ))

/-- The derivation unit of `smallEtaleSectionsDerived`. -/
abbrev smallEtaleSectionsDerivedUnit
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})
    [F.Additive] :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ smallEtaleSectionsDerived B S hS F :=
  Functor.totalRightDerivedUnit (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS X) (ComplexShape.up ℤ))

/-- `smallEtaleSectionsDerived` is a right derived functor, with its unit. -/
instance smallEtaleSectionsDerived_isRightDerivedFunctor
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})
    [F.Additive] :
    (smallEtaleSectionsDerived B S hS F).IsRightDerivedFunctor
      (smallEtaleSectionsDerivedUnit B S hS F)
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS X) (ComplexShape.up ℤ)) := by
  dsimp only [smallEtaleSectionsDerived, smallEtaleSectionsDerivedUnit]
  infer_instance

variable {Z : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)

/-- **The derived functor `RΓ_Z(X, -) : D(X_étale) ⥤ D(Ab)`** of the sections with support in
the closed subspace `Z` (Stacks 0A4L), on unbounded derived categories: the total right derived
functor of the left exact functor `Γ_Z(X, -)`. -/
@[stacks 0A4L "the derived functor RΓ_Z(X, -) : D(X_étale) → D(Ab)"]
abbrev derivedGlobalSectionsWithSupport :
    smallEtaleDerivedCategory.{u + 1} B S hS X ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  smallEtaleSectionsDerived B S hS (closedGlobalSectionsWithSupport B S hS i)

/-- **The derived global sections `RΓ(X, -) : D(X_étale) ⥤ D(Ab)`**, on unbounded derived
categories. -/
abbrev derivedSmallEtaleGlobalSections :
    smallEtaleDerivedCategory.{u + 1} B S hS X ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  smallEtaleSectionsDerived B S hS (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})

/-- **The derived sections over the open complement `RΓ(U, -) : D(X_étale) ⥤ D(Ab)`**, the total
right derived functor of `F ↦ Γ(U, F|_U)`, on unbounded derived categories: the source's
`RΓ(U, K)`, cohomology over `U` of the restriction of `K`. -/
abbrev derivedSectionsOnComplement :
    smallEtaleDerivedCategory.{u + 1} B S hS X ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  smallEtaleSectionsDerived B S hS (sectionsOnComplement B S hS i hi)

/-- **The cohomology with support `H^q_Z(X, K)` of a complex `K` in `D(X_étale)`**: the `q`-th
cohomology group of `RΓ_Z(X, K)`. -/
@[stacks 0A4L "the cohomology with support H^q_Z(X, K) of a complex K in D(X_étale)"]
abbrev derivedCohomologyWithSupport (K : smallEtaleDerivedCategory.{u + 1} B S hS X) (q : ℤ) :
    AddCommGrpCat.{u + 1} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
    ((derivedGlobalSectionsWithSupport B S hS i).obj K)

/-- **`H^q_Z(X, F) = R^q Γ_Z(X, F)`.** For an abelian sheaf `F` on `X_étale` placed in degree
`0`, the `q`-th cohomology group of `RΓ_Z(X, F)` is the `q`-th classical right derived functor
`AlgebraicGeometry.Space.closedCohomologyWithSupport` of `Γ_Z(X, -)` at `F`, naturally in `F`. So
the cohomology with support of a complex extends the cohomology with support of a sheaf. -/
@[stacks 0A4L "H^q_Z(X, F) = R^q Γ_Z(X, F) is the cohomology of RΓ_Z(X, F)"]
def derivedCohomologyWithSupportSingleIso (q : ℕ) :
    DerivedCategory.singleFunctor (abelianSheaves.{u + 1} B S hS X) 0 ⋙
        derivedGlobalSectionsWithSupport B S hS i ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ) ≅
      closedCohomologyWithSupport B S hS i q :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (closedGlobalSectionsWithSupport B S hS i) (derivedGlobalSectionsWithSupport B S hS i)
    (smallEtaleSectionsDerivedUnit B S hS (closedGlobalSectionsWithSupport B S hS i))
    (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B S hS X.1) q

/-- **The distinguished triangle `RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`** of
Stacks 0A4L, with its long exact cohomology sequence.

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over `S` and let `U` be the open
complement of `Z`.  The inclusion `Γ_Z(X, -) ⟶ Γ(X, -)` and the restriction
`Γ(X, -) ⟶ Γ(U, (-)|_U)` descend to maps `rf : RΓ_Z(X, -) ⟶ RΓ(X, -)` and
`rg : RΓ(X, -) ⟶ RΓ(U, -)` of derived functors on the unbounded derived category `D(X_étale)`
(pinned down as the derived maps by their composites with the derivation units), and there is
a connecting map `δ : RΓ(U, -) ⟶ RΓ_Z(X, -)[1]` such that for every `K` in `D(X_étale)`

`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`

is a distinguished triangle in `D(Ab)`, and consequently the cohomology sequence

`… ⟶ H^i_Z(X, K) ⟶ H^i(X, K) ⟶ H^i(U, K) ⟶ H^{i+1}_Z(X, K) ⟶ …`

is exact, every six-term window of it being exact.

The source's argument is the proof: for an injective abelian sheaf `I` the restriction
`I(X) ⟶ I(U)` is surjective (Cohomology on Sites, Lemma 093X) with kernel `Γ_Z(X, I)`, so the
three functors applied to a K-injective resolution with injective terms give a short exact
sequence of complexes. -/
@[stacks 0A4L "the distinguished triangle RΓ_Z(X, K) → RΓ(X, K) → RΓ(U, K) → RΓ_Z(X, K)[1] and \
the long exact sequence of cohomology with support, for every K in D(X_étale)"]
theorem exists_distTriang_derivedGlobalSectionsWithSupport :
    ∃ (rf : derivedGlobalSectionsWithSupport B S hS i ⟶ derivedSmallEtaleGlobalSections B S hS)
      (rg : derivedSmallEtaleGlobalSections B S hS ⟶ derivedSectionsOnComplement B S hS i hi)
      (δ : derivedSectionsOnComplement B S hS i hi ⟶
        derivedGlobalSectionsWithSupport B S hS i ⋙
          shiftFunctor (DerivedCategory AddCommGrpCat.{u + 1}) (1 : ℤ)),
      Functor.whiskerRight (NatTrans.mapHomotopyCategory
            (globalSectionsWithSupportInclusion B S hS X.1
              (Set.range (pointsMap B S hS Z.1 i.hom))) (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫
          smallEtaleSectionsDerivedUnit B S hS
            (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) =
        smallEtaleSectionsDerivedUnit B S hS (closedGlobalSectionsWithSupport B S hS i) ≫
          Functor.whiskerLeft DerivedCategory.Qh rf ∧
      Functor.whiskerRight (NatTrans.mapHomotopyCategory
            (restrictionToComplement B S hS i hi) (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
          smallEtaleSectionsDerivedUnit B S hS (sectionsOnComplement B S hS i hi) =
        smallEtaleSectionsDerivedUnit B S hS
            (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) ≫
          Functor.whiskerLeft DerivedCategory.Qh rg ∧
      ∀ K, Triangle.mk (rf.app K) (rg.app K) (δ.app K) ∈
          distTriang (DerivedCategory AddCommGrpCat.{u + 1}) ∧
        ∀ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁),
          (Functor.homologySequenceComposableArrows₅
            (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0)
            (Triangle.mk (rf.app K) (rg.app K) (δ.app K)) n₀ n₁ h).Exact := by
  have := isGrothendieckAbelian_smallEtaleAbelianSheaf B S hS X.1
  obtain ⟨rf, rg, δ, hf, hg, hT⟩ :=
    Stacks.ShortExactOnInjectivesToTarget.exists_derivedTriangle_of_shortExactOnInjectives.{u + 1}
      (abelianSheaves.{u + 1} B S hS X) AddCommGrpCat.{u + 1}
      (closedGlobalSectionsWithSupport B S hS i)
      (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
      (sectionsOnComplement B S hS i hi)
      (globalSectionsWithSupportInclusion B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom)))
      (restrictionToComplement B S hS i hi)
      (globalSectionsWithSupportInclusion_comp_restrictionToComplement B S hS i hi)
      (fun I _ => shortExact_sectionsWithSupport_restrictionToComplement B S hS i hi I)
      (derivedGlobalSectionsWithSupport B S hS i) (derivedSmallEtaleGlobalSections B S hS)
      (derivedSectionsOnComplement B S hS i hi)
      (smallEtaleSectionsDerivedUnit B S hS (closedGlobalSectionsWithSupport B S hS i))
      (smallEtaleSectionsDerivedUnit B S hS
        (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}))
      (smallEtaleSectionsDerivedUnit B S hS (sectionsOnComplement B S hS i hi))
  exact ⟨rf, rg, δ, hf, hg, fun K => ⟨hT K, fun n₀ n₁ h =>
    Functor.homologySequenceComposableArrows₅_exact
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0) _ (hT K) n₀ n₁ h⟩⟩

end Derived

end AlgebraicGeometry.Space

end
