module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplementChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Auxiliary facts for the Chow reduction of Stacks 08BE

* `AlgebraicGeometry.Space.C1573.openComplementOfClosedSubspace_val`: the open complement of a
  closed subspace built from its points is the subfunctor `AlgebraicGeometry.Space.openComplement`.
* `AlgebraicGeometry.Space.C1573.isIso_fromPreimage_iso_comp`: being an isomorphism over an open
  subfunctor is unchanged by precomposition with an isomorphism.
* `AlgebraicGeometry.Space.C1573.exists_yoneda_iso_of_isImmersion`: the source of an immersion into
  a represented presheaf is represented, by a scheme immersed in the target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The open complement of a closed subspace, built from its points, is the open complement
subfunctor. -/
theorem C1573.openComplementOfClosedSubspace_val (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    (openComplementOfClosedSubspace B S hS X Z).1 = openComplement B S hS Z.1 := by
  have h := (openSubspacesOrderIso B S hS X.1 X.2).injective (a₁ := openComplementOfClosedSubspace
    B S hS X Z) (a₂ := ⟨openComplement B S hS Z.1,
      isOpenSubspace_openComplement B S hS X.2 Z.1 Z.2⟩) (by
    refine TopologicalSpace.Opens.ext ?_
    show subspacePointSet B S hS X.1 (openComplementOfClosedSubspace B S hS X Z).1 =
      Set.range (pointsMap B S hS (openComplement B S hS Z.1).toFunctor
        (openComplement B S hS Z.1).ι)
    rw [subspacePointSet_openComplement, range_pointsMap_ι_openComplement])
  exact congrArg Subtype.val h

variable {B S hS}

/-- **Isomorphisms over an open subfunctor are stable under precomposition with an
isomorphism.** -/
theorem C1573.isIso_fromPreimage_iso_comp {X' X'' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (φ : X'' ⟶ X') [IsIso φ] (g : X' ⟶ X) (V : Subfunctor X)
    (h : IsIso (V.fromPreimage g)) : IsIso (V.fromPreimage (φ ≫ g)) := by
  let k : (V.preimage (φ ≫ g)).toFunctor ⟶ (V.preimage g).toFunctor :=
    Subfunctor.lift ((V.preimage (φ ≫ g)).ι ≫ φ) (by
      rintro U _ ⟨x, rfl⟩
      exact x.2)
  let k' : (V.preimage g).toFunctor ⟶ (V.preimage (φ ≫ g)).toFunctor :=
    Subfunctor.lift ((V.preimage g).ι ≫ inv φ) (by
      rintro U _ ⟨x, rfl⟩
      show (inv φ ≫ φ ≫ g).app U x.1 ∈ V.obj U
      rw [IsIso.inv_hom_id_assoc]
      exact x.2)
  have hk : IsIso k := by
    refine ⟨⟨k', ?_, ?_⟩⟩ <;> ext U x <;> refine Subtype.ext ?_
    · show (φ ≫ inv φ).app U x.1 = x.1
      simp
    · show (inv φ ≫ φ).app U x.1 = x.1
      simp
  have hfac : V.fromPreimage (φ ≫ g) = k ≫ V.fromPreimage g := by
    ext U x
    rfl
  rw [hfac]
  infer_instance

/-- **The source of an immersion into a represented presheaf is represented**, by a scheme
immersed into the target. -/
theorem C1573.exists_yoneda_iso_of_isImmersion {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {P : BigFppfOver B S hS} (i : X' ⟶ yoneda.obj P) (hi : IsImmersion B S hS i) :
    ∃ (Q : BigFppfOver B S hS) (e : yoneda.obj Q ≅ X') (g : Q ⟶ P),
      e.hom ≫ i = yoneda.map g ∧
        _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map g) := by
  obtain ⟨hrep, hP⟩ := hi
  have hpb := hrep.isPullback (𝟙 (yoneda.obj P))
  have : IsIso (hrep.fst (𝟙 (yoneda.obj P))) := hpb.isIso_fst_of_isIso
  exact ⟨hrep.pullback (𝟙 _), asIso (hrep.fst (𝟙 _)), hrep.snd (𝟙 _),
    (hrep.w (𝟙 _)).trans (Category.comp_id _), hP _ _ _ hpb⟩

variable (B S hS)

/-- The kernel of the structure map of the inclusion of a closed subspace is its defining ideal
sheaf. -/
theorem C1573.kerIdeal_structureSharp_ι (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    SheafOfModules.kerIdeal (structureSharp B S hS (ObjectProperty.homMk Z.1.ι :
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)) =
      definingIdealSheaf B S hS X Z := by
  rw [(closedImmersion_quasicoherentIdeal_correspondence B S hS X).2.1 Z,
    ker_pushforwardStructureProjection]
  exact SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun U =>
    SetLike.ext fun a => SheafOfModules.mem_kerIdeal _ U a)

/-- The points of a closed subspace are the complement of the unit locus of its defining ideal
sheaf. -/
theorem C1573.range_pointsMap_ι_eq_compl_idealUnitLocus (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) =
      (idealUnitLocus B S hS X (definingIdealSheaf B S hS X Z))ᶜ := by
  rw [← range_pointsMap_ι_openComplement_eq_idealUnitLocus, range_pointsMap_ι_openComplement,
    compl_compl]

/-- **The closed subspace cut out by a power of the ideal of `Z` has no more points than `Z`.** -/
theorem C1573.range_pointsMap_ι_subset_of_definingIdealSheaf_eq_idealPowerMultiple
    (X : AlgebraicSpaces B S hS) (Z Z' : ClosedSubspaces B S hS X.1) (e : ℕ)
    (h : definingIdealSheaf B S hS X Z' = idealPowerMultiple B S hS X.1 X.2
      (definingIdealSheaf B S hS X Z) e (SheafOfModules.unit _)) :
    Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι) ⊆
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) := by
  simp only [range_pointsMap_ι_eq_compl_idealUnitLocus]
  refine Set.compl_subset_compl.2 ?_
  rintro x ⟨V, hV, hx⟩
  refine ⟨V, ?_, hx⟩
  rw [h]
  have hV' : chartIdeal B S hS X (definingIdealSheaf B S hS X Z) V = ⊤ := hV
  have h1 : (1 : chartRing B S hS X.1 X.2 V) ∈
      chartIdeal B S hS X (definingIdealSheaf B S hS X Z) V ^ e := by
    rw [hV', Ideal.top_pow]
    exact Submodule.mem_top
  have h2 := le_idealPowerMultiple_obj B S hS X.1 X.2 (definingIdealSheaf B S hS X Z) e
    (SheafOfModules.unit _) V (Submodule.smul_mem_smul h1
      (Submodule.mem_top (x := (1 : chartRing B S hS X.1 X.2 V))))
  refine (Ideal.eq_top_iff_one _).2 ?_
  exact (one_mul (1 : chartRing B S hS X.1 X.2 V)) ▸ h2

end AlgebraicGeometry.Space

end
