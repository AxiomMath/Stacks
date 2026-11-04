module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.HenselianPairEtaleSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangePasteIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreEtaleSectionsHenselianLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreEtaleSectionsProper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GlobalSectionsBaseChangeCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GlobalSectionsComparisonTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedBaseFieldSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change for the direct image along a proper morphism

This file proves that the underived base change map `g^{-1} f_* ⟶ f'_* (g')^{-1}` of abelian
étale sheaves is an isomorphism for a cartesian square with `f` proper over a base point which is
the spectrum of a separably closed field lying over the closed point of a strictly henselian local
ring — the pieces of [Stacks, Tag 0A3T] and [Stacks, Tag 0A3U] that need no limit argument.

## Main results

* `Stacks.EtaleCohomology.isIso_of_isIso_Γ_map_of_isSepClosed` — on the spectrum of a separably
  closed field, a morphism of abelian étale sheaves is an isomorphism as soon as it is bijective
  on global sections.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isSepClosed` — the base change map is
  an isomorphism for every cartesian square over an extension `Spec Ω ⟶ Spec κ` of separably
  closed fields, with no hypothesis on the morphism.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_closedFibre` — the base change map of the
  closed-fibre square of a proper morphism to the spectrum of a strictly henselian local ring is an
  isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace Stacks.EtaleCohomology

/-- Global sections of a morphism of sheaves are invertible exactly when its component at the
terminal object is. -/
theorem isIso_Γ_map_iff_isIso_app_terminal {X : Scheme.{u}} {A : Type*} [Category A]
    [HasWeakSheafify (Scheme.smallEtaleTopology X) A]
    [HasGlobalSectionsFunctor (Scheme.smallEtaleTopology X) A]
    {F G : Sheaf (Scheme.smallEtaleTopology X) A} (φ : F ⟶ G) :
    IsIso ((Sheaf.Γ (Scheme.smallEtaleTopology X) A).map φ) ↔
      IsIso (φ.hom.app (op (terminal X.Etale))) :=
  NatIso.isIso_map_iff (Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology X) A
    (terminalIsTerminal (C := X.Etale))) φ

/-- **On the spectrum of a separably closed field, global sections detect isomorphisms of
abelian étale sheaves.** The stalk at the canonical point is global sections, and that single
point covers the spectrum. -/
theorem isIso_of_isIso_Γ_map_of_isSepClosed (κ : Type u) [Field κ] [IsSepClosed κ]
    {F G : Sheaf (Scheme.smallEtaleTopology (Spec (.of κ))) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (h : IsIso ((Sheaf.Γ (Scheme.smallEtaleTopology (Spec (.of κ))) AddCommGrpCat.{u + 1}).map
      φ)) : IsIso φ := by
  rw [← isIso_iff_of_reflects_iso _
    (sheafCompose (Scheme.smallEtaleTopology (Spec (.of κ))) (forget AddCommGrpCat.{u + 1}))]
  refine isIso_of_geometricStalk_family.{0, u} (Ω := fun _ : PUnit.{u + 1} ↦ κ)
    (fun _ ↦ 𝟙 (Spec (.of κ))) ?_ _ (fun _ ↦ ?_)
  · ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨PUnit.unit, x, rfl⟩
  · rw [NatIso.isIso_map_iff (sheafFiberIdIsoGamma.{u, 0} κ),
      isIso_Γ_map_iff_isIso_app_terminal]
    rw [isIso_Γ_map_iff_isIso_app_terminal] at h
    exact (inferInstance : IsIso ((forget AddCommGrpCat.{u + 1}).map
      (φ.hom.app (op (terminal (Spec (.of κ)).Etale)))))

/-- Restriction of abelian global sections along `c` is bijective, read as the unit of the
inverse-image/direct-image adjunction on global sections, as soon as some comparison of global
sections of sheaves of sets along `c` is an isomorphism. -/
theorem isIso_Γ_map_etaleAbelianUnit_of_isIso {T Z : Scheme.{u}} (c : T ⟶ Z)
    (α : Sheaf.Γ (Scheme.smallEtaleTopology Z) (Type (u + 1)) ⟶
      smallEtaleInverseImage.{u, 0} c ⋙ Sheaf.Γ (Scheme.smallEtaleTopology T) (Type (u + 1)))
    [IsIso α] (G : Sheaf (Scheme.smallEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    IsIso ((Sheaf.Γ (Scheme.smallEtaleTopology Z) AddCommGrpCat.{u + 1}).map
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} c).unit.app G)) :=
  (isIso_Γ_map_iff_isIso_app_terminal _).2
    (isIso_etaleAbelianUnit_app_terminal c G (isIso_unit_app_terminal_of_isIso c α _))

/-- The morphism of spectra induced by an extension of separably closed fields is geometrically
connected. -/
theorem geometricallyConnected_spec_map_of_isSepClosed (κ Ω : Type u) [Field κ] [IsSepClosed κ]
    [Field Ω] [Algebra κ Ω] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap κ Ω))) :=
  (AlgebraicGeometry.geometricallyConnected_spec_iff κ Ω).2
    ((Algebra.isGeometricallyConnected_iff_connectedSpace_primeSpectrum κ Ω).2 inferInstance)

/-- Restriction of abelian global sections along a flat, quasi-compact, geometrically connected
morphism is bijective ([Stacks, Tag 0A3I], [Stacks, Tag 0EZK]). -/
theorem isIso_Γ_map_etaleAbelianUnit_of_flat {T Z : Scheme.{u}} (c : T ⟶ Z) [Flat c]
    [QuasiCompact c] [GeometricallyConnected c]
    (G : Sheaf (Scheme.smallEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    IsIso ((Sheaf.Γ (Scheme.smallEtaleTopology Z) AddCommGrpCat.{u + 1}).map
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} c).unit.app G)) := by
  have : IsIso (globalSectionsSmallEtaleInverseImage.{u, 0} c) :=
    isIso_globalSectionsSmallEtaleInverseImage c (universally_isQuotientMap_of_flat_quasiCompact c)
  exact isIso_Γ_map_etaleAbelianUnit_of_isIso c (globalSectionsSmallEtaleInverseImage c) G

/-- Over the spectrum of a separably closed field, the base change map is an isomorphism as soon
as both unit maps are bijective on global sections. -/
private theorem isIso_etaleAbelianBaseChange_of_isIso_Γ_map_unit (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] {Z X₀ X' : Scheme.{u}} (x : Spec (.of Ω) ⟶ Z) (f₀ : X₀ ⟶ Z) (g' : X' ⟶ X₀)
    (f' : X' ⟶ Spec (.of Ω)) (w : g' ≫ f₀ = f' ≫ x)
    (hx : ∀ G, IsIso ((Sheaf.Γ (Scheme.smallEtaleTopology Z) AddCommGrpCat.{u + 1}).map
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} x).unit.app G)))
    (hg' : ∀ K, IsIso ((Sheaf.Γ (Scheme.smallEtaleTopology X₀) AddCommGrpCat.{u + 1}).map
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} g').unit.app K))) :
    IsIso (etaleAbelianBaseChange.{u, 0} f₀ x g' f' w) :=
  (NatTrans.isIso_iff_isIso_app _).2 fun K ↦ isIso_of_isIso_Γ_map_of_isSepClosed Ω _
    (isIso_Γ_map_etaleAbelianBaseChange_app.{u, 0} f₀ x g' f' w K (hx _) (hg' K))

/-- **Base change along a flat, quasi-compact, geometrically connected morphism to the spectrum
of a separably closed field.** For any `f₀ : X₀ ⟶ Z`, any such `x : Spec Ω ⟶ Z` with `Ω` separably
closed, and any cartesian square over `x`, the base change map `x^{-1} f₀_* ⟶ f'_* (g')^{-1}` of
abelian étale sheaves is an isomorphism: on global sections over `Spec Ω` both restriction maps
are bijective, and global sections detect isomorphisms on `Spec Ω`. -/
theorem isIso_etaleAbelianBaseChange_of_flat_of_isSepClosed (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] {Z X₀ X' : Scheme.{u}} (x : Spec (.of Ω) ⟶ Z) [Flat x] [QuasiCompact x]
    [GeometricallyConnected x] (f₀ : X₀ ⟶ Z) (g' : X' ⟶ X₀) (f' : X' ⟶ Spec (.of Ω))
    (sq : IsPullback g' f' f₀ x) :
    IsIso (etaleAbelianBaseChange.{u, 0} f₀ x g' f' sq.w) := by
  have : Flat g' := MorphismProperty.of_isPullback (P := @Flat) sq.flip inferInstance
  have : QuasiCompact g' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq.flip inferInstance
  have : GeometricallyConnected g' :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq.flip inferInstance
  exact isIso_etaleAbelianBaseChange_of_isIso_Γ_map_unit Ω x f₀ g' f' sq.w
    (isIso_Γ_map_etaleAbelianUnit_of_flat x) (isIso_Γ_map_etaleAbelianUnit_of_flat g')

/-- **Base change along an extension of separably closed fields.** For separably closed fields
`κ ⊆ Ω`, any morphism `f₀ : X₀ ⟶ Spec κ` and any cartesian square over `Spec Ω ⟶ Spec κ`, the base
change map of abelian étale sheaves is an isomorphism. -/
@[sga "4 XVI 1.6" "Degree-zero clause"]
theorem isIso_etaleAbelianBaseChange_of_isSepClosed (κ Ω : Type u) [Field κ] [IsSepClosed κ]
    [Field Ω] [IsSepClosed Ω] [Algebra κ Ω] {X₀ X' : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of κ))
    (g' : X' ⟶ X₀) (f' : X' ⟶ Spec (.of Ω))
    (sq : IsPullback g' f' f₀ (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)))) :
    IsIso (etaleAbelianBaseChange.{u, 0} f₀ (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)))
      g' f' sq.w) :=
  have := geometricallyConnected_spec_map_of_isSepClosed κ Ω
  isIso_etaleAbelianBaseChange_of_flat_of_isSepClosed Ω _ f₀ g' f' sq

/-- **Base change to the closed fibre over a strictly henselian local ring.** For `R` strictly
henselian local and `f : X ⟶ Spec R` proper, the base change map of the closed-fibre square
`X₀ = X ×_{Spec R} Spec κ ⟶ X` is an isomorphism of abelian étale sheaves on `Spec κ`.

On global sections over `Spec κ` the two restriction maps in play are bijective: along
`Spec κ ⟶ Spec R` by [Stacks, Tag 09ZH], along `X₀ ⟶ X` by [Stacks, Tag 0A3S]. The residue field
is separably closed, so global sections detect isomorphisms on `Spec κ`. -/
@[sga "4 XII 5.2" "(i), special case, (iii)", sga "4½ Arcata 4.1.2" "partial"]
theorem isIso_etaleAbelianBaseChange_closedFibre (R : Type u) [CommRing R]
    [StrictlyHenselianLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] :
    IsIso (etaleAbelianBaseChange.{u, 0} f (residueFieldPoint R) (closedFibreInclusion R f)
      (closedFibreProjection R f) (isPullback_closedFibre R f).w) := by
  have h09ZH : IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, 0}
      (residueFieldPoint R)).val :=
    isIso_globalSectionsComparison_maximalIdeal.{u, 0} R
  have h0A3S : IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, 0}
      (closedFibreInclusion R f)).val :=
    isIso_globalSectionsComparison_closedFibre_of_isProper.{u, 0} R f
  exact isIso_etaleAbelianBaseChange_of_isIso_Γ_map_unit (IsLocalRing.ResidueField R)
    (residueFieldPoint R) f (closedFibreInclusion R f) (closedFibreProjection R f)
    (isPullback_closedFibre R f).w
    (isIso_Γ_map_etaleAbelianUnit_of_isIso (residueFieldPoint R)
      (globalSectionsSmallEtaleInverseImageComparison.{u, 0} (residueFieldPoint R)).val)
    (isIso_Γ_map_etaleAbelianUnit_of_isIso (closedFibreInclusion R f)
      (globalSectionsSmallEtaleInverseImageComparison.{u, 0} (closedFibreInclusion R f)).val)

/-- **Base change at a geometric point over the closed point of a strictly henselian local
ring.** Let `R` be strictly henselian local with residue field `κ`, let `f : X ⟶ Spec R` be proper,
let `κ ⊆ Ω` be an extension with `Ω` separably closed and let `t : Spec Ω ⟶ Spec R` be the
composite `Spec Ω ⟶ Spec κ ⟶ Spec R`. For every cartesian square over `t` the base change map
`t^{-1} f_* ⟶ q_* p^{-1}` of abelian étale sheaves is an isomorphism. -/
@[sga "4½ Arcata 4.1.2" "partial"]
theorem isIso_etaleAbelianBaseChange_of_strictlyHenselian (R : Type u) [CommRing R]
    [StrictlyHenselianLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra (IsLocalRing.ResidueField R) Ω]
    {Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Spec (.of Ω))
    (sq : IsPullback p q f
      (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) Ω)) ≫
        residueFieldPoint R)) :
    IsIso (etaleAbelianBaseChange.{u, 0} f
      (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) Ω)) ≫
        residueFieldPoint R) p q sq.w) := by
  obtain ⟨k, hkfst, hksnd⟩ := (isPullback_closedFibre R f).exists_lift p
    (q ≫ Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) Ω)))
    (sq.w.trans (Category.assoc _ _ _).symm)
  have sqU : IsPullback k q (closedFibreProjection R f)
      (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) Ω))) :=
    IsPullback.of_right (hkfst ▸ sq) hksnd (isPullback_closedFibre R f)
  exact isIso_etaleAbelianBaseChange_of_paste (residueFieldPoint R) f (closedFibreProjection R f)
    (closedFibreInclusion R f) _ q k (isPullback_closedFibre R f).w sqU.w _ rfl p hkfst.symm sq.w
    (isIso_etaleAbelianBaseChange_closedFibre R f)
    (isIso_etaleAbelianBaseChange_of_isSepClosed (IsLocalRing.ResidueField R) Ω
      (closedFibreProjection R f) k q sqU)

/-- `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_strictlyHenselian` for a geometric
point `t` given together with its factorization through the closed point. -/
@[sga "4½ Arcata 4.1.2" "partial"]
theorem isIso_etaleAbelianBaseChange_of_strictlyHenselian_of_eq (R : Type u) [CommRing R]
    [StrictlyHenselianLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra (IsLocalRing.ResidueField R) Ω]
    {Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Spec (.of Ω)) (t : Spec (.of Ω) ⟶ Spec (.of R))
    (ht : t = Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) Ω)) ≫
      residueFieldPoint R)
    (sq : IsPullback p q f t) :
    IsIso (etaleAbelianBaseChange.{u, 0} f t p q sq.w) := by
  subst ht
  exact isIso_etaleAbelianBaseChange_of_strictlyHenselian R f Ω p q sq

end Stacks.EtaleCohomology

end
