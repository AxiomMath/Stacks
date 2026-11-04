module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineSkyscraper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModule

/-!
# The stalks of `R¹ j_* μ_N` over the origin of `𝐀¹_k` have `N` elements

Let `k` be a field, `N` invertible in `k` and `j : 𝐆_m ⟶ 𝐀¹_k`. At every geometric point `x` of
`𝐀¹_k` over the origin, the stalk of `R¹ j_* μ_N` has exactly `N` elements.

Over an algebraically closed field `L` this is the computation `R¹ j_* μ_N ≅ 0_* (ℤ/N)`
(`Stacks.EtaleCohomology.Purity.natCard_sections_rightDerived_one_rootsOfUnity`): a sheaf on `𝐀¹_L`
vanishing on `𝐆_m` is the direct image of its restriction to the origin, whose stalks over the
separably closed `L` are its global sections. The general case descends along
`k ⊆ K = k^{sep} ⊆ L = K̄`: stalks at geometric points only depend on the point up to an extension
of separably closed fields; along `Spec K ⟶ Spec k` higher direct images commute with base change
(`Stacks.EtaleCohomology.SeparableBaseChange.isIso_higherBaseChangeMapAb`), and along the universal
homeomorphism `Spec L ⟶ Spec K` direct image is an equivalence; finally the base change of
`𝐆_m ⊆ 𝐀¹` along a field extension is `𝐆_m ⊆ 𝐀¹`, so smooth base change along that isomorphism
identifies the direct images.

## Main results

* `Stacks.EtaleCohomology.Purity.nonempty_stalk_iso_sections_of_isSepClosed`: the stalks of a
  sheaf on the spectrum of a separably closed field are its global sections.
* `Stacks.EtaleCohomology.Purity.nonempty_stalk_comp_iso_stalk`: stalks do not change along an
  extension of separably closed fields.
* `Stacks.EtaleCohomology.Purity.eq_comp_origin_of_range_subset`: a geometric point of `𝐀¹_k` off
  `𝐆_m` factors through the origin.
* `Stacks.EtaleCohomology.Purity.natCard_stalk_rightDerived_one_rootsOfUnity`: the stalks of
  `R¹ j_* μ_N` at geometric points over the origin have `N` elements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Purity

attribute [-instance] CategoryTheory.catToReflQuiver

/-- Isomorphic abelian groups have the same cardinality. -/
private theorem natCard_eq_of_iso {A B : Ab.{u + 1}} (e : A ≅ B) : Nat.card A = Nat.card B :=
  Nat.card_congr e.addCommGroupIsoToAddEquiv.toEquiv

/-- **The stalks of a sheaf on the spectrum of a separably closed field are its global sections**,
at every geometric point. -/
theorem nonempty_stalk_iso_sections_of_isSepClosed (K : Type u) [Field K] [IsSepClosed K]
    (G : Sheaf (smallEtaleTopology (Spec (.of K))) Ab.{u + 1}) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (p : Spec (.of Ω) ⟶ Spec (.of K)) :
    Nonempty ((smallEtaleStalkAb p).obj G ≅
      ((sheafSections (smallEtaleTopology (Spec (.of K))) Ab.{u + 1}).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))).obj G) := by
  let adj := constantSheafAdj (smallEtaleTopology (Spec (.of K))) Ab.{u + 1}
    (isTerminalEtaleMkId (Spec (.of K)))
  have := isEquivalence_sheafSections_final_of_isSepClosed K Ab.{u + 1}
  have : IsIso (adj.counit.app G) := inferInstance
  exact ⟨(smallEtaleStalkAb p).mapIso (asIso (adj.counit.app G)).symm ≪≫
    CategoryTheory.Sites.constantSheafFiberIso (Scheme.pointSmallEtale p)
      (((sheafSections (smallEtaleTopology (Spec (.of K))) Ab.{u + 1}).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))).obj G)⟩

/-- **Stalks do not change along an extension of separably closed fields**: for a geometric point
`y : Spec K ⟶ X` and `π : Spec Ω ⟶ Spec K` with `Ω` separably closed, the stalks at `π ≫ y` and
at `y` are isomorphic. -/
theorem nonempty_stalk_comp_iso_stalk {X : Scheme.{u}} (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    {K : Type u} [Field K] [IsSepClosed K] (y : Spec (.of K) ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (π : Spec (.of Ω) ⟶ Spec (.of K)) :
    Nonempty ((smallEtaleStalkAb (π ≫ y)).obj F ≅ (smallEtaleStalkAb y).obj F) := by
  obtain ⟨e2⟩ := nonempty_stalk_iso_sections_of_isSepClosed K ((smallEtalePullbackAb y).obj F) π
  obtain ⟨e3⟩ := nonempty_stalk_iso_sections_of_isSepClosed K ((smallEtalePullbackAb y).obj F)
    (𝟙 _)
  have e4 := (smallEtalePullbackStalkAbIso y (𝟙 (Spec (.of K)))).app F
  rw [Category.id_comp] at e4
  exact ⟨((smallEtalePullbackStalkAbIso y π).app F).symm ≪≫ e2 ≪≫ e3.symm ≪≫ e4⟩

/-- The origin is a section of `𝐀¹_k ⟶ Spec k`. -/
theorem origin_comp_over (k : Type u) [Field k] :
    origin k ≫ (affineLine k ↘ Spec (.of k)) = 𝟙 _ := by
  rw [origin, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext c
  simp

/-- The coordinate vanishes at the origin. -/
theorem origin_appTop_coordinate (k : Type u) [Field k] :
    (origin k).appTop (coordinate k) = 0 := by
  rw [origin, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coordinate,
    AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  simp

/-- **A geometric point of `𝐀¹_k` off `𝐆_m` factors through the origin.** -/
theorem eq_comp_origin_of_range_subset {k : Type u} [Field k] {Ω : Type u} [Field Ω]
    (z : Spec (.of Ω) ⟶ affineLine k)
    (hz : Set.range z.base ⊆ ((punctured k : Set (affineLine k)))ᶜ) :
    z = (z ≫ (affineLine k ↘ Spec (.of k))) ≫ origin k := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, origin_comp_over, Category.comp_id]
  · intro i
    rw [Subsingleton.elim i ⟨0⟩, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    show z.appTop (coordinate k) =
      (z ≫ (affineLine k ↘ Spec (.of k))).appTop ((origin k).appTop (coordinate k))
    rw [origin_appTop_coordinate, map_zero]
    by_contra hne
    have hu : IsUnit (z.appTop (coordinate k)) := by
      let e := (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv
      have h1 : e (z.appTop (coordinate k)) ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff e e.injective]
      have h2 := (isUnit_iff_ne_zero.2 h1).map e.symm
      rwa [RingEquiv.symm_apply_apply] at h2
    obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
    refine hz ⟨p, rfl⟩ (?_ : p ∈ z ⁻¹ᵁ punctured k)
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hu]
    trivial

/-- **Over an algebraically closed field the stalks of `R¹ j_* μ_N` over the origin have `N`
elements**: `R¹ j_* μ_N` vanishes on `𝐆_m`, so it is the direct image of its restriction to the
origin, whose stalks are its global sections, which are `Γ(𝐀¹, R¹ j_* μ_N) ≅ ℤ/N`. -/
theorem natCard_stalk_rightDerived_one_rootsOfUnity_of_isAlgClosed (L : Type u) [Field L]
    [IsAlgClosed L] {N : ℕ} (hN0 : 0 < N) (hN : IsUnit (N : L)) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ affineLine L)
    (hz : Set.range z.base ⊆ ((punctured L : Set (affineLine L)))ᶜ) :
    Nat.card ((smallEtaleStalkAb z).obj
      (((smallEtalePushforwardAb (punctured L).ι).rightDerived 1).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured L).toScheme N))) = N := by
  let R' := ((smallEtalePushforwardAb (punctured L).ι).rightDerived 1).obj
    (rootsOfUnityPunctured L (ℓ := N))
  rw [← natCard_eq_of_iso ((smallEtaleStalkAb z).mapIso
    (((smallEtalePushforwardAb (punctured L).ι).rightDerived 1).mapIso
      (restrictionRootsOfUnityIso (punctured L).ι N)))]
  have hres : IsZero ((etaleRestriction.{u, 0} (punctured L).ι).obj R') :=
    isZero_restriction_rightDerived_of_isOpenImmersion (punctured L).ι _
      (fun t a => ⟨N, hN0, by
        exact_mod_cast isUnit_natCast_globalSections_of_over (affineLine L ↘ Spec (.of L)) hN,
        nsmul_eq_zero_stalk_rootsOfUnityPunctured L t a⟩) 1 one_pos
  have hunit := isIso_unit_origin_of_isZero_restriction L R' hres
  have hz' := eq_comp_origin_of_range_subset z hz
  rw [hz', ← natCard_eq_of_iso ((smallEtalePullbackStalkAbIso (origin L)
    (z ≫ (affineLine L ↘ Spec (.of L)))).app R')]
  obtain ⟨e⟩ := nonempty_stalk_iso_sections_of_isSepClosed L
    ((smallEtalePullbackAb (origin L)).obj R') (z ≫ (affineLine L ↘ Spec (.of L)))
  show Nat.card ((smallEtaleStalkAb (z ≫ (affineLine L ↘ Spec (.of L)))).obj
    ((smallEtalePullbackAb (origin L)).obj R')) = N
  rw [natCard_eq_of_iso e]
  let M := (etaleAbelianInverseImage.{u, 0} (origin L)).obj R'
  let : MorphismProperty.ContainsIdentities (@Etale.{u}) := ⟨fun _ => inferInstance⟩
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 (Spec (.of L)))) :=
    MorphismProperty.Over.mkIdTerminal _ _
  let Γk := (sheafSections (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (op (Scheme.Etale.mk (𝟙 (Spec (.of L)))))
  let eM : Γk.obj M ≅ (Sheaf.Γ (affineLine L).smallEtaleTopology AddCommGrpCat.{u + 1}).obj R' :=
    ((Sheaf.ΓNatIsoSheafSections _ _ hT).app M).symm ≪≫
      ((etaleAbelianDirectImageGammaIso.{u, 0} (origin L)).app M).symm ≪≫
      (Sheaf.Γ _ _).mapIso (asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0}
        (origin L)).unit.app R')).symm
  rw [natCard_eq_of_iso (Γk.mapIso ((smallEtalePullbackAbIsoInverseImage (origin L)).app R')),
    natCard_eq_of_iso eM]
  exact natCard_sections_rightDerived_one_rootsOfUnity L hN0 hN

section BaseChange

variable (F E : Type u) [Field F] [Field E] [Algebra F E]

/-- `Spec E ⟶ Spec F` for a field extension `E/F`. -/
abbrev specMap : Spec (.of E) ⟶ Spec (.of F) := Spec.map (CommRingCat.ofHom (algebraMap F E))

/-- **The base change of `𝐀¹_F` to `E` is `𝐀¹_E`.** -/
def affineLineBaseChangeIso :
    Limits.pullback (specMap F E) (affineLine F ↘ Spec (.of F)) ≅ affineLine E :=
  (IsPullback.of_hasPullback (specMap F E) (affineLine F ↘ Spec (.of F))).isoIsPullback _ _
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (specMap F E)).flip

/-- Composing `affineLineBaseChangeIso` with the base-change map `𝐀¹_E ⟶ 𝐀¹_F` gives the second
projection of the pullback. -/
theorem affineLineBaseChangeIso_hom_map :
    (affineLineBaseChangeIso F E).hom ≫ AffineSpace.map (ULift.{u} (Fin 1)) (specMap F E) =
      pullback.snd (specMap F E) (affineLine F ↘ Spec (.of F)) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The preimage of `𝐆_{m,F}` in `𝐀¹_E` is `𝐆_{m,E}`. -/
theorem preimage_punctured_map :
    AffineSpace.map (ULift.{u} (Fin 1)) (specMap F E) ⁻¹ᵁ punctured F = punctured E := by
  rw [Scheme.preimage_basicOpen_top, coordinate, AffineSpace.map_appTop_coord]
  rfl

/-- **The base change of `𝐆_m ⊆ 𝐀¹_F` to `E` is `𝐆_m ⊆ 𝐀¹_E`.** -/
def puncturedBaseChangeIso :
    Limits.pullback (specMap F E) ((punctured F).ι ≫ (affineLine F ↘ Spec (.of F))) ≅
      (punctured E).toScheme := by
  have sq := SeparableBaseChange.isPullback_baseChangeMap (affineLine F ↘ Spec (.of F))
    (punctured F).ι (specMap F E)
  have sq3 := IsPullback.of_iso sq (Iso.refl _) (affineLineBaseChangeIso F E) (Iso.refl _)
    (Iso.refl _)
    (fst' := SeparableBaseChange.baseChangeMap (affineLine F ↘ Spec (.of F)) (punctured F).ι
      (specMap F E) ≫ (affineLineBaseChangeIso F E).hom)
    (snd' := pullback.snd (specMap F E) ((punctured F).ι ≫ (affineLine F ↘ Spec (.of F))))
    (f' := AffineSpace.map (ULift.{u} (Fin 1)) (specMap F E)) (g' := (punctured F).ι)
    (by simp) (by simp) (by simp [affineLineBaseChangeIso_hom_map]) (by simp)
  exact sq3.isoIsPullback _ _ (isPullback_morphismRestrict
      (AffineSpace.map (ULift.{u} (Fin 1)) (specMap F E)) (punctured F)).flip ≪≫
    (affineLine E).isoOfEq (preimage_punctured_map F E)

/-- Composing `puncturedBaseChangeIso` with the inclusion `𝐆_{m,E} ⟶ 𝐀¹_E` agrees with the base
change of the inclusion `𝐆_{m,F} ⟶ 𝐀¹_F` followed by `affineLineBaseChangeIso`. -/
theorem puncturedBaseChangeIso_hom_ι :
    (puncturedBaseChangeIso F E).hom ≫ (punctured E).ι =
      SeparableBaseChange.baseChangeMap (affineLine F ↘ Spec (.of F)) (punctured F).ι
        (specMap F E) ≫ (affineLineBaseChangeIso F E).hom := by
  simp only [puncturedBaseChangeIso, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι]
  exact IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- A lift of a point off `𝐆_{m,F}` to the base change lies off `𝐆_{m,E}`. -/
theorem range_comp_affineLineBaseChangeIso_subset {Ω : Type u} [Field Ω]
    (x' : Spec (.of Ω) ⟶ Limits.pullback (specMap F E) (affineLine F ↘ Spec (.of F)))
    (hx : Set.range (x' ≫ pullback.snd (specMap F E) (affineLine F ↘ Spec (.of F))).base ⊆
      ((punctured F : Set (affineLine F)))ᶜ) :
    Set.range (x' ≫ (affineLineBaseChangeIso F E).hom).base ⊆
      ((punctured E : Set (affineLine E)))ᶜ := by
  rintro _ ⟨p, rfl⟩ hp
  apply hx ⟨p, rfl⟩
  have : (x' ≫ (affineLineBaseChangeIso F E).hom).base p ∈
      AffineSpace.map (ULift.{u} (Fin 1)) (specMap F E) ⁻¹ᵁ punctured F := by
    rwa [preimage_punctured_map]
  show (x' ≫ pullback.snd (specMap F E) (affineLine F ↘ Spec (.of F))).base p ∈
    (punctured F : Set (affineLine F))
  rwa [← affineLineBaseChangeIso_hom_map, ← Category.assoc]

/-- The inverse image of `μ_N` is `μ_N`, for `N` invertible. -/
def pullbackRootsOfUnityIso {X Y : Scheme.{u}} (π : X ⟶ Y) (N : ℕ)
    (hN : IsUnit ((N : ℕ) : Γ(Y, ⊤))) :
    (smallEtalePullbackAb π).obj (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} Y N) ≅
      Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X N :=
  (smallEtalePullbackAbIsoInverseImage π).app _ ≪≫
    Stacks.Kummer.rootsOfUnityInverseImageIso.{u, 0} π N hN

variable {F E} {N : ℕ} (hN0 : 0 < N) (hNE : IsUnit (N : E))

include hN0 hNE in
/-- **Smooth base change along `𝐀¹_E ≅ (𝐀¹_F)_E`**: the stalk of `R¹ h_* μ_N` along the base
change `h` of `𝐆_m ⊆ 𝐀¹_F` at a point is the stalk of `R¹ j_* μ_N` along `j : 𝐆_{m,E} ⊆ 𝐀¹_E`. -/
theorem natCard_stalk_baseChange_eq {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x' : Spec (.of Ω) ⟶ Limits.pullback (specMap F E) (affineLine F ↘ Spec (.of F)))
    (G : Sheaf (smallEtaleTopology
      (Limits.pullback (specMap F E) ((punctured F).ι ≫ (affineLine F ↘ Spec (.of F)))))
      Ab.{u + 1})
    (eG : G ≅ Stacks.Kummer.rootsOfUnitySheaf.{u, 0} _ N) :
    Nat.card ((smallEtaleStalkAb x').obj (((smallEtalePushforwardAb
        (SeparableBaseChange.baseChangeMap (affineLine F ↘ Spec (.of F)) (punctured F).ι
          (specMap F E))).rightDerived 1).obj G)) =
      Nat.card ((smallEtaleStalkAb (x' ≫ (affineLineBaseChangeIso F E).hom)).obj
        (((smallEtalePushforwardAb (punctured E).ι).rightDerived 1).obj
          (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured E).toScheme N))) := by
  let ψ := affineLineBaseChangeIso F E
  let ψ₀ := puncturedBaseChangeIso F E
  let h := SeparableBaseChange.baseChangeMap (affineLine F ↘ Spec (.of F)) (punctured F).ι
    (specMap F E)
  have sq : IsPullback h ψ₀.hom ψ.hom (punctured E).ι :=
    IsPullback.of_vert_isIso ⟨(puncturedBaseChangeIso_hom_ι F E).symm⟩
  have : IsSeparated (punctured E).ι := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated (punctured E).ι := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  have hN' : IsUnit ((N : ℤ) : Γ(affineLine E, ⊤)) := by
    exact_mod_cast isUnit_natCast_globalSections_of_over (ℓ := N)
      (affineLine E ↘ Spec (.of E)) hNE
  have hb := SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth ψ.hom h ψ₀.hom
    (punctured E).ι sq (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured E).toScheme N)
    (fun t a => ⟨N, hN0, hN', nsmul_eq_zero_stalk_of_nsmul_id
      (Stacks.Kummer.nsmul_id_rootsOfUnitySheaf_univ.{u, 0} _ N) t a⟩) 1
  have hNY : IsUnit ((N : ℕ) : Γ((punctured E).toScheme, ⊤)) :=
    isUnit_natCast_globalSections_of_over (ℓ := N)
      ((punctured E).ι ≫ (affineLine E ↘ Spec (.of E))) hNE
  let eG' : G ≅ (smallEtalePullbackAb ψ₀.hom).obj
      (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured E).toScheme N) :=
    eG ≪≫ (pullbackRootsOfUnityIso ψ₀.hom N hNY).symm
  rw [natCard_eq_of_iso ((smallEtaleStalkAb x').mapIso
    (((smallEtalePushforwardAb h).rightDerived 1).mapIso eG'))]
  exact (natCard_eq_of_iso ((smallEtaleStalkAb x').mapIso (@asIso _ _ _ _ _ hb))).symm.trans
    (natCard_eq_of_iso ((smallEtalePullbackStalkAbIso ψ.hom x').app _))

end BaseChange

section Descent

variable {F : Type u} [Field F] {N : ℕ}

/-- The base change of the punctured line along `Spec E ⟶ Spec F`. -/
abbrev puncturedProj (F E : Type u) [Field F] [Field E] [Algebra F E] :=
  pullback.snd (specMap F E) ((punctured F).ι ≫ (affineLine F ↘ Spec (.of F)))

/-- **Along a separable algebraic extension**, the stalk of `R¹ j_* μ_N` at the image of a point of
the base change is the stalk of `R¹` of the base change. -/
theorem natCard_stalk_comp_snd_of_isSeparable (E : Type u) [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x' : Spec (.of Ω) ⟶ Limits.pullback (specMap F E) (affineLine F ↘ Spec (.of F))) :
    Nat.card ((smallEtaleStalkAb
        (x' ≫ pullback.snd (specMap F E) (affineLine F ↘ Spec (.of F)))).obj
        (((smallEtalePushforwardAb (punctured F).ι).rightDerived 1).obj
          (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured F).toScheme N))) =
      Nat.card ((smallEtaleStalkAb x').obj (((smallEtalePushforwardAb
        (SeparableBaseChange.baseChangeMap (affineLine F ↘ Spec (.of F)) (punctured F).ι
          (specMap F E))).rightDerived 1).obj ((smallEtalePullbackAb (puncturedProj F E)).obj
            (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured F).toScheme N)))) := by
  have hb := SeparableBaseChange.isIso_higherBaseChangeMapAb F E (affineLine F ↘ Spec (.of F))
    (punctured F).ι (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured F).toScheme N) 1
  exact (natCard_eq_of_iso ((smallEtalePullbackStalkAbIso _ x').app _)).symm.trans
    (natCard_eq_of_iso ((smallEtaleStalkAb x').mapIso (@asIso _ _ _ _ _ hb)))

/-- **Along `Spec F̄ ⟶ Spec F` for `F` separably closed**, a universal homeomorphism, the stalk of
`R¹ j_* μ_N` at the image of a point of the base change is the stalk of `R¹` of the base
change: direct image along the base change of `𝐀¹_F` is an equivalence. -/
theorem natCard_stalk_comp_snd_of_isSepClosed [IsSepClosed F] {Ω : Type u} [Field Ω]
    [IsSepClosed Ω]
    (x' : Spec (.of Ω) ⟶ Limits.pullback (specMap F (AlgebraicClosure F))
      (affineLine F ↘ Spec (.of F))) :
    Nat.card ((smallEtaleStalkAb (x' ≫ pullback.snd (specMap F (AlgebraicClosure F))
        (affineLine F ↘ Spec (.of F)))).obj
        (((smallEtalePushforwardAb (punctured F).ι).rightDerived 1).obj
          (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured F).toScheme N))) =
      Nat.card ((smallEtaleStalkAb x').obj (((smallEtalePushforwardAb
        (SeparableBaseChange.baseChangeMap (affineLine F ↘ Spec (.of F)) (punctured F).ι
          (specMap F (AlgebraicClosure F)))).rightDerived 1).obj
            ((smallEtalePullbackAb (puncturedProj F (AlgebraicClosure F))).obj
            (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured F).toScheme N)))) := by
  let s := specMap F (AlgebraicClosure F)
  let πF := affineLine F ↘ Spec (.of F)
  let j := (punctured F).ι
  have := universalHomeomorphism_spec_algebraicClosure F
  let f' := pullback.snd s πF
  let e' := pullback.snd s (j ≫ πF)
  let h := SeparableBaseChange.baseChangeMap πF j s
  have sq := SeparableBaseChange.isPullback_baseChangeMap πF j s
  have : UniversalHomeomorphism f' := universalHomeomorphism_pullback_snd s πF
  have : UniversalHomeomorphism e' := universalHomeomorphism_pullback_snd s (j ≫ πF)
  have := isEquivalence_smallEtalePushforwardAb_of_universalHomeomorphism f'
  let μ := Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured F).toScheme N
  have hb := isIso_higherBaseChangeMapAb_app_of_universalHomeomorphism e' j (𝟙 _) rfl (e' ≫ j)
    (by simp) 1 μ
  let eR : ((smallEtalePushforwardAb j).rightDerived 1).obj μ ≅
      (smallEtalePushforwardAb f').obj (((smallEtalePushforwardAb h).rightDerived 1).obj
        ((smallEtalePullbackAb e').obj μ)) :=
    ((smallEtalePullbackAbIdOf (𝟙 _) rfl).app _).symm ≪≫ @asIso _ _ _ _ _ hb ≪≫
      (Functor.rightDerivedIsoOfNatIso (eqToIso (congrArg smallEtalePushforwardAb sq.w.symm))
        1).app _ ≪≫
      (Functor.rightDerivedIsoOfNatIso (smallEtalePushforwardAbCompIso h f').symm 1).app _ ≪≫
      ((smallEtalePushforwardAb h).rightDerivedCompIso (smallEtalePushforwardAb f') 1).app _
  have : IsIso ((smallEtaleAdjunctionAb f').counit.app (((smallEtalePushforwardAb h).rightDerived
      1).obj ((smallEtalePullbackAb e').obj μ))) := inferInstance
  rw [natCard_eq_of_iso ((smallEtaleStalkAb _).mapIso eR)]
  exact (natCard_eq_of_iso ((smallEtalePullbackStalkAbIso f' x').app _)).symm.trans
    (natCard_eq_of_iso ((smallEtaleStalkAb x').mapIso
      (asIso ((smallEtaleAdjunctionAb f').counit.app _))))

end Descent

/-- `Spec` of an algebra map, composed with `Spec` of a ring map out of the algebra, as `Spec` of
the composite. -/
theorem spec_map_comp_specMap {F E Ω : Type u} [Field F] [Field E] [Field Ω] [Algebra F E]
    [Algebra F Ω] (φ : E →ₐ[F] Ω) :
    Spec.map (CommRingCat.ofHom (φ : E →+* Ω)) ≫ specMap F E =
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) := by
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact φ.commutes c

/-- **The stalks of `R¹ j_* μ_N` over the origin of `𝐀¹_k` have `N` elements**, for every field
`k`, `N` invertible in `k` and every geometric point `x` over the origin. -/
theorem natCard_stalk_rightDerived_one_rootsOfUnity (k : Type u) [Field k] {N : ℕ} (hN0 : 0 < N)
    (hN : IsUnit (N : k)) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ affineLine k)
    (hx : Set.range x.base ⊆ ((punctured k : Set (affineLine k)))ᶜ) :
    Nat.card ((smallEtaleStalkAb x).obj
      (((smallEtalePushforwardAb (punctured k).ι).rightDerived 1).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured k).toScheme N))) = N := by
  let K := SeparableClosure k
  let L := AlgebraicClosure K
  have hNk : IsUnit ((N : ℕ) : Γ((punctured k).toScheme, ⊤)) :=
    isUnit_natCast_globalSections_of_over (ℓ := N)
      ((punctured k).ι ≫ (affineLine k ↘ Spec (.of k))) hN
  have hNK : IsUnit (N : K) := by simpa using hN.map (algebraMap k K)
  have hNK' : IsUnit ((N : ℕ) : Γ((punctured K).toScheme, ⊤)) :=
    isUnit_natCast_globalSections_of_over (ℓ := N)
      ((punctured K).ι ≫ (affineLine K ↘ Spec (.of K))) hNK
  have hNL : IsUnit (N : L) := by simpa using hNK.map (algebraMap K L)
  let : Algebra k Ω := (Spec.preimage (x ≫ (affineLine k ↘ Spec (.of k)))).hom.toAlgebra
  let φ : K →ₐ[k] Ω := IsSepClosed.lift
  have w : Spec.map (CommRingCat.ofHom (φ : K →+* Ω)) ≫ specMap k K =
      x ≫ (affineLine k ↘ Spec (.of k)) := by
    rw [spec_map_comp_specMap φ]
    exact Spec.map_preimage _
  let x' := pullback.lift _ _ w
  have hx' : x' ≫ pullback.snd (specMap k K) (affineLine k ↘ Spec (.of k)) = x :=
    pullback.lift_snd _ _ _
  rw [← hx', natCard_stalk_comp_snd_of_isSeparable K x',
    natCard_stalk_baseChange_eq hN0 hNK x' _ (pullbackRootsOfUnityIso _ N hNk)]
  have hy := range_comp_affineLineBaseChangeIso_subset k K x' (by rw [hx']; exact hx)
  let y := x' ≫ (affineLineBaseChangeIso k K).hom
  let π := Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
  obtain ⟨e⟩ := nonempty_stalk_comp_iso_stalk
    (((smallEtalePushforwardAb (punctured K).ι).rightDerived 1).obj
      (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured K).toScheme N)) y π
  show Nat.card ((smallEtaleStalkAb y).obj _) = N
  rw [← natCard_eq_of_iso e]
  let : Algebra K (AlgebraicClosure Ω) :=
    (Spec.preimage ((π ≫ y) ≫ (affineLine K ↘ Spec (.of K)))).hom.toAlgebra
  have : Module.IsTorsionFree K L :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap K L).injective
  have : Module.IsTorsionFree K (AlgebraicClosure Ω) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap K (AlgebraicClosure Ω)).injective
  let φ' : L →ₐ[K] AlgebraicClosure Ω := IsAlgClosed.lift
  have w' : Spec.map (CommRingCat.ofHom (φ' : L →+* AlgebraicClosure Ω)) ≫ specMap K L =
      (π ≫ y) ≫ (affineLine K ↘ Spec (.of K)) := by
    rw [spec_map_comp_specMap φ']
    exact Spec.map_preimage _
  let y' := pullback.lift _ _ w'
  have hy' : y' ≫ pullback.snd (specMap K L) (affineLine K ↘ Spec (.of K)) = π ≫ y :=
    pullback.lift_snd _ _ _
  rw [← hy', natCard_stalk_comp_snd_of_isSepClosed y',
    natCard_stalk_baseChange_eq hN0 hNL y' _ (pullbackRootsOfUnityIso _ N hNK')]
  have hπy : Set.range (π ≫ y).base ⊆ ((punctured K : Set (affineLine K)))ᶜ := by
    rintro _ ⟨p, rfl⟩
    exact hy ⟨π.base p, rfl⟩
  exact natCard_stalk_rightDerived_one_rootsOfUnity_of_isAlgClosed L hN0 hNL _
    (range_comp_affineLineBaseChangeIso_subset K L y' (by rw [hy']; exact hπy))

end Stacks.EtaleCohomology.Purity

end
