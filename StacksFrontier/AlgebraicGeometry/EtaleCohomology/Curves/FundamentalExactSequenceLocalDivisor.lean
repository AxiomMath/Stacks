module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSurjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreFunctionFieldIsoSupplement

/-!
# A divisor on a smooth curve is étale-locally the divisor of a function

placeholder
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- **The projection from the fibre of an étale `X`-scheme over a point of `X` is injective on
points**, being a base change of the preimmersion `Spec κ(x) ⟶ X`. -/
theorem injective_base_pullback_fst_fromSpecResidueField {X : Scheme.{u}} (z : X) (V : X.Etale) :
    Function.Injective (pullback.fst V.hom (X.fromSpecResidueField z)).base := by
  have : IsPreimmersion (X.fromSpecResidueField z) := inferInstance
  have : IsPreimmersion (pullback.fst V.hom (X.fromSpecResidueField z)) := inferInstance
  exact (pullback.fst V.hom (X.fromSpecResidueField z)).isEmbedding.injective

section Local

attribute [local instance] Classical.decEq

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper
  hasCoproduct_closedPointSkyscraper_obj

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsCurve k fX]
  [Smooth fX]

/-- The instances carried by an affine open subscheme of an integral étale `X`-scheme containing
a given point. -/
private theorem isIntegral_etaleOpenSub {W : X.Etale} [AlgebraicGeometry.IsIntegral W.left]
    {O : W.left.Opens} {w : W.left} (hw : w ∈ O) :
    AlgebraicGeometry.IsIntegral (etaleOpenSub W O).left := by
  have : Nonempty ↥O := ⟨⟨w, hw⟩⟩
  have : Nonempty ↥O.toScheme := ⟨⟨w, hw⟩⟩
  exact inferInstanceAs (AlgebraicGeometry.IsIntegral O.toScheme)

/-- The instances carried by an affine open subscheme of an integral étale `X`-scheme containing
a given point, together with local noetherianity. -/
private theorem instances_etaleOpenSub (f : X ⟶ Spec (.of k)) [IsCurve k f] {W : X.Etale}
    [AlgebraicGeometry.IsIntegral W.left] {O : W.left.Opens} {w : W.left} (hw : w ∈ O)
    (hO : IsAffineOpen O) :
    AlgebraicGeometry.IsIntegral (etaleOpenSub W O).left ∧ IsAffine (etaleOpenSub W O).left ∧
      IsLocallyNoetherian (etaleOpenSub W O).left ∧ NoetherianSpace (etaleOpenSub W O).left := by
  have : IsAffine (etaleOpenSub W O).left := hO
  exact ⟨isIntegral_etaleOpenSub hw, hO, isLocallyNoetherian_of_etale_over_isCurve f _,
    noetherianSpace_of_etale_over_isCurve f _⟩

/-- A point of the fibre of an open subscheme over a point of `X` has image in the open. -/
private theorem mem_of_fibre_etaleOpenSub {W : X.Etale} (O : W.left.Opens) (z : X)
    (q : ↥(pullback (etaleOpenSub W O).hom (X.fromSpecResidueField z))) :
    O.ι.base ((pullback.fst (etaleOpenSub W O).hom (X.fromSpecResidueField z)).base q) ∈
      (O : Set W.left) := by
  rw [← Scheme.Opens.range_ι]
  exact Set.mem_range_self _

/-- The image in `X` of a point of the fibre of an open subscheme over `z` is `z`. -/
private theorem hom_base_fibre_etaleOpenSub {W : X.Etale} (O : W.left.Opens) (z : X)
    (q : ↥(pullback (etaleOpenSub W O).hom (X.fromSpecResidueField z))) :
    W.hom.base
        (O.ι.base ((pullback.fst (etaleOpenSub W O).hom (X.fromSpecResidueField z)).base q)) =
      z :=
  hom_base_pullback_fst_fromSpecResidueField z (etaleOpenSub W O) q


/-- **Away from the fibre over `x` a summand section at `x` restricts to zero**, so it is the
divisor of the unit function there: an affine open neighbourhood of a point not lying over `x`
misses the fibre over `x`, and the sections of `(i_x)_* 𝐙` over it are zero. -/
private theorem imageSieve_of_notMem_fibre {W : X.Etale}
    [AlgebraicGeometry.IsIntegral W.left] (x : closedPoints X)
    (β : (closedPointSkyscraper.{u, v} X x).obj.obj (op W)) {w : W.left}
    (hw : W.hom.base w ≠ x.1) :
    ∃ O : W.left.Opens, w ∈ O ∧
      Presheaf.imageSieve (closedPointDivisorMap.{u, v} fX).hom
        ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op W) β) (etaleOpenSubHom W O) := by
  have hcl : IsClosed ({x.1} : Set X) := x.2
  have hCcl : IsClosed (W.hom.base ⁻¹' ({x.1} : Set X)) :=
    hcl.preimage W.hom.base.hom.continuous
  obtain ⟨O, hOaff, hwO, hOsub⟩ := exists_isAffineOpen_mem_and_subset (X := W.left) (x := w)
    (U := ⟨(W.hom.base ⁻¹' ({x.1} : Set X))ᶜ, hCcl.isOpen_compl⟩) (by simpa using hw)
  refine ⟨O, hwO, ?_⟩
  obtain ⟨_, _, _, _⟩ := instances_etaleOpenSub fX hwO hOaff
  have : IsEmpty ↥((smallEtaleBaseChange (X.fromSpecResidueField x.1)).obj
      (etaleOpenSub W O)).left := by
    refine ⟨fun q => ?_⟩
    exact (hOsub (mem_of_fibre_etaleOpenSub (W := W) O x.1 q))
      (Set.mem_preimage.2 (Set.mem_singleton_iff.2 (hom_base_fibre_etaleOpenSub (W := W) O x.1 q)))
  have : Subsingleton ↥((closedPointSkyscraper.{u, v} X x).obj.obj
      (op (etaleOpenSub W O))) :=
    subsingleton_integerSkyscraper_obj.{u, v} x.1 (etaleOpenSub W O)
  refine imageSieve_closedPointDivisorMap_of_divisorSections_eq fX (etaleOpenSubHom W O) x β 1 ?_
  rw [Subsingleton.elim ((closedPointSkyscraper.{u, v} X x).obj.map
    (etaleOpenSubHom W O).op β) 0, map_zero]
  exact map_zero _


/-- **Near a point lying over `x` a summand section at `x` is the divisor of a rational function
pulled back from the curve.** A divisor supported at `x` is principal on a Zariski open
neighbourhood of `x` in the curve; shrinking an étale neighbourhood of the given point so that it
meets the fibre over `x` only in that point and lies over the Zariski open, the pullback of the
rational function has exactly the prescribed divisor. -/
private theorem imageSieve_of_mem_fibre {W : X.Etale}
    [AlgebraicGeometry.IsIntegral W.left] (x : closedPoints X)
    (β : (closedPointSkyscraper.{u, v} X x).obj.obj (op W)) {w : W.left}
    (hw : W.hom.base w = x.1) :
    ∃ O : W.left.Opens, w ∈ O ∧
      Presheaf.imageSieve (closedPointDivisorMap.{u, v} fX).hom
        ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op W) β) (etaleOpenSubHom W O) := by
  have hlnX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian fX
  have hlqf : LocallyQuasiFinite W.hom := (AlgebraicGeometry.locallyQuasiFinite_of_etale W.hom).2
  have : IsLocallyNoetherian W.left := isLocallyNoetherian_of_etale_over_isCurve fX W
  have hxg : x.1 ≠ genericPoint X := ne_genericPoint_of_mem_closedPoints fX x.2
  obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.hom)
    (g := X.fromSpecResidueField x.1) w
    (Classical.arbitrary ↥(Spec (X.residueField x.1)))
    (hw.trans (Scheme.fromSpecResidueField_apply _ _).symm)
  set βLC := (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x.1 W).hom β with hβLC
  obtain ⟨Vx, g, hxVx, hordx, hord0⟩ := exists_opens_ord_eq_single fX hxg (βLC p).down
  have hdisc : _root_.IsDiscrete (W.hom.base ⁻¹' ({x.1} : Set X)) :=
    W.hom.isDiscrete_preimage_singleton x.1
  obtain ⟨O₀, hO₀, hO₀eq⟩ := _root_.isDiscrete_iff_forall_mem_exists_isOpen.1 hdisc w
    (Set.mem_preimage.2 (Set.mem_singleton_iff.2 hw))
  have hwmem : w ∈ O₀ ∩ (W.hom.base ⁻¹' ({x.1} : Set X)) := by
    rw [hO₀eq]; exact Set.mem_singleton w
  have hwV : w ∈ W.hom.base ⁻¹' (Vx : Set X) :=
    Set.mem_preimage.2 (by rw [hw]; exact hxVx)
  obtain ⟨O, hOaff, hwO, hOsub⟩ := exists_isAffineOpen_mem_and_subset (X := W.left) (x := w)
    (U := ⟨O₀ ∩ W.hom.base ⁻¹' (Vx : Set X),
      hO₀.inter (Vx.isOpen.preimage W.hom.base.hom.continuous)⟩) ⟨hwmem.1, hwV⟩
  refine ⟨O, hwO, ?_⟩
  obtain ⟨_, _, _, _⟩ := instances_etaleOpenSub fX hwO hOaff
  have : IsDominant (etaleOpenSub W O).hom :=
    isDominant_of_flat (A := (etaleOpenSub W O).left) (B := X) (etaleOpenSub W O).hom
  obtain ⟨a, ha⟩ := exists_units_genericFibreToFunctionField_eq
    (X := X) (V := (etaleOpenSub W O).left) (etaleOpenSub W O).hom
    (Units.map (dominantFunctionFieldMap (X := (etaleOpenSub W O).left) (S := X)
      (etaleOpenSub W O).hom).toMonoidHom g)
  have hval : ∀ (z : X) (q : ↥(pullback (etaleOpenSub W O).hom (X.fromSpecResidueField z))),
      residueFibreOrd.{u, v} (etaleOpenSub W O) z (Additive.ofMul a) q =
        ULift.up (X.ord (g : ↥X.functionField) z) := by
    intro z q
    refine (residueFibreOrd_apply.{u, v} (etaleOpenSub W O) z (Additive.ofMul a) q).trans ?_
    refine congrArg ULift.up ?_
    refine (etaleGenericFibreOrd_eq_ord (etaleOpenSub W O) a (g : ↥X.functionField) ha _).trans ?_
    exact congrArg _ (hom_base_fibre_etaleOpenSub (W := W) O z q)
  have hmemVx : ∀ (z : X) (q : ↥(pullback (etaleOpenSub W O).hom
      (X.fromSpecResidueField z))), z ∈ (Vx : Set X) := by
    intro z q
    rw [← hom_base_fibre_etaleOpenSub (W := W) O z q]
    exact Set.mem_preimage.1 (hOsub (mem_of_fibre_etaleOpenSub (W := W) O z q)).2
  refine imageSieve_closedPointDivisorMap_of_divisorSections_eq fX (etaleOpenSubHom W O) x β a ?_
  refine DFinsupp.ext fun z => ?_
  refine (genericFibreDivisorSections_apply.{u, v} (etaleOpenSub W O) (Additive.ofMul a) z).trans ?_
  have hleft : integerSkyscraperDivisor.{u, v} (etaleOpenSub W O) z.1 (Additive.ofMul a) =
      (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X z.1
        (etaleOpenSub W O)).inv
        (residueFibreOrd.{u, v} (etaleOpenSub W O) z.1 (Additive.ofMul a)) := rfl
  by_cases hz : z = x
  · subst hz
    have hq : ∀ q : ↥(pullback (etaleOpenSub W O).hom (X.fromSpecResidueField z.1)),
        ((smallEtaleBaseChange (X.fromSpecResidueField z.1)).map
          (etaleOpenSubHom W O)).left.base q = p := by
      intro q
      refine injective_base_pullback_fst_fromSpecResidueField z.1 W ?_
      refine Eq.trans (congrArg
        (fun φ : pullback (etaleOpenSub W O).hom (X.fromSpecResidueField z.1) ⟶ W.left =>
          φ.base q) (smallEtaleBaseChange_map_left_comp_fst (X.fromSpecResidueField z.1)
            (etaleOpenSubHom W O))) ?_
      have h2 : O.ι.base ((pullback.fst (etaleOpenSub W O).hom
          (X.fromSpecResidueField z.1)).base q) ∈ O₀ ∩ (W.hom.base ⁻¹' ({z.1} : Set X)) :=
        ⟨(hOsub (mem_of_fibre_etaleOpenSub (W := W) O z.1 q)).1,
          Set.mem_preimage.2 (Set.mem_singleton_iff.2
            (hom_base_fibre_etaleOpenSub (W := W) O z.1 q))⟩
      rw [hO₀eq] at h2
      exact (Set.mem_singleton_iff.1 h2).trans hp.symm
    refine Eq.trans ?_ (DirectSum.of_eq_same (β := fun y : closedPoints X =>
      ((closedPointSkyscraper.{u, v} X y).obj.obj (op (etaleOpenSub W O)) : Type _)) z
      ((closedPointSkyscraper.{u, v} X z).obj.map (etaleOpenSubHom W O).op β)).symm
    refine hleft.trans ?_
    refine Eq.trans ?_ (integerSkyscraper_map_eq (etaleOpenSubHom W O) z.1 β).symm
    refine congrArg _ (LocallyConstant.ext fun q => ?_)
    refine Eq.trans (((hval z.1 q).trans (congrArg ULift.up hordx)).trans
      (ULift.up_down (βLC p))) ?_
    refine Eq.trans ?_ (LocallyConstant.coe_comap_apply _ βLC q).symm
    exact congrArg βLC (hq q).symm
  · refine Eq.trans ?_ (DirectSum.of_eq_of_ne (β := fun y : closedPoints X =>
      ((closedPointSkyscraper.{u, v} X y).obj.obj (op (etaleOpenSub W O)) : Type _)) x z
      ((closedPointSkyscraper.{u, v} X x).obj.map (etaleOpenSubHom W O).op β) hz).symm
    refine hleft.trans ?_
    refine Eq.trans (congrArg _ (LocallyConstant.ext fun q => ?_)) (map_zero _)
    exact (hval z.1 q).trans (congrArg ULift.up
      (hord0 z.1 (hmemVx z.1 q) (fun h => hz (Subtype.ext h))))


/-! ### Local surjectivity on each summand, and surjectivity -/

/-- **A summand section of the third term of the fundamental exact sequence is, near any point of
an irreducible étale `X`-scheme, the divisor of an invertible function on the generic fibre.** -/
theorem exists_open_imageSieve_closedPointDivisorMap {W : X.Etale}
    [AlgebraicGeometry.IsIntegral W.left] (x : closedPoints X)
    (β : (closedPointSkyscraper.{u, v} X x).obj.obj (op W)) (w : W.left) :
    ∃ O : W.left.Opens, w ∈ O ∧
      Presheaf.imageSieve (closedPointDivisorMap.{u, v} fX).hom
        ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op W) β) (etaleOpenSubHom W O) := by
  by_cases hw : W.hom.base w = x.1
  · exact imageSieve_of_mem_fibre fX x β hw
  · exact imageSieve_of_notMem_fibre fX x β hw

/-- **A summand section of the third term is locally in the image of the second map, over an
irreducible étale `X`-scheme.** The affine open neighbourhoods produced by
`Stacks.EtaleCohomology.exists_open_imageSieve_closedPointDivisorMap` cover. -/
theorem imageSieve_closedPointDivisorMap_ι_mem_of_isIntegral {W : X.Etale}
    [AlgebraicGeometry.IsIntegral W.left] (x : closedPoints X)
    (β : (closedPointSkyscraper.{u, v} X x).obj.obj (op W)) :
    Presheaf.imageSieve (closedPointDivisorMap.{u, v} fX).hom
      ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op W) β) ∈ X.smallEtaleTopology W := by
  choose O hO him using exists_open_imageSieve_closedPointDivisorMap fX x β
  refine X.smallEtaleTopology.superset_covering ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff
      (fun w : W.left => etaleOpenSubHom W (O w))).mpr ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro V - ⟨w⟩
    exact him w
  · ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨y, ⟨y, hO y⟩, rfl⟩

/-- **A summand section of the third term is locally in the image of the second map**, over an
arbitrary étale `X`-scheme: the irreducible objects are cover-dense, and a summand section
restricts to a summand section. -/
theorem imageSieve_closedPointDivisorMap_ι_mem (U : X.Etale) (x : closedPoints X)
    (β : (closedPointSkyscraper.{u, v} X x).obj.obj (op U)) :
    Presheaf.imageSieve (closedPointDivisorMap.{u, v} fX).hom
      ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op U) β) ∈ X.smallEtaleTopology U := by
  have : IsNormal X := isNormal_of_smooth_isCurve fX
  refine X.smallEtaleTopology.transitive
    ((isIntegralEtale X).ι.is_cover_of_isCoverDense X.smallEtaleTopology U) _ ?_
  intro V f hf
  obtain ⟨⟨Z, lift, map, fac⟩⟩ := hf
  have : AlgebraicGeometry.IsIntegral ((isIntegralEtale X).ι.obj Z).left := Z.property
  rw [← fac, Sieve.pullback_comp]
  refine X.smallEtaleTopology.pullback_stable lift ?_
  rw [Presheaf.pullback_imageSieve]
  have hnat : (closedPointDivisorSheaf.ι.{u, v} X x).hom.app
        (op ((isIntegralEtale X).ι.obj Z))
        ((closedPointSkyscraper.{u, v} X x).obj.map map.op β) =
      (closedPointDivisorSheaf.{u, v} X).obj.map map.op
        ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op U) β) :=
    ConcreteCategory.congr_hom
      ((closedPointDivisorSheaf.ι.{u, v} X x).hom.naturality map.op) β
  rw [← hnat]
  exact imageSieve_closedPointDivisorMap_ι_mem_of_isIntegral fX x _

/-- The summand inclusions of `⨁_x (i_x)_* 𝐙` are jointly epimorphic. -/
theorem closedPointDivisorSheaf.hom_ext
    {T : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (k₁ k₂ : closedPointDivisorSheaf.{u, v} X ⟶ T)
    (hk : ∀ x : closedPoints X, closedPointDivisorSheaf.ι.{u, v} X x ≫ k₁ =
      closedPointDivisorSheaf.ι.{u, v} X x ≫ k₂) : k₁ = k₂ :=
  Sigma.hom_ext k₁ k₂ hk

/-- **The second map of the fundamental exact sequence of Stacks 03RI is an epimorphism of étale
sheaves**: a divisor on a nonsingular curve is étale-locally the divisor of a rational function.

A morphism out of `⨁_x (i_x)_* 𝐙` vanishing on the image of the divisor map vanishes on every
summand, because a summand section is locally in that image and the target is a sheaf; and the
summand inclusions are jointly epimorphic. -/
theorem epi_closedPointDivisorMap : Epi (closedPointDivisorMap.{u, v} fX) := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro T h hdh
  have hz : ∀ (x : closedPoints X) (U : X.Etaleᵒᵖ)
      (β : (closedPointSkyscraper.{u, v} X x).obj.obj U),
      h.hom.app U ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app U β) = 0 := by
    intro x U β
    refine T.isSeparated _ _ (imageSieve_closedPointDivisorMap_ι_mem fX U.unop x β) _ 0 ?_
    intro V f hf
    obtain ⟨a, ha⟩ := hf
    have h1 : T.obj.map f.op (h.hom.app U
          ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app U β)) =
        h.hom.app (op V) ((closedPointDivisorSheaf.{u, v} X).obj.map f.op
          ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app U β)) :=
      (ConcreteCategory.congr_hom (h.hom.naturality f.op) _).symm
    have h3 := congrArg (fun φ : (genericPointDirectImage.{u, v} X).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField)) ⟶ T =>
      φ.hom.app (op V) a) hdh
    have h4 : h.hom.app (op V) ((closedPointDivisorMap.{u, v} fX).hom.app (op V) a) = 0 := by
      refine h3.trans ?_
      simp
    rw [h1, ← ha, h4, map_zero]
  refine closedPointDivisorSheaf.hom_ext h 0 fun x => ?_
  rw [Limits.comp_zero]
  refine Sheaf.hom_ext ?_
  ext U β
  refine (hz x U β).trans ?_
  simp

end Local

end Stacks.EtaleCohomology

end
