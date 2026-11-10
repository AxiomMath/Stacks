module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerAffineSpaceClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFunctionPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurity
public import StacksFrontier.AlgebraicGeometry.Blowup.SmoothCentre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.GysinGoodness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurityGluing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.EtaleNeighbourhoodExcision
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeFour.ClosedImmersionBaseChangeOffImage

/-!
# The Kummer flag class of the coordinates of affine space is nonzero

Let `K` be algebraically closed, `ℓ` a prime invertible in `K` and `ζ` a primitive `ℓ`-th root of
unity. On `𝔸^d_K` consider the flag of the divisor data of the coordinates in the order
`x_{d-1}, …, x_0` (`Stacks.EtaleCohomology.KummerFlag.stdDatum`), each with its zero locus the
fibre of the coordinate over the origin of `𝔸¹_K`. Its Kummer flag class is nonzero
(`kummerFlagClass_stdDatum_ne_zero`).

The proof is by induction on `d`, along the hyperplane `x_{d-1} = 0`:

* a nonzero class of degree `c` along a closed immersion with connected source which has some
  purity class of degree `c` is itself a purity class (`isPurityClassFun_of_ne_zero`): the two
  differ by a scalar, `End(Λ_T) = ℤ/ℓ` being a field;
* the divisor class of `x_{d-1}` is nonzero (`H¹(𝔸^d, ℤ/ℓ) = 0` and `x_{d-1}` is not an `ℓ`-th
  power on `D(x_{d-1})`, `Stacks.EtaleCohomology.KummerFlag.kummerDivisorClass_ne_zero`), and the
  fibre of `x_{d-1}` has a purity class of degree `2`
  (`Stacks.EtaleCohomology.Purity.exists_ext_purity_principalDivisor`), so the divisor class is a
  purity class: its Gysin map is injective;
* the restriction of the remaining flag class to the hyperplane `𝔸^{d-1}` is the flag class of
  the coordinates of `𝔸^{d-1}` (`exists_kummerFlagClass_ofFunction_eq`, from
  `Stacks.EtaleCohomology.KummerFlag.transport_kummerFlagClass`), nonzero by induction.

## Main definitions

* `Stacks.EtaleCohomology.KummerFlag.coordProj`: the coordinate projections `𝔸^n_K ⟶ 𝔸¹_K`.
* `Stacks.EtaleCohomology.KummerFlag.DivisorDatum.ofIsPullback`
* `Stacks.EtaleCohomology.KummerFlag.stdDatum`

## Main results

* `Stacks.EtaleCohomology.KummerFlag.exists_kummerFlagClass_ofFunction_eq`
* `Stacks.EtaleCohomology.KummerFlag.isPurityClassFun_of_ne_zero`
* `Stacks.EtaleCohomology.KummerFlag.kummerFlagClass_stdDatum_ne_zero`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.ExtTransport

universe u

namespace Stacks.EtaleCohomology.KummerFlag

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

section Transport

variable {k : Type u} [Field k] {N : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k))
  {X X' : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fX' : X' ⟶ Spec (.of k)) (g : X' ⟶ X)
  (hg : g ≫ fX = fX') {d : ℕ} (f : Fin d → Γ(X, ⊤)) {W : Fin d → Scheme.{u}}
  (i : ∀ m, W m ⟶ X) [∀ m, IsClosedImmersion (i m)]
  (hi : ∀ m, Set.range (X.basicOpen (f m)).ι.base = (Set.range (i m).base)ᶜ)
  (f' : Fin d → Γ(X', ⊤)) {W' : Fin d → Scheme.{u}} (i' : ∀ m, W' m ⟶ X')
  [∀ m, IsClosedImmersion (i' m)]
  (hi' : ∀ m, Set.range (X'.basicOpen (f' m)).ι.base = (Set.range (i' m).base)ᶜ)
  (hf : ∀ m, g.appTop (f m) = f' m) (gW : ∀ m, W' m ⟶ W m) (hW : ∀ m, i' m ≫ g = gW m ≫ i m)

include hζ hg hf hW in
/-- **The Kummer flag class of functions is natural**: if `g^♯ f_m = f'_m` and `g` maps the
closed parts into each other, the Kummer flag class of the `f'_m` is the inverse image of that of
the `f_m`, read through isomorphisms. -/
theorem exists_kummerFlagClass_ofFunction_eq [NeZero N]
    (hpc : ∀ m, PreconnectedSpace (X'.basicOpen (f' m))) :
    ∃ (a : flagSheaf (N := N) (fun m => DivisorDatum.ofFunction (f' m) (i' m) (hi' m)) ⟶
        (etaleModuleInverseImage.{u, 0} (ZMod N) g).obj
          (flagSheaf (N := N) (fun m => DivisorDatum.ofFunction (f m) (i m) (hi m))))
      (b : (etaleModuleInverseImage.{u, 0} (ZMod N) g).obj (unitSheaf (X := X) N) ⟶
        unitSheaf (X := X') N),
      IsIso a ∧ IsIso b ∧
      kummerFlagClass hζ hN fX' (fun m => DivisorDatum.ofFunction (f' m) (i' m) (hi' m)) =
        transport (etaleModuleInverseImage.{u, 0} (ZMod N) g) a b (2 * d)
          (kummerFlagClass hζ hN fX (fun m => DivisorDatum.ofFunction (f m) (i m) (hi m))) := by
  have hle : ∀ m, X'.basicOpen (f' m) ≤ g ⁻¹ᵁ X.basicOpen (f m) := fun m => by
    rw [Scheme.preimage_basicOpen_top, hf m]
  let gV : ∀ m, (DivisorDatum.ofFunction (f' m) (i' m) (hi' m)).V ⟶
      (DivisorDatum.ofFunction (f m) (i m) (hi m)).V := fun m => g.resLE _ _ (hle m)
  have hV : ∀ m, (DivisorDatum.ofFunction (f' m) (i' m) (hi' m)).j ≫ g =
      gV m ≫ (DivisorDatum.ofFunction (f m) (i m) (hi m)).j :=
    fun m => (Scheme.Hom.resLE_comp_ι _ _).symm
  have ha : ∀ m, Units.map (gV m).appTop.hom (DivisorDatum.ofFunction (f m) (i m) (hi m)).a =
      (DivisorDatum.ofFunction (f' m) (i' m) (hi' m)).a ^ 1 := by
    intro m
    rw [pow_one]
    ext
    change (gV m).appTop ((X.basicOpen (f m)).ι.appTop (f m)) =
      (X'.basicOpen (f' m)).ι.appTop (f' m)
    have h := congrArg (fun φ => φ.appTop (f m)) (hV m)
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf m] at h
    exact h.symm
  have : ∀ m, PreconnectedSpace (DivisorDatum.ofFunction (f' m) (i' m) (hi' m)).V := hpc
  have h := transport_kummerFlagClass hζ hN fX fX' g hg 1
    (fun m => DivisorDatum.ofFunction (f m) (i m) (hi m))
    (fun m => DivisorDatum.ofFunction (f' m) (i' m) (hi' m)) gV hV gW hW ha
  rw [kummerFlagClassPow_one] at h
  exact ⟨(flagSheafIso N g _ _ gV hV gW hW).hom, (constantInverseImageIso (ZMod N) g).inv,
    inferInstance, inferInstance, h.symm⟩

end Transport

section Coordinates

variable (K : Type u) [Field K]

/-- The `j`-th coordinate `𝔸^n_K ⟶ 𝔸¹_K`. -/
def coordProj {n : ℕ} (j : ULift.{u} (Fin n)) :
    𝔸(ULift.{u} (Fin n); Spec (.of K)) ⟶ Purity.affineLine K :=
  AffineSpace.reindex (fun _ : ULift.{u} (Fin 1) => j) (Spec (.of K))

/-- `coordProj K j` pulls the coordinate of `𝔸¹_K` back to the `j`-th coordinate. -/
theorem coordProj_appTop_coordinate {n : ℕ} (j : ULift.{u} (Fin n)) :
    (coordProj K j).appTop (Purity.coordinate K) = AffineSpace.coord (Spec (.of K)) j :=
  AffineSpace.reindex_appTop_coord _ _ _

/-- `coordProj K j` is a morphism over `Spec K`. -/
theorem coordProj_over {n : ℕ} (j : ULift.{u} (Fin n)) :
    coordProj K j ≫ (Purity.affineLine K ↘ Spec (.of K)) =
      𝔸(ULift.{u} (Fin n); Spec (.of K)) ↘ Spec (.of K) :=
  AffineSpace.reindex_over _ _

/-- The last coordinate projection of `Stacks.EtaleCohomology.Purity` is `coordProj` at the last
index. -/
theorem lastCoordinateProjection_eq (M : ℕ) :
    Purity.lastCoordinateProjection K M = coordProj K ⟨Fin.last M⟩ := by
  have hover : (Stacks.Chow.affineSpaceSuccIso (Spec (.of K)) M).hom ≫
      (𝔸(ULift.{u} (Fin M); Purity.affineLine K) ↘ Purity.affineLine K) =
        AffineSpace.reindex ((Stacks.Chow.uliftFinSuccSumEquiv.{u} M).symm ∘ Sum.inr)
          (Spec (.of K)) := by
    rw [Stacks.Chow.affineSpaceSuccIso, Iso.trans_hom, Category.assoc,
      Stacks.Chow.affineSpaceSumIso_hom_over]
    exact Stacks.Chow.affineSpace_reindex_comp _ _ _
  rw [Purity.lastCoordinateProjection, hover, coordProj]
  congr 1
  funext x
  obtain ⟨x⟩ := x
  obtain rfl : x = 0 := Subsingleton.elim _ _
  rfl

/-- The last coordinate projection is smooth. -/
instance smooth_coordProj_last (M : ℕ) : Smooth (coordProj K ⟨Fin.last M⟩) := by
  rw [← lastCoordinateProjection_eq]
  infer_instance

/-- The coordinate hyperplane `𝔸^M ⊆ 𝔸^{M+1}` keeps the first `M` coordinates. -/
theorem coordinateSubspaceEmbedding_comp_coordProj (M : ℕ) (j : Fin M) :
    Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding (Spec (.of K)) M 1 ≫
      coordProj K ⟨j.castSucc⟩ = coordProj K ⟨j⟩ := by
  ext1
  · rw [Category.assoc, coordProj_over, coordProj_over]
    exact Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_over _ M 1
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coordProj, coordProj,
      AffineSpace.reindex_appTop_coord, AffineSpace.reindex_appTop_coord]
    exact Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_firstCoordinate _ M 1 j

/-- The basic open of `φ^♯ t` is the complement of the fibre of `φ` over the origin. -/
theorem range_basicOpen_ι_eq_compl_of_isPullback {X W : Scheme.{u}}
    (φ : X ⟶ Purity.affineLine K) (i : W ⟶ X) (p : W ⟶ Spec (.of K))
    (h : IsPullback i p φ (Purity.origin K)) :
    Set.range (X.basicOpen (φ.appTop (Purity.coordinate K))).ι.base = (Set.range i.base)ᶜ := by
  rw [Stacks.Cohomology.ClosedImmersionBaseChange.range_eq_preimage_range_of_isPullback h,
    Purity.range_origin, Set.preimage_compl,
    compl_compl, ← Scheme.preimage_basicOpen_top]
  change Set.range (φ ⁻¹ᵁ (Purity.punctured K)).ι = _
  rw [Scheme.Opens.range_ι]
  rfl

/-- **The divisor datum of a morphism to the affine line**, with a chosen fibre over the
origin: the basic open of `φ^♯ t` with the unit `φ^♯ t`, and the fibre `W`. -/
def DivisorDatum.ofIsPullback {X W : Scheme.{u}} (φ : X ⟶ Purity.affineLine K) (i : W ⟶ X)
    (p : W ⟶ Spec (.of K)) (h : IsPullback i p φ (Purity.origin K)) : DivisorDatum X :=
  haveI := Purity.isClosedImmersion_origin K
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback h.flip inferInstance
  DivisorDatum.ofFunction (φ.appTop (Purity.coordinate K)) i
    (range_basicOpen_ι_eq_compl_of_isPullback K φ i p h)

/-- The function `x_{d-1-m}` of the standard flag on `𝔸^d_K`. -/
abbrev stdFun (d : ℕ) (m : Fin d) : Γ(𝔸(ULift.{u} (Fin d); Spec (.of K)), ⊤) :=
  (coordProj K ⟨m.rev⟩).appTop (Purity.coordinate K)

/-- The closed part of the standard flag: the fibre of `x_{d-1-m}` over the origin. -/
abbrev stdW (d : ℕ) (m : Fin d) : Scheme.{u} := pullback (coordProj K ⟨m.rev⟩) (Purity.origin K)

/-- The closed immersion of the fibre of `x_{d-1-m}` over the origin. -/
abbrev stdι (d : ℕ) (m : Fin d) : stdW K d m ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of K)) :=
  pullback.fst _ _

/-- The fibre of a coordinate over the origin is a closed subscheme. -/
instance (d : ℕ) (m : Fin d) : IsClosedImmersion (stdι K d m) := by
  have := Purity.isClosedImmersion_origin K
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance

/-- The basic open of `x_{d-1-m}` is the complement of its fibre over the origin. -/
theorem stdRange (d : ℕ) (m : Fin d) :
    Set.range ((𝔸(ULift.{u} (Fin d); Spec (.of K))).basicOpen (stdFun K d m)).ι.base =
      (Set.range (stdι K d m).base)ᶜ :=
  range_basicOpen_ι_eq_compl_of_isPullback K _ _ _ (IsPullback.of_hasPullback _ _)

/-- **The standard flag on `𝔸^d_K`**: the divisor data of the coordinates `x_{d-1}, …, x_0`, in
this order, each with the fibre over the origin as closed part. -/
abbrev stdDatum (d : ℕ) (m : Fin d) : DivisorDatum 𝔸(ULift.{u} (Fin d); Spec (.of K)) :=
  DivisorDatum.ofFunction (stdFun K d m) (stdι K d m) (stdRange K d m)

end Coordinates

section Rigidity

attribute [local instance] moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **A nonzero class is a purity class**, for a closed part with irreducible source which has
some purity class of the same degree: the two differ by a scalar of the field `ℤ/ℓ`. -/
theorem isPurityClassFun_of_ne_zero {T Y : Scheme.{u}}
    {P : EtaleModules.{u, 0} (ZMod ℓ) T ⥤ EtaleModules.{u, 0} (ZMod ℓ) Y} [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] {A : EtaleModules.{u, 0} (ZMod ℓ) Y}
    {c : ℕ} {γ γ' : Ext (P.obj (unitSheaf (X := T) ℓ)) A c}
    (hγ : Purity.IsPurityClassFun ℓ P A γ) [IrreducibleSpace T] (hγ' : γ' ≠ 0) :
    Purity.IsPurityClassFun ℓ P A γ' := by
  obtain ⟨u, hu⟩ := (hγ.1 (unitSheaf (X := T) ℓ) 0 c (zero_add c)).2 γ'
  obtain ⟨v, rfl⟩ := (Ext.mk₀_bijective _ _).2 u
  obtain ⟨r, rfl⟩ := Purity.exists_eq_smul_id_unitSheaf T v
  simp only [Ext.mapExactFunctor_mk₀] at hu
  have hr : r ≠ 0 := by
    rintro rfl
    apply hγ'
    rw [← hu, zero_smul, P.map_zero, Ext.mk₀_zero, Ext.zero_comp]
  subst hu
  refine ⟨fun G q q' h => ?_, hγ.2⟩
  exact ((Purity.Gysin.isGoodAt_comp_mk₀_iff P γ (r • 𝟙 (unitSheaf (X := T) ℓ)) G
    (fun q => Purity.Gysin.bijective_comp_mk₀_smul_id r hr.isUnit q)).2
    ⟨fun q q' h => hγ.1 G q q' h, fun q hq => hγ.2 G q hq⟩).1 q q' h

/-- A class whose inverse image along `θ ≫ i` is nonzero has nonzero inverse image along `i`. -/
private theorem mapExactFunctor_inverseImage_ne_zero_of_comp {Y W X : Scheme.{u}} (θ : Y ⟶ W)
    (i : W ⟶ X) {F G : EtaleModules.{u, 0} (ZMod ℓ) X} {q : ℕ} (x : Ext F G q)
    (hx : x.mapExactFunctor (etaleModuleInverseImage.{u, 0} (ZMod ℓ) (θ ≫ i)) ≠ 0) :
    x.mapExactFunctor (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i) ≠ 0 := by
  intro hy
  apply hx
  let e := etaleModuleInverseImageCompIso.{u, 0} (ZMod ℓ) θ i
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor e.inv F q x
  rw [← Stacks.ExtFunctorial.mapExactFunctor_comp_functor, hy, Ext.mapExactFunctor_zero,
    Ext.zero_comp] at key
  apply (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (e.inv.app F) q).1
  change (Ext.mk₀ (e.inv.app F)).comp _ (zero_add _) = (Ext.mk₀ (e.inv.app F)).comp 0 (zero_add _)
  rw [key, Ext.comp_zero]

private theorem mk₀_directImage_map_inv_comp_hom_comp {X W : Scheme.{u}} (i : W ⟶ X)
    {A B : EtaleModules.{u, 0} (ZMod ℓ) W} (e : A ≅ B) {Z : EtaleModules.{u, 0} (ZMod ℓ) X}
    {k : ℕ} (δ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj B) Z k) :
    (Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).map e.inv)).comp
      ((Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).map e.hom)).comp δ (zero_add k))
        (zero_add k) = δ := by
  rw [Ext.mk₀_comp_mk₀_assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Ext.mk₀_id_comp]

/-- A class `x` with nonzero inverse image to `W` stays nonzero after the closed restriction to `W`
followed by a class `δ` which is, through an isomorphism `Λ_W ≅ i⁻¹ Λ_X`, a purity class. -/
private theorem comp_ne_zero_of_isPurityClassFun {X W : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] {F : EtaleModules.{u, 0} (ZMod ℓ) X} {q q' : ℕ}
    (x : Ext F (unitSheaf (X := X) ℓ) q)
    (e : unitSheaf (X := W) ℓ ≅ (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf ℓ))
    (δ : Ext ((closedRestriction (N := ℓ) i).obj (unitSheaf ℓ)) (unitSheaf (X := X) ℓ) 2)
    (hδ : Purity.IsPurityClassFun ℓ (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)
      (unitSheaf (X := X) ℓ)
      ((Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).map e.hom)).comp δ (zero_add 2)))
    (hx : x.mapExactFunctor (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i) ≠ 0) (h : q + 2 = q') :
    (x.mapExactFunctor (closedRestriction (N := ℓ) i)).comp δ h ≠ 0 := by
  intro h0
  rw [← Stacks.ExtFunctorial.mapExactFunctor_comp_functor _ _ _ _ x] at h0
  apply hx
  apply (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso e.inv q).1
  change (x.mapExactFunctor _).comp (Ext.mk₀ e.inv) (add_zero _) =
    (0 : Ext _ _ q).comp (Ext.mk₀ e.inv) (add_zero _)
  rw [Ext.zero_comp]
  apply (hδ.1 _ q q' h).1
  beta_reduce
  rw [Ext.mapExactFunctor_zero, Ext.zero_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc _ _ _ (add_zero _) (zero_add 2) (by omega),
    mk₀_directImage_map_inv_comp_hom_comp i e δ]
  exact h0

end Rigidity

section AffineSpaceFlag

attribute [local instance] moduleCat_hasLimitsOfSize

variable {K : Type u} [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] {ζ : K}
  (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : IsUnit (ℓ : K))

/-- The divisor class of the last coordinate of `𝔸^{n+1}_K` is nonzero. -/
theorem kummerDivisorClass_stdDatum_zero_ne_zero (n : ℕ) :
    kummerDivisorClass hζ hℓ (𝔸(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K))
      (stdDatum K (n + 1) 0).j (stdDatum K (n + 1) 0).i (stdDatum K (n + 1) 0).range_eq
      (stdDatum K (n + 1) 0).a ≠ 0 := by
  have hp : ℓ.Prime := Fact.out
  refine kummerDivisorClass_ne_zero hζ hℓ _ _ _ _
    (subsingleton_ext_one_unitSheaf_affineSpace K (n + 1) hζ hℓ) _ ?_
  refine kummerUnitClass_ne_zero_of_not_exists_pow hζ hℓ _ _ ?_
  have hf : stdFun K (n + 1) 0 = AffineSpace.coord (Spec (.of K)) ⟨(0 : Fin (n + 1)).rev⟩ :=
    coordProj_appTop_coordinate K _
  have hprime : Prime (stdFun K (n + 1) 0) := by
    rw [hf]
    exact prime_affineSpace_coord K (n + 1) _
  exact not_exists_pow_eq_unit_basicOpen hprime hp.one_lt
    (exists_pow_eq_units_affineSpace K (n + 1) hp.pos)

omit [IsAlgClosed K] in
/-- The remaining flag class of `𝔸^{n+1}_K` restricts to a nonzero class on the hyperplane
`𝔸^n_K`, if the flag class of `𝔸^n_K` is nonzero. -/
private theorem mapExactFunctor_coordinateSubspaceEmbedding_ne_zero (n : ℕ)
    (IH : kummerFlagClass hζ hℓ (𝔸(ULift.{u} (Fin n); Spec (.of K)) ↘ Spec (.of K))
      (stdDatum K n) ≠ 0) :
    (kummerFlagClass hζ hℓ (𝔸(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K))
      (fun m : Fin n => stdDatum K (n + 1) m.succ)).mapExactFunctor
        (etaleModuleInverseImage.{u, 0} (ZMod ℓ)
          (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding (Spec (.of K)) n 1)) ≠ 0 := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have := Purity.isClosedImmersion_origin K
  let h0 := Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding (Spec (.of K)) n 1
  let x := kummerFlagClass hζ hℓ (𝔸(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K))
    (fun m : Fin n => stdDatum K (n + 1) m.succ)
  have hcomp : ∀ m : Fin n, h0 ≫ coordProj K ⟨m.succ.rev⟩ = coordProj K ⟨m.rev⟩ := fun m => by
    rw [Fin.rev_succ]
    exact coordinateSubspaceEmbedding_comp_coordProj K n m.rev
  obtain ⟨a, b, -, -, htr⟩ := exists_kummerFlagClass_ofFunction_eq hζ hℓ
    (𝔸(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K))
    (𝔸(ULift.{u} (Fin n); Spec (.of K)) ↘ Spec (.of K)) h0
    (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_over _ n 1)
    (fun m : Fin n => stdFun K (n + 1) m.succ) (fun m => stdι K (n + 1) m.succ)
    (fun m => stdRange K (n + 1) m.succ)
    (fun m : Fin n => stdFun K n m) (fun m => stdι K n m) (fun m => stdRange K n m)
    (fun m => by
      change h0.appTop ((coordProj K ⟨m.succ.rev⟩).appTop (Purity.coordinate K)) =
        (coordProj K ⟨m.rev⟩).appTop (Purity.coordinate K)
      rw [← hcomp m, Scheme.Hom.comp_appTop, CommRingCat.comp_apply])
    (fun m => pullback.lift (pullback.fst _ _ ≫ h0) (pullback.snd _ _)
      (by rw [Category.assoc, hcomp m, pullback.condition]))
    (fun m => (pullback.lift_fst _ _ _).symm)
    (fun m => preconnectedSpace_basicOpen _)
  have htr' : kummerFlagClass hζ hℓ (𝔸(ULift.{u} (Fin n); Spec (.of K)) ↘ Spec (.of K))
      (stdDatum K n) = transport (etaleModuleInverseImage.{u, 0} (ZMod ℓ) h0) a b (2 * n) x :=
    htr
  intro h
  change x.mapExactFunctor (etaleModuleInverseImage.{u, 0} (ZMod ℓ) h0) = 0 at h
  apply IH
  rw [htr', transport_apply, h, map_zero]

/-- **The Kummer flag class of the coordinates of `𝔸^d_K` is nonzero.** -/
theorem kummerFlagClass_stdDatum_ne_zero : ∀ d : ℕ,
    kummerFlagClass hζ hℓ (𝔸(ULift.{u} (Fin d); Spec (.of K)) ↘ Spec (.of K)) (stdDatum K d) ≠ 0
  | 0 => by
    have : Fact (1 < ℓ) := ⟨(Fact.out : ℓ.Prime).one_lt⟩
    intro h
    apply id_unitSheaf_ne_zero (N := ℓ) 𝔸(ULift.{u} (Fin 0); Spec (.of K))
    apply (Ext.mk₀_bijective _ _).1
    rwa [Ext.mk₀_zero]
  | n + 1 => by
    have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    have := Purity.isClosedImmersion_origin K
    let h0 := Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding (Spec (.of K)) n 1
    let x := kummerFlagClass hζ hℓ (𝔸(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K))
      (fun m : Fin n => stdDatum K (n + 1) m.succ)
    have hx : x.mapExactFunctor (etaleModuleInverseImage.{u, 0} (ZMod ℓ) h0) ≠ 0 :=
      mapExactFunctor_coordinateSubspaceEmbedding_ne_zero hζ hℓ n
        (kummerFlagClass_stdDatum_ne_zero n)
    have hφ0 : coordProj K ⟨(0 : Fin (n + 1)).rev⟩ = Purity.lastCoordinateProjection K n := by
      rw [lastCoordinateProjection_eq, Fin.rev_zero]
    have hpbH : IsPullback h0 (𝔸(ULift.{u} (Fin n); Spec (.of K)) ↘ Spec (.of K))
        (coordProj K ⟨(0 : Fin (n + 1)).rev⟩) (Purity.origin K) := by
      rw [hφ0]
      exact Purity.isPullback_coordinateSubspaceEmbedding_one K n
    let θ : 𝔸(ULift.{u} (Fin n); Spec (.of K)) ⟶ (stdDatum K (n + 1) 0).W :=
      hpbH.isoPullback.hom
    have hθ : θ ≫ (stdDatum K (n + 1) 0).i = h0 := hpbH.isoPullback_hom_fst
    have hsmooth : Smooth (coordProj K ⟨(0 : Fin (n + 1)).rev⟩) := by
      rw [hφ0]
      infer_instance
    obtain ⟨γ, hγ₁, hγ₂⟩ := Purity.exists_ext_purity_principalDivisor hℓ
      (coordProj K ⟨(0 : Fin (n + 1)).rev⟩) (stdDatum K (n + 1) 0).i (pullback.snd _ _)
      (IsPullback.of_hasPullback _ _)
    have hγ := Purity.isPurityClassFun_of_rfl _ _ γ hγ₁ hγ₂
    have : IsIso θ := inferInstanceAs (IsIso hpbH.isoPullback.hom)
    have : IrreducibleSpace (stdDatum K (n + 1) 0).W :=
      Function.Surjective.irreducibleSpace θ.continuous θ.surjective
    let c := constantInverseImageIso (ZMod ℓ) (stdDatum K (n + 1) 0).i
    let δ0 := kummerDivisorClass hζ hℓ (𝔸(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K))
      (stdDatum K (n + 1) 0).j (stdDatum K (n + 1) 0).i (stdDatum K (n + 1) 0).range_eq
      (stdDatum K (n + 1) 0).a
    have hδ0 : (Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod ℓ)
        (stdDatum K (n + 1) 0).i).map c.hom)).comp δ0 (zero_add 2) ≠ 0 := by
      intro h
      apply kummerDivisorClass_stdDatum_zero_ne_zero hζ hℓ n
      change δ0 = 0
      rw [← mk₀_directImage_map_inv_comp_hom_comp (stdDatum K (n + 1) 0).i c δ0, h, Ext.comp_zero]
    exact comp_ne_zero_of_isPurityClassFun (stdDatum K (n + 1) 0).i x c δ0
      (isPurityClassFun_of_ne_zero hγ hδ0)
      (mapExactFunctor_inverseImage_ne_zero_of_comp θ _ x (by rwa [hθ]))
      (show 2 * n + 2 = 2 * (n + 1) by ring)

end AffineSpaceFlag

end Stacks.EtaleCohomology.KummerFlag

end
