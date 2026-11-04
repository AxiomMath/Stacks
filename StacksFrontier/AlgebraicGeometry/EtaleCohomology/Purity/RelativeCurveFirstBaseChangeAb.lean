module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerChartSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.BaseChangeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveHigherVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagAffineSpace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModuleLocallyConstant

/-!
# The degree-one base change map along an étale divisor of a smooth relative curve

Let `W` be smooth over a field `k`, `g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a
closed immersion with `Z ⟶ W` étale, `j : U₀ ⟶ U` the open complement of `Z` and `N` invertible
in `k`. Let `W' ⟶ W` be a morphism with `W'` smooth over a field `k'`, `U' = U ×_W W'` and
`U₀' = U₀ ×_U U'`. For every locally constant sheaf `H` of finite type of `ℤ/N`-modules on `U`,
the degree-one base change map `u'⁻¹ R¹ j_*(j⁻¹ H) ⟶ R¹ j'_*(u₀⁻¹ j⁻¹ H)` of the underlying
abelian sheaves is an isomorphism
(`Stacks.EtaleCohomology.Purity.isIso_higherBaseChangeMapAb_one_of_relativeCurve`).

Isomorphisms are étale local
(`Stacks.EtaleCohomology.isIso_of_forall_exists_isIso_smallEtalePullbackAb`). Over `U₀'` both sides
vanish. Around a point of `U'` over `Z`, choose a chart `V ⊆ U` with `π : V ⟶ 𝔸¹_W` étale and
`Z ∩ V` the fibre of `V ⟶ 𝔸¹_k` over the origin
(`Stacks.EtaleCohomology.Purity.exists_smooth_affineLine_chart`), an étale `T₁ ⟶ U` on which `H` is
constant, and adjoin a primitive `N`-th root of unity: `Ũ = (T₁ ×_U V) ×_k k(ζ_N)`, étale over `U`.
Its base change `Ũ' = Ũ ×_U U'` has the chart `Ũ' ⟶ 𝔸¹_{W'} ⟶ 𝔸¹_{k'}`, the base change of
`Ũ ⟶ 𝔸¹_W`, with the same coordinate. The base change maps along `Ũ ⟶ U` and `Ũ' ⟶ U'` are
invertible (smooth base change, Stacks 0EYU), and that of the square over `Ũ' ⟶ Ũ` is invertible on
the constant coefficients
(`Stacks.EtaleCohomology.Purity.isIso_higherBaseChangeMapAb_one_constantSheaf_of_charts`); the cube
lemma (`Stacks.EtaleCohomology.isIso_map_higherBaseChangeMapAb_app_of_cube`) concludes.

## Main results

* `Stacks.EtaleCohomology.Purity.affineLineBaseMap_appTop_coordinate`.
* `Stacks.EtaleCohomology.Purity.exists_isPullback_punctured_of_mem_range_iff`.
* `Stacks.EtaleCohomology.Purity.isIso_higherBaseChangeMapAb_one_of_relativeCurve`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/- The base instance
`Stacks.Cohomology.DerivedLowerShriek.preservesZeroMorphisms_abelianLowerShriek` (reachable through
`ProperBaseChange.LowerShriekCompactification`) leaves the searches for
`(smallEtalePullbackAb _).PreservesZeroMorphisms` below stuck at a universe constraint; it is not
used here. -/
attribute [-instance] Stacks.Cohomology.DerivedLowerShriek.preservesZeroMorphisms_abelianLowerShriek

universe u

namespace Stacks.EtaleCohomology.Purity

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k]

/-- The coordinate of `𝔸¹_k` pulls back to the coordinate of `𝔸¹_W` along `𝔸¹_W ⟶ 𝔸¹_k`. -/
theorem affineLineBaseMap_appTop_coordinate {W : Scheme.{u}} (pW : W ⟶ Spec (.of k)) :
    (affineLineBaseMap k pW).appTop (coordinate k) = AffineSpace.coord W ⟨0⟩ := by
  rw [affineLineBaseMap, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    KummerFlag.lastCoordinateProjection_eq, KummerFlag.coordProj_appTop_coordinate,
    AffineSpace.map_appTop_coord]
  rfl

/-- A point lies over the punctured line exactly when it lies in the basic open of the pulled
back coordinate. -/
theorem mem_punctured_iff_mem_basicOpen {V : Scheme.{u}} (φ : V ⟶ affineLine k) (v : V) :
    φ.base v ∈ (punctured k : Set (affineLine k)) ↔
      v ∈ (V.basicOpen (φ.appTop (coordinate k)) : Set V) := by
  rw [← Scheme.preimage_basicOpen_top]
  rfl

/-- **An open immersion with the points over the punctured line as image is its pullback.** -/
theorem exists_isPullback_punctured_of_mem_range_iff {V V₀ : Scheme.{u}} (φ : V ⟶ affineLine k)
    (j : V₀ ⟶ V) [IsOpenImmersion j]
    (h : ∀ v, v ∈ Set.range j.base ↔ φ.base v ∈ (punctured k : Set (affineLine k))) :
    ∃ φ₀ : V₀ ⟶ (punctured k).toScheme, IsPullback j φ₀ φ (punctured k).ι := by
  have H' : φ ⁻¹ᵁ (punctured k).ι.opensRange = j.opensRange := by
    ext v
    change φ.base v ∈ Set.range (punctured k).ι.base ↔ v ∈ Set.range j.base
    rw [Scheme.Opens.range_ι]
    exact (h v).symm
  have hsub : Set.range (j ≫ φ).base ⊆ Set.range (punctured k).ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact (h (j.base y)).1 ⟨y, rfl⟩
  exact ⟨IsOpenImmersion.lift (punctured k).ι (j ≫ φ) hsub,
    (IsOpenImmersion.isPullback _ j (punctured k).ι φ (IsOpenImmersion.lift_fac _ _ _).symm
      H').flip⟩

/-- On a scheme over a chart `V` of `U`, a point lies over the punctured line exactly when its
image in `U` lies off `Z`. -/
theorem mem_punctured_iff_of_chart {U Z U₀ V' : Scheme.{u}} (i : Z ⟶ U) (j : U₀ ⟶ U)
    (hj : Set.range j.base = (Set.range i.base)ᶜ) (V : U.Opens) (φV : V.toScheme ⟶ affineLine k)
    (ψ : (i ⁻¹ᵁ V).toScheme ⟶ Spec (.of k)) (hpb : IsPullback (i ∣_ V) ψ φV (origin k))
    (s : V' ⟶ V.toScheme) (x : V') :
    (s ≫ φV).base x ∈ (punctured k : Set (affineLine k)) ↔
      (s ≫ V.ι).base x ∈ Set.range j.base := by
  have h1 := mem_range_iff_of_isPullback_origin (i ∣_ V) ψ φV hpb (s.base x)
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hj, Set.mem_compl_iff,
    ← mem_range_morphismRestrict_iff i V (s.base x)]
  exact ⟨fun hp hm => h1.1 hm hp, fun hn => by_contra fun hp => hn (h1.2 hp)⟩

/-- A sheaf killed by `N`, with `N` invertible on a `k`-scheme `Y`, has torsion stalks of order a
positive integer invertible on `Y`. -/
private theorem exists_isUnit_nsmul_eq_zero_stalk {N : ℕ} (hN : IsUnit (N : k))
    {X Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (hG : N • 𝟙 G = 0) (t : GeometricPoint X) (a : (smallEtaleStalkAb t.hom).obj G) :
    ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(Y, ⊤)) ∧ n • a = 0 :=
  ⟨N, Nat.pos_of_ne_zero (by rintro rfl; simp at hN),
    by exact_mod_cast isUnit_natCast_globalSections_of_over (ℓ := N) f hN,
    nsmul_eq_zero_stalk_of_nsmul_id hG t a⟩

/-- The inverse image of a sheaf killed by `N` is killed by `N`. -/
private theorem nsmul_id_smallEtalePullbackAb_eq_zero {N : ℕ} {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (hG : N • 𝟙 G = 0) :
    N • 𝟙 ((smallEtalePullbackAb f).obj G) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hG, Functor.map_zero]

section BaseChange

variable (k) (N : ℕ) (hN : IsUnit (N : k)) {U W Z U₀ : Scheme.{u}} (pW : W ⟶ Spec (.of k))
  [Smooth pW] (g : U ⟶ W) [SmoothOfRelativeDimension 1 g] (i : Z ⟶ U) [IsClosedImmersion i]
  [Etale (i ≫ g)] (j : U₀ ⟶ U) [IsOpenImmersion j] (hj : Set.range j.base = (Set.range i.base)ᶜ)
  {k' : Type u} [Field k'] {W' U' U₀' : Scheme.{u}} (pW' : W' ⟶ Spec (.of k')) [Smooth pW']
  (uW : W' ⟶ W) (u' : U' ⟶ U) (g' : U' ⟶ W') (hU : IsPullback u' g' g uW)
  (j' : U₀' ⟶ U') [IsOpenImmersion j'] (u₀ : U₀' ⟶ U₀) (sq : IsPullback u₀ j' j u')
  (H : EtaleModules.{u, 0} (ZMod N) U) (hH : lccModules U N H)

include hN hj hU hH pW pW' in
/-- **The degree-one base change map near a point over `Z`.** At a point `p` of `U'` over `Z`,
the inverse image of the degree-one base change map of `j⁻¹ H` along some étale neighbourhood of
`p` is an isomorphism. -/
theorem exists_isIso_smallEtalePullbackAb_higherBaseChangeMapAb_one (p : U') (z : Z)
    (hz : u'.base p = i.base z) :
    ∃ (V : Scheme.{u}) (e' : V ⟶ U'), p ∈ Set.range e'.base ∧
      IsIso ((smallEtalePullbackAb e').map ((higherBaseChangeMapAb u' j j' u₀ sq.w.symm (0 + 1)).app
        ((etaleModuleForgetAb.{u, 0} (ZMod N) U₀).obj
          ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H)))) := by
  classical
  have : NeZero (N : k) := ⟨hN.ne_zero⟩
  have : NeZero N := NeZero.of_neZero_natCast k
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (g ≫ pW)
  have : IsSeparated j := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated j := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  have : QuasiCompact j' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have : IsSeparated j' := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated j' := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  set F := (etaleModuleRestriction.{u, 0} (ZMod N) j).obj H with hFdef
  set Fa := (etaleModuleForgetAb.{u, 0} (ZMod N) U₀).obj F with hFadef
  have hFa : N • 𝟙 Fa = 0 := nsmul_id_etaleModuleForgetUniv_zmod F
  have htors := exists_isUnit_nsmul_eq_zero_stalk hN (g ≫ pW) hFa
  have htors' := exists_isUnit_nsmul_eq_zero_stalk hN (u' ≫ g ≫ pW)
    (nsmul_id_smallEtalePullbackAb_eq_zero u₀ hFa)
  -- `N` is invertible in `k'`, since `U'` is nonempty
  have hN' : IsUnit (N : k') := by
    rw [isUnit_iff_ne_zero]
    intro hk0
    have hU1 := isUnit_natCast_globalSections_of_over (ℓ := N) (u' ≫ g ≫ pW) hN
    have h0 : ((N : ℕ) : Γ(U', ⊤)) = 0 := by
      have := map_natCast (((Scheme.ΓSpecIso (.of k')).inv ≫ (g' ≫ pW').appTop).hom) N
      rw [← this, hk0, map_zero]
    rw [h0] at hU1
    have := hU1.map (U'.presheaf.germ ⊤ p trivial).hom
    rw [map_zero] at this
    exact not_isUnit_zero this
  -- the chart and the trivialisation
  obtain ⟨V, hzV, π, ψ, hπ, hover, -, hpb⟩ := exists_smooth_affineLine_chart k pW g i z
  obtain ⟨T₁, e₁, he₁, E, ⟨t₁, ht₁⟩, hE, ⟨c⟩⟩ :=
    exists_etale_inverseImage_constant_of_isFiniteTypeLocallyConstant (ZMod N) H hH (i.base z)
  let φV : V.toScheme ⟶ affineLine k := π ≫ affineLineBaseMap k pW
  -- adjoining a primitive `N`-th root of unity
  let K := CyclotomicField N k
  let sK : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let T : T₁.Opens := e₁ ⁻¹ᵁ V
  let pT : T.toScheme ⟶ Spec (.of k) := (e₁ ∣_ V) ≫ φV ≫ (affineLine k ↘ Spec (.of k))
  let Ut := pullback pT sK
  let s : Ut ⟶ V.toScheme := pullback.fst pT sK ≫ (e₁ ∣_ V)
  let e : Ut ⟶ U := s ≫ V.ι
  have : Etale (e₁ ∣_ V) := MorphismProperty.of_isPullback (P := @Etale)
    (isPullback_morphismRestrict e₁ V).flip inferInstance
  have : Etale (pullback.fst pT sK) := MorphismProperty.of_isPullback (P := @Etale)
    (IsPullback.of_hasPullback pT sK).flip inferInstance
  have : Etale s := inferInstanceAs (Etale (pullback.fst pT sK ≫ (e₁ ∣_ V)))
  have : Etale e := inferInstanceAs (Etale (s ≫ V.ι))
  have : Smooth e := SmoothOfRelativeDimension.smooth 0 e
  have : Etale π := hπ
  let πt : Ut ⟶ 𝔸(ULift.{u} (Fin (0 + 1)); W) := s ≫ π
  have : Etale πt := inferInstanceAs (Etale (s ≫ π))
  let φ : Ut ⟶ affineLine k := s ≫ φV
  have hφ : φ = πt ≫ affineLineBaseMap k pW := (Category.assoc _ _ _).symm
  have : Smooth φ := by
    rw [hφ]
    have : Smooth πt := SmoothOfRelativeDimension.smooth 0 πt
    infer_instance
  have hπt : πt ≫ (𝔸(ULift.{u} (Fin (0 + 1)); W) ↘ W) = e ≫ g := by
    change ((pullback.fst pT sK ≫ (e₁ ∣_ V)) ≫ π) ≫ _ =
      ((pullback.fst pT sK ≫ (e₁ ∣_ V)) ≫ V.ι) ≫ g
    simp only [Category.assoc, hover]
  have he₁e : e = pullback.fst pT sK ≫ T.ι ≫ e₁ := by
    change (pullback.fst pT sK ≫ (e₁ ∣_ V)) ≫ V.ι = _
    rw [Category.assoc, morphismRestrict_ι]
  -- a point of `Ũ` over `p`
  obtain ⟨xt, hxt⟩ : ∃ xt : Ut, e.base xt = u'.base p := by
    have ht₁T : t₁ ∈ T := by
      change e₁.base t₁ ∈ V
      rw [ht₁]
      exact hzV
    have : Surjective sK := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
    obtain ⟨y, hy⟩ := (pullback.fst pT sK).surjective ⟨t₁, ht₁T⟩
    refine ⟨y, ?_⟩
    rwa [he₁e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy, hz]
  -- the cube
  let Ut₀ := pullback j e
  let jt : Ut₀ ⟶ Ut := pullback.snd j e
  let e₀ : Ut₀ ⟶ U₀ := pullback.fst j e
  have sqB : IsPullback jt e₀ e j := (IsPullback.of_hasPullback j e).flip
  let Ut' := pullback e u'
  let ut : Ut' ⟶ Ut := pullback.fst e u'
  let e' : Ut' ⟶ U' := pullback.snd e u'
  have hu : e' ≫ u' = ut ≫ e := pullback.condition.symm
  let Ut₀' := pullback j' e'
  let jt' : Ut₀' ⟶ Ut' := pullback.snd j' e'
  let e₀' : Ut₀' ⟶ U₀' := pullback.fst j' e'
  have sqA : IsPullback jt' e₀' e' j' := (IsPullback.of_hasPullback j' e').flip
  have hlift : (e₀' ≫ u₀) ≫ j = (jt' ≫ ut) ≫ e := by
    rw [Category.assoc, sq.w, ← Category.assoc, ← sqA.w, Category.assoc, hu, Category.assoc]
  let ut₀ : Ut₀' ⟶ Ut₀ := pullback.lift (e₀' ≫ u₀) (jt' ≫ ut) hlift
  have wut : jt' ≫ ut = ut₀ ≫ jt := (pullback.lift_snd _ _ _).symm
  have hv : e₀' ≫ u₀ = ut₀ ≫ e₀ := (pullback.lift_fst _ _ _).symm
  have : Etale e' := MorphismProperty.of_isPullback (P := @Etale)
    (IsPullback.of_hasPullback e u') inferInstance
  have : Smooth e' := SmoothOfRelativeDimension.smooth 0 e'
  have : QuasiCompact jt := MorphismProperty.of_isPullback (P := @QuasiCompact)
    (IsPullback.of_hasPullback j e) inferInstance
  have : QuasiCompact jt' := MorphismProperty.of_isPullback (P := @QuasiCompact)
    (IsPullback.of_hasPullback j' e') inferInstance
  -- the squares over `e` and `e'`: smooth base change
  have hB := SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth e jt e₀ j sqB Fa htors
    (0 + 1)
  have hA := SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth e' jt' e₀' j' sqA
    ((smallEtalePullbackAb u₀).obj Fa) htors' (0 + 1)
  -- the chart on `Ũ'`: the base change of `Ũ ⟶ 𝔸¹_W` along `𝔸¹_{W'} ⟶ 𝔸¹_W`
  have hmapW := (AffineSpace.isPullback_map (n := ULift.{u} (Fin (0 + 1))) uW).flip
  have hout : IsPullback (e' ≫ g') ut uW (πt ≫ (𝔸(ULift.{u} (Fin (0 + 1)); W) ↘ W)) := by
    rw [hπt]
    exact (IsPullback.of_hasPullback e u').flip.paste_horiz hU.flip
  let πt' := hmapW.lift (e' ≫ g') (ut ≫ πt) (by rw [hout.w]; exact (Category.assoc _ _ _).symm)
  have hout' : IsPullback (πt' ≫ (𝔸(ULift.{u} (Fin (0 + 1)); W') ↘ W')) ut uW
      (πt ≫ (𝔸(ULift.{u} (Fin (0 + 1)); W) ↘ W)) := by
    rwa [hmapW.lift_fst]
  have hleft : IsPullback πt' ut (AffineSpace.map (ULift.{u} (Fin (0 + 1))) uW) πt :=
    IsPullback.of_right hout' (hmapW.lift_snd _ _ _) hmapW
  have : Etale πt' := MorphismProperty.of_isPullback (P := @Etale) hleft.flip inferInstance
  let φ' : Ut' ⟶ affineLine k' := πt' ≫ affineLineBaseMap k' pW'
  have : Smooth φ' := by
    have : Smooth πt' := SmoothOfRelativeDimension.smooth 0 πt'
    infer_instance
  have hc : ∀ {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (r : Γ(Z, ⊤)),
      (a ≫ b).appTop r = a.appTop (b.appTop r) := fun a b r => by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h1 : φ'.appTop (coordinate k') = (ut ≫ πt).appTop (AffineSpace.coord W ⟨0⟩) := by
    change (πt' ≫ affineLineBaseMap k' pW').appTop (coordinate k') = _
    rw [hc πt' (affineLineBaseMap k' pW'), affineLineBaseMap_appTop_coordinate,
      ← AffineSpace.map_appTop_coord (n := ULift.{u} (Fin (0 + 1))) uW ⟨0⟩,
      ← hc πt' (AffineSpace.map (ULift.{u} (Fin (0 + 1))) uW), hleft.w]
  have hcoord : ut.appTop (φ.appTop (coordinate k)) = φ'.appTop (coordinate k') := by
    rw [h1, hc ut πt, hφ, hc πt (affineLineBaseMap k pW), affineLineBaseMap_appTop_coordinate]
  -- the punctured squares
  obtain ⟨φ₀, sqS⟩ := exists_isPullback_punctured_of_mem_range_iff φ jt fun x => by
    rw [Scheme.Pullback.range_snd]
    exact (mem_punctured_iff_of_chart i j hj V φV ψ hpb s x).symm
  obtain ⟨φ₀', sqX⟩ := exists_isPullback_punctured_of_mem_range_iff φ' jt' fun x => by
    rw [Scheme.Pullback.range_snd, Set.mem_preimage,
      mem_range_iff_of_isPullback_of_isOpenImmersion u' j j' u₀ sq.flip,
      ← Scheme.Hom.comp_apply, hu, Scheme.Hom.comp_apply,
      ← mem_punctured_iff_of_chart i j hj V φV ψ hpb s, mem_punctured_iff_mem_basicOpen (s ≫ φV),
      mem_punctured_iff_mem_basicOpen φ', ← hcoord, ← Scheme.preimage_basicOpen_top ut]
    rfl
  -- the coefficients on `Ũ₀`
  let A : AddCommGrpCat.{u + 1} := (forget₂ (ModuleCat.{u + 1} (ZMod N)) Ab.{u + 1}).obj E
  have : Module.Finite (ZMod N) E := hE
  have : Finite E := Module.finite_of_finite (ZMod N)
  have : Finite A := inferInstanceAs (Finite E)
  have hE0 : ∀ x : E, N • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul]
  have hA0 : ∀ a : A, N • a = 0 := fun a => hE0 a
  obtain ⟨cY⟩ := nonempty_smallEtalePullbackAb_forget_iso_constant (ZMod N) H e₁ E c
    (jt ≫ pullback.fst pT sK ≫ T.ι)
  have heq : (jt ≫ pullback.fst pT sK ≫ T.ι) ≫ e₁ = e₀ ≫ j := by
    refine Eq.trans ?_ pullback.condition.symm
    rw [Category.assoc, Category.assoc]
    exact congrArg (jt ≫ ·) he₁e.symm
  let cF : (smallEtalePullbackAb e₀).obj Fa ≅
      (constantSheaf (smallEtaleTopology Ut₀) Ab.{u + 1}).obj A :=
    (smallEtalePullbackAb e₀).mapIso
        ((etaleModuleForgetAb.{u, 0} (ZMod N) U₀).mapIso
          ((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) j).app H).symm ≪≫
        ((etaleModuleForgetInverseImageIso.{u, 0} (ZMod N) j).app H).symm ≪≫
        ((smallEtalePullbackAbIsoEtaleAbelianInverseImage j).app _).symm) ≪≫
      (smallEtalePullbackAbCompIso' e₀ j ((jt ≫ pullback.fst pT sK ≫ T.ι) ≫ e₁) heq).app _ ≪≫ cY
  have hζ := IsCyclotomicExtension.zeta_spec N k K
  have hC : IsIso ((higherBaseChangeMapAb ut jt jt' ut₀ wut (0 + 1)).app
      ((smallEtalePullbackAb e₀).obj Fa)) :=
    isIso_app_of_iso_of_isIso (higherBaseChangeMapAb ut jt jt' ut₀ wut (0 + 1)) cF.symm
      (isIso_higherBaseChangeMapAb_one_constantSheaf_of_charts ut jt jt' ut₀ wut φ φ₀ sqS φ' φ₀'
        sqX hcoord N hN hN' (jt ≫ pullback.snd pT sK) hζ A hA0)
  -- the point of `Ũ'` over `p`
  obtain ⟨x', -, hx'⟩ := Scheme.Pullback.exists_preimage_pullback xt p hxt
  exact ⟨Ut', e', ⟨x', hx'⟩, isIso_map_higherBaseChangeMapAb_app_of_cube j j' jt jt' u' u₀
    sq.w.symm e e₀ sqB.w e' e₀' sqA.w ut ut₀ wut hu hv (0 + 1) Fa hB hA hC⟩

include hN hj hU hH pW pW' in
/-- **The degree-one base change map along an étale divisor of a smooth relative curve.** For
`W` smooth over `k`, `g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a closed immersion
with `Z ⟶ W` étale, `j : U₀ ⟶ U` the open complement, `N` invertible in `k`, a base change
`U' = U ×_W W'` along `W' ⟶ W` with `W'` smooth over a field and `U₀' = U₀ ×_U U'`, the
degree-one base change map `u'⁻¹ R¹ j_*(j⁻¹ H) ⟶ R¹ j'_*(u₀⁻¹ j⁻¹ H)` of the underlying abelian
sheaves is an isomorphism for every locally constant sheaf `H` of finite type of
`ℤ/N`-modules. -/
theorem isIso_higherBaseChangeMapAb_one_of_relativeCurve :
    IsIso ((higherBaseChangeMapAb u' j j' u₀ sq.w.symm (0 + 1)).app
      ((etaleModuleForgetAb.{u, 0} (ZMod N) U₀).obj
        ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H))) := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (g ≫ pW)
  have : QuasiCompact j' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  set Fa := (etaleModuleForgetAb.{u, 0} (ZMod N) U₀).obj
    ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H) with hFadef
  have hFa : N • 𝟙 Fa = 0 := nsmul_id_etaleModuleForgetUniv_zmod _
  apply isIso_of_forall_exists_isIso_smallEtalePullbackAb
  intro p
  by_cases hp : p ∈ Set.range j'.base
  · -- over `U₀'` both sides vanish
    refine ⟨U₀', j', hp, ?_⟩
    have h0 : IsZero ((smallEtalePullbackAb j).obj
        (((smallEtalePushforwardAb j).rightDerived (0 + 1)).obj Fa)) :=
      (isZero_restriction_rightDerived_of_isOpenImmersion j Fa
        (exists_isUnit_nsmul_eq_zero_stalk hN (g ≫ pW) hFa) (0 + 1) Nat.one_pos).of_iso
        ((smallEtalePullbackAbIsoEtaleRestriction j).app _)
    have hs : IsZero ((smallEtalePullbackAb j').obj ((smallEtalePullbackAb u').obj
        (((smallEtalePushforwardAb j).rightDerived (0 + 1)).obj Fa))) :=
      (Functor.map_isZero (smallEtalePullbackAb u₀) h0).of_iso
        ((smallEtalePullbackAbCompIso' j' u' (u₀ ≫ j) sq.w).app _ ≪≫
          ((smallEtalePullbackAbCompIso' u₀ j (u₀ ≫ j) rfl).app _).symm)
    have ht : IsZero ((smallEtalePullbackAb j').obj
        (((smallEtalePushforwardAb j').rightDerived (0 + 1)).obj
          ((smallEtalePullbackAb u₀).obj Fa))) :=
      (isZero_restriction_rightDerived_of_isOpenImmersion j' _
        (exists_isUnit_nsmul_eq_zero_stalk hN (u' ≫ g ≫ pW)
          (nsmul_id_smallEtalePullbackAb_eq_zero u₀ hFa)) (0 + 1) Nat.one_pos).of_iso
        ((smallEtalePullbackAbIsoEtaleRestriction j').app _)
    exact ⟨⟨0, hs.eq_of_src _ _, ht.eq_of_src _ _⟩⟩
  · -- over `Z`
    obtain ⟨z, hz⟩ : u'.base p ∈ Set.range i.base := by
      by_contra h
      refine hp ?_
      rwa [mem_range_iff_of_isPullback_of_isOpenImmersion u' j j' u₀ sq.flip p, hj]
    exact exists_isIso_smallEtalePullbackAb_higherBaseChangeMapAb_one k N hN pW g i j hj pW' uW
      u' g' hU j' u₀ sq H hH p z hz.symm

end BaseChange

end Stacks.EtaleCohomology.Purity

end
