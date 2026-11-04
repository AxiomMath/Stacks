module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAffineSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSupportedInOpen
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineRepresentableUnconditional

/-!
# Hilbert families supported in an open subscheme

Let `X ⟶ S` be a separated morphism of schemes, `V ⊆ S` an open and `U ⊆ X` an open lying over
`V`. For a scheme `T` over `S` whose structure morphism factors through `V`, a degree-`d` Hilbert
family in `X` over `T` supported in `U` is the same as a degree-`d` Hilbert family in `U` over `T`,
viewed as a scheme over `V`. This is the identification `F_U = Hilb^d_{U/S}` in the source's proof
of [Stacks, Tag 0B9A]: a closed subscheme of `U_T` finite over `T` stays closed in `X_T` because
`X_T` is separated over `T`.

## Main definitions

* `Stacks.Hilbert.OpenChart.openIncl`: the open immersion `U_T ⟶ X_T`.
* `Stacks.Hilbert.OpenChart.extend` (`Φ`) and `Stacks.Hilbert.OpenChart.restrict` (`Ψ`): the two
  directions of the identification.

## Main results

* `restrict_extend`, `extend_restrict` and `restrict_baseChange` (naturality).

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert.OpenChart

/-- If `a ≫ m = i` with `m` a monomorphism, then `a` is the pullback of `i` along `m`. -/
theorem isPullback_of_comp_mono {C : Type*} [Category C] {A O Y : C} (a : A ⟶ O) (m : O ⟶ Y)
    [Mono m] : IsPullback a (𝟙 A) m (a ≫ m) :=
  IsPullback.of_isLimit (c := PullbackCone.mk a (𝟙 A) (by simp))
    (PullbackCone.IsLimit.mk _ (fun s ↦ s.snd)
      (fun s ↦ by rw [← cancel_mono m]; simpa using s.condition.symm)
      (fun s ↦ by simp)
      (fun s l _ h₂ ↦ by simpa using h₂))

variable {S : Scheme.{u}} (X : Over S) {d : ℕ} (V : S.Opens) (U : X.left.Opens)
  (hUV : U ≤ X.hom ⁻¹ᵁ V)

/-- The morphism `U ⟶ V` induced by `X ⟶ S`. -/
def restrictHom : U.toScheme ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (U.ι ≫ X.hom) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hUV x.2)

/-- The morphism `restrictHom` composed with the inclusion of `V` is `U ⟶ X ⟶ S`. -/
@[reassoc (attr := simp)]
theorem restrictHom_ι : restrictHom X V U hUV ≫ V.ι = U.ι ≫ X.hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- `U` as a scheme over `V`. -/
abbrev restricted : Over V.toScheme := Over.mk (restrictHom X V U hUV)

variable {T : Over S} (a : T.left ⟶ V.toScheme) (ha : a ≫ V.ι = T.hom)

/-- The open immersion `U ×_V T ⟶ X ×_S T`. -/
def openIncl : ((Over.pullback a).obj (restricted X V U hUV)).left ⟶
    ((Over.pullback T.hom).obj X).left :=
  pullback.map (restrictHom X V U hUV) a X.hom T.hom U.ι (𝟙 _) V.ι (restrictHom_ι X V U hUV)
    (by rw [ha, Category.id_comp])

/-- The morphism `openIncl` is an open immersion. -/
instance : IsOpenImmersion (openIncl X V U hUV a ha) := by
  unfold openIncl
  infer_instance

/-- The first projection of `openIncl` is the first projection of `U ×_V T` followed by `U ⟶ X`. -/
@[reassoc (attr := simp)]
theorem openIncl_fst : openIncl X V U hUV a ha ≫ pullback.fst X.hom T.hom =
    pullback.fst (restrictHom X V U hUV) a ≫ U.ι := by
  simp only [openIncl, pullback.map, pullback.lift_fst]

/-- The morphism `openIncl` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem openIncl_snd : openIncl X V U hUV a ha ≫ pullback.snd X.hom T.hom =
    pullback.snd (restrictHom X V U hUV) a := by
  simp only [openIncl, pullback.map, pullback.lift_snd, Category.comp_id]

/-- `U ×_V T` is the preimage of `U` in `X ×_S T`. -/
theorem isPullback_openIncl : IsPullback (openIncl X V U hUV a ha)
    (pullback.fst (restrictHom X V U hUV) a) (pullback.fst X.hom T.hom) U.ι := by
  have hout' : IsPullback (openIncl X V U hUV a ha ≫ pullback.snd X.hom T.hom)
      (pullback.fst (restrictHom X V U hUV) a) T.hom (U.ι ≫ X.hom) := by
    rw [openIncl_snd, ← restrictHom_ι, ← ha]
    exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono a (restrictHom X V U hUV) V.ι _
      (IsPullback.of_hasPullback (restrictHom X V U hUV) a).flip.isLimit)
  exact IsPullback.of_right hout' (openIncl_fst X V U hUV a ha)
    (IsPullback.of_hasPullback X.hom T.hom).flip

variable [IsSeparated X.hom]

/-- A closed subscheme of `U ×_V T` finite over `T` is closed in `X ×_S T`. -/
instance isClosedImmersion_comp_openIncl (Z' : HilbertFamily (restricted X V U hUV) (Over.mk a) d) :
    IsClosedImmersion (Z'.ideal.subschemeι ≫ openIncl X V U hUV a ha) := by
  have hfin : IsFinite (Z'.ideal.subschemeι ≫ pullback.snd (restrictHom X V U hUV) a) :=
    Z'.isFinite_structural
  have : UniversallyClosed ((Z'.ideal.subschemeι ≫ openIncl X V U hUV a ha) ≫
      pullback.snd X.hom T.hom) := by
    rw [Category.assoc, openIncl_snd]
    infer_instance
  have : UniversallyClosed (Z'.ideal.subschemeι ≫ openIncl X V U hUV a ha) :=
    UniversallyClosed.of_comp_of_isSeparated _ (pullback.snd X.hom T.hom)
  exact .of_isPreimmersion _ (Scheme.Hom.isClosedMap _).isClosed_range

/-- **Φ**: a family in `U` over `T` viewed as a family in `X`. -/
def extend (Z' : HilbertFamily (restricted X V U hUV) (Over.mk a) d) :
    HilbertFamily X T d where
  ideal := (Z'.ideal.subschemeι ≫ openIncl X V U hUV a ha).ker
  isFiniteLocallyFreeOfRank := by
    let i := Z'.ideal.subschemeι ≫ openIncl X V U hUV a ha
    have e : i.ker.subschemeι = inv i.toImage ≫ i := by
      rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
    change Stacks.Morphisms.IsFiniteLocallyFreeOfRank (i.ker.subschemeι ≫ pullback.snd _ _) d
    rw [e, Category.assoc, Category.assoc, openIncl_snd]
    exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp (asIso (inv i.toImage)) _
      Z'.isFiniteLocallyFreeOfRank

/-- The family `extend` is supported in `U`. -/
theorem extend_supportedIn (Z' : HilbertFamily (restricted X V U hUV) (Over.mk a) d) :
    (extend X V U hUV a ha Z').SupportedIn U := by
  intro z
  let i := Z'.ideal.subschemeι ≫ openIncl X V U hUV a ha
  have e : i.ker.subschemeι = inv i.toImage ≫ i := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  change (i.ker.subschemeι ≫ pullback.fst X.hom T.hom) z ∈ U
  rw [e]
  simp only [i, Category.assoc, openIncl_fst]
  exact (_ : U.toScheme).2

omit [IsSeparated X.hom] in
/-- The range of `openIncl` is the preimage of `U` under the first projection `X ×_S T ⟶ X`. -/
theorem range_openIncl :
    Set.range (openIncl X V U hUV a ha) = pullback.fst X.hom T.hom ⁻¹' (U : Set X.left) := by
  have h := isPullback_openIncl X V U hUV a ha
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso h.isoPullback.hom.base).2,
    Set.image_univ, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

omit [IsSeparated X.hom] in
/-- For a family `Z` supported in `U`, the pullback of `openIncl` along the closed immersion of `Z`
is an isomorphism. -/
theorem isIso_pullback_snd_openIncl {Z : HilbertFamily X T d} (hZ : Z.SupportedIn U) :
    IsIso (pullback.snd (openIncl X V U hUV a ha) Z.ideal.subschemeι) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun z ↦ ?_⟩⟩
  change z ∈ Set.range (pullback.snd (openIncl X V U hUV a ha) Z.ideal.subschemeι)
  rw [Scheme.Pullback.range_snd, range_openIncl]
  exact hZ z

/-- **Ψ**: a family in `X` supported in `U`, viewed as a family in `U` over `V`. -/
def restrict (Z : HilbertFamily X T d) (hZ : Z.SupportedIn U) :
    HilbertFamily (restricted X V U hUV) (Over.mk a) d where
  ideal := Z.ideal.comap (openIncl X V U hUV a ha)
  isFiniteLocallyFreeOfRank := by
    have := isIso_pullback_snd_openIncl X V U hUV a ha hZ
    change Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((Z.ideal.comap (openIncl X V U hUV a ha)).subschemeι ≫
        pullback.snd (restrictHom X V U hUV) a) d
    have e : (Z.ideal.comap (openIncl X V U hUV a ha)).subschemeι ≫
        pullback.snd (restrictHom X V U hUV) a =
        ((Z.ideal.comapIso (openIncl X V U hUV a ha)).hom ≫
          pullback.snd (openIncl X V U hUV a ha) Z.ideal.subschemeι) ≫
            (Z.ideal.subschemeι ≫ pullback.snd X.hom T.hom) := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc,
        ← openIncl_snd X V U hUV a ha, reassoc_of% pullback.condition]
    rw [e]
    exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp (asIso _) _
      Z.isFiniteLocallyFreeOfRank

/-- `extend` is a left inverse of `restrict`: `Φ (Ψ Z) = Z`. -/
theorem extend_restrict {Z : HilbertFamily X T d} (hZ : Z.SupportedIn U) :
    extend X V U hUV a ha (restrict X V U hUV a ha Z hZ) = Z := by
  have := isIso_pullback_snd_openIncl X V U hUV a ha hZ
  apply HilbertFamily.ext
  change ((Z.ideal.comap (openIncl X V U hUV a ha)).subschemeι ≫
    openIncl X V U hUV a ha).ker = Z.ideal
  rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition,
    Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_subschemeι]

/-- `restrict` is a left inverse of `extend`: `Ψ (Φ Z') = Z'`. -/
theorem restrict_extend (Z' : HilbertFamily (restricted X V U hUV) (Over.mk a) d) :
    restrict X V U hUV a ha (extend X V U hUV a ha Z') (extend_supportedIn X V U hUV a ha Z') =
      Z' := by
  apply HilbertFamily.ext
  change (Z'.ideal.subschemeι ≫ openIncl X V U hUV a ha).ker.comap (openIncl X V U hUV a ha) =
    Z'.ideal
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hfst : pullback.fst (openIncl X V U hUV a ha) (Z'.ideal.subschemeι ≫
      openIncl X V U hUV a ha) = pullback.snd _ _ ≫ Z'.ideal.subschemeι := by
    rw [← cancel_mono (openIncl X V U hUV a ha), pullback.condition, Category.assoc]
  rw [hfst, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

omit [IsSeparated X.hom] in
/-- **Ψ commutes with base change.** -/
theorem restrict_baseChange {T₂ : Over S} (g : T₂ ⟶ T) (b : T₂.left ⟶ V.toScheme)
    (hb : b ≫ V.ι = T₂.hom) (hgb : g.left ≫ a = b) {Z : HilbertFamily X T d}
    (hZ : Z.SupportedIn U) :
    restrict X V U hUV b hb (baseChange X g Z) (hZ.baseChange g) =
      baseChange (restricted X V U hUV) (Over.homMk g.left hgb : Over.mk b ⟶ Over.mk a)
        (restrict X V U hUV a ha Z hZ) := by
  apply HilbertFamily.ext
  change (Z.ideal.comap (familyBaseChangeMap X g)).comap (openIncl X V U hUV b hb) =
    (Z.ideal.comap (openIncl X V U hUV a ha)).comap
      (familyBaseChangeMap (restricted X V U hUV) (Over.homMk g.left hgb :
        Over.mk b ⟶ Over.mk a))
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, familyBaseChangeMap_comp_fst, openIncl_fst]
    exact (congrArg (· ≫ U.ι) (familyBaseChangeMap_comp_fst (restricted X V U hUV)
      (Over.homMk g.left hgb : Over.mk b ⟶ Over.mk a))).symm
  · simp only [Category.assoc, familyBaseChangeMap_comp_snd, openIncl_snd, openIncl_snd_assoc]
    exact (familyBaseChangeMap_comp_snd (restricted X V U hUV)
      (Over.homMk g.left hgb : Over.mk b ⟶ Over.mk a)).symm

omit [IsSeparated X.hom] in
/-- **A finite set inside an affine open and inside another open lies in an affine open contained
in the latter.** The elements of `Γ(X, U)` whose basic open lies in `V` form an ideal not covered
by the finitely many primes of the points of `E`, by prime avoidance, so one of them cuts out a
basic open of `U` containing `E` and contained in `V`. -/
theorem _root_.Stacks.Hilbert.OpenChart.exists_isAffineOpen_between_of_finite {X : Scheme.{u}}
    {U V : X.Opens} (hU : IsAffineOpen U) {E : Set X} (hE : E.Finite) (hEU : E ⊆ U) (hEV : E ⊆ V) :
    ∃ W : X.Opens, IsAffineOpen W ∧ E ⊆ W ∧ W ≤ V := by
  classical
  by_cases hne : E.Nonempty
  · let I : Ideal Γ(X, U) :=
      { carrier := {r | X.basicOpen r ≤ V}
        zero_mem' := by simp
        add_mem' := fun hr hs ↦ (X.basicOpen_add_le _ _).trans (sup_le hr hs)
        smul_mem' := fun r s hs ↦ by
          change X.basicOpen (r * s) ≤ V
          rw [Scheme.basicOpen_mul]
          exact inf_le_of_right_le hs }
    let p : E → PrimeSpectrum Γ(X, U) := fun x ↦ hU.primeIdealOf ⟨x.1, hEU x.2⟩
    have hp (x : E) (r : Γ(X, U)) : r ∉ (p x).asIdeal ↔ x.1 ∈ X.basicOpen r := by
      change p x ∈ PrimeSpectrum.basicOpen r ↔ _
      rw [← hU.fromSpec_preimage_basicOpen]
      change hU.fromSpec (p x) ∈ X.basicOpen r ↔ _
      rw [IsAffineOpen.fromSpec_primeIdealOf]
    let x₀ : E := ⟨hne.choose, hne.choose_spec⟩
    have hn : ¬ (I : Set Γ(X, U)) ⊆ ⋃ x ∈ (Set.univ : Set E), ((p x).asIdeal : Set Γ(X, U)) := by
      let := hE.fintype
      rw [Ideal.subset_union_prime_finite (Set.toFinite (Set.univ : Set E)) x₀ x₀
        (fun x _ _ _ ↦ (p x).isPrime)]
      rintro ⟨x, _, hx⟩
      obtain ⟨r, hr, hxr⟩ := hU.exists_basicOpen_le ⟨x.1, hEV x.2⟩ (hEU x.2)
      exact (hp x r).2 hxr (hx hr)
    obtain ⟨r, hr, havoid⟩ := Set.not_subset.mp hn
    exact ⟨X.basicOpen r, hU.basicOpen r, fun x hx ↦ (hp ⟨x, hx⟩ r).1 fun hrp ↦
      havoid (Set.mem_iUnion.2 ⟨⟨x, hx⟩, Set.mem_iUnion.2 ⟨Set.mem_univ _, hrp⟩⟩), hr⟩
  · exact ⟨⊥, by simpa using hU.basicOpen (0 : Γ(X, U)), fun z hz ↦ (hne ⟨z, hz⟩).elim, bot_le⟩

/-- An index of the charts of the gluing criterion: an affine open `V` of the base and an affine
open `U` of `X` over it. -/
structure ChartIndex where
  /-- The affine open of the base. -/
  V : S.Opens
  hV : IsAffineOpen V
  /-- The affine open of `X`. -/
  U : X.left.Opens
  hU : IsAffineOpen U
  hUV : U ≤ X.hom ⁻¹ᵁ V

variable {X}

/-- The chart subfunctor: families over schemes mapping into `V` and supported in `U`. -/
def chartSubfunctor (d : ℕ) (i : ChartIndex X) : Subfunctor (hilbertFunctorOfRank X d) where
  obj T := {Z | (∀ t, T.unop.hom t ∈ i.V) ∧ Z.SupportedIn i.U}
  map {T Y} h Z hZ := ⟨fun t ↦ by
      have hw : h.unop.left ≫ T.unop.hom = Y.unop.hom := Over.w h.unop
      rw [← hw, Scheme.Hom.comp_apply]
      exact hZ.1 _, hZ.2.baseChange _⟩

omit [IsSeparated X.hom] in
/-- The base change of `Z` along `h : Y ⟶ T` lies in the chart subfunctor of `i` if and only if
`h` maps `Y` into the open of `T` lying over `V` on which `Z` is supported in `U`. -/
theorem baseChange_mem_chartSubfunctor_iff (d : ℕ) (i : ChartIndex X) {T Y : Over S} (h : Y ⟶ T)
    (Z : HilbertFamily X T d) :
    (hilbertFunctorOfRank X d).map h.op Z ∈ (chartSubfunctor d i).obj (op Y) ↔
      ∀ y : Y.left, h.left y ∈ T.hom ⁻¹ᵁ i.V ⊓
        ⟨(Z.notSupportedLocus i.U)ᶜ, (Z.isClosed_notSupportedLocus i.U).isOpen_compl⟩ := by
  have hw : h.left ≫ T.hom = Y.hom := Over.w h
  change ((∀ y, Y.hom y ∈ i.V) ∧ (baseChange X h Z).SupportedIn i.U) ↔ _
  rw [HilbertFamily.baseChange_supportedIn_iff]
  constructor
  · rintro ⟨h₁, h₂⟩ y
    refine ⟨?_, h₂ y⟩
    change T.hom (h.left y) ∈ i.V
    rw [← Scheme.Hom.comp_apply, hw]
    exact h₁ y
  · intro H
    refine ⟨fun y ↦ ?_, fun y ↦ (H y).2⟩
    rw [← hw, Scheme.Hom.comp_apply]
    exact (H y).1

/-- Over a scheme `T` mapping into `V`, base change of the extended universal family of the
Hilbert scheme of `U` over `V` is injective on morphisms and hits every family supported in `U`. -/
private theorem injective_baseChange_extend_and_exists_eq (i : ChartIndex X)
    {HV : Over i.V.toScheme} (R : RepresentsHilbertFunctorOfRank (restricted X i.V i.U i.hUV) HV d)
    {T : Over S} (hT : ∀ t, T.hom t ∈ i.V) :
    Function.Injective (fun k : T ⟶ (Over.map i.V.ι).obj HV ↦ baseChange X k
      (extend X i.V i.U i.hUV (T := (Over.map i.V.ι).obj HV) HV.hom rfl (R.family (𝟙 HV)))) ∧
    ∀ Z : HilbertFamily X T d, Z.SupportedIn i.U → ∃ k : T ⟶ (Over.map i.V.ι).obj HV,
      baseChange X k
        (extend X i.V i.U i.hUV (T := (Over.map i.V.ι).obj HV) HV.hom rfl (R.family (𝟙 HV))) =
          Z := by
  set H : Over S := (Over.map i.V.ι).obj HV
  set Zu : HilbertFamily X H d := extend X i.V i.U i.hUV (T := H) HV.hom rfl (R.family (𝟙 HV))
  have hZu : Zu.SupportedIn i.U := extend_supportedIn X i.V i.U i.hUV (T := H) HV.hom rfl _
  have hrange : Set.range T.hom ⊆ Set.range i.V.ι := by
    rw [Scheme.Opens.range_ι]
    exact Set.range_subset_iff.2 hT
  let a : T.left ⟶ i.V.toScheme := IsOpenImmersion.lift i.V.ι T.hom hrange
  have ha : a ≫ i.V.ι = T.hom := IsOpenImmersion.lift_fac _ _ _
  have hkV (k : T ⟶ H) : k.left ≫ HV.hom = a := by
    rw [← cancel_mono i.V.ι, ha, Category.assoc]
    exact Over.w k
  let kV (k : T ⟶ H) : Over.mk a ⟶ HV := Over.homMk k.left (hkV k)
  have key (k : T ⟶ H) : restrict X i.V i.U i.hUV a ha (baseChange X k Zu)
      (hZu.baseChange k) = R.family (kV k) := by
    rw [restrict_baseChange X i.V i.U i.hUV HV.hom rfl k a ha (hkV k) hZu, restrict_extend]
    apply HilbertFamily.ext
    rw [baseChange_ideal, ← R.naturality]
    exact congrArg (fun m ↦ (R.family m).ideal) (Category.comp_id _)
  refine ⟨fun k k' hkk ↦ ?_, fun Z hZ ↦ ?_⟩
  · have h1 : baseChange X k Zu = baseChange X k' Zu := hkk
    have h2 : R.family (kV k) = R.family (kV k') := by
      rw [← key, ← key]
      congr 1
    have h3 := congrArg Over.Hom.left (R.family.injective h2)
    exact Over.OverMorphism.ext h3
  · let kV₀ := R.family.symm (restrict X i.V i.U i.hUV a ha Z hZ)
    have hk₀ : kV₀.left ≫ HV.hom ≫ i.V.ι = T.hom := by
      rw [← Category.assoc, Over.w kV₀]
      exact ha
    let k : T ⟶ H := Over.homMk kV₀.left hk₀
    have hkk : kV k = kV₀ := Over.OverMorphism.ext rfl
    refine ⟨k, ?_⟩
    rw [← extend_restrict X i.V i.U i.hUV a ha (hZu.baseChange k), key, hkk,
      Equiv.apply_symm_apply, extend_restrict]

/-- **The chart subfunctors are representable** by the Hilbert scheme of `U` over `V` (Tag 0B99),
viewed over `S`. -/
theorem chartSubfunctor_isRepresentable (d : ℕ) (i : ChartIndex X) :
    (chartSubfunctor d i).toFunctor.IsRepresentable := by
  have : IsAffine i.V.toScheme := i.hV
  have : IsAffine (restricted X i.V i.U i.hUV).left := i.hU
  obtain ⟨⟨HV, R⟩⟩ := exists_representsHilbertFunctorOfRank_of_isAffine_of_isAffine
    (restricted X i.V i.U i.hUV) d
  let H : Over S := (Over.map i.V.ι).obj HV
  let Zu : HilbertFamily X H d :=
    extend X i.V i.U i.hUV (T := H) HV.hom rfl (R.family (𝟙 HV))
  have hZu : Zu.SupportedIn i.U := extend_supportedIn X i.V i.U i.hUV (T := H) HV.hom rfl _
  let η : yoneda.obj H ⟶ (chartSubfunctor d i).toFunctor :=
    { app := fun T ↦ ↾ fun k ↦ ⟨baseChange X k Zu, fun t ↦ by
          have hw : k.left ≫ HV.hom ≫ i.V.ι = T.unop.hom := Over.w k
          rw [← hw, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
          exact (HV.hom (k.left t)).2, hZu.baseChange k⟩
      naturality := fun T T' g ↦ by
        ext k
        exact Subtype.ext (baseChange_comp X g.unop k Zu) }
  have hbij (T : Over S) : Function.Bijective (η.app (op T)) := by
    by_cases hT : ∀ t, T.hom t ∈ i.V
    · obtain ⟨hinj, hsurj⟩ := injective_baseChange_extend_and_exists_eq i R hT
      refine ⟨fun k k' hkk ↦ hinj (congrArg Subtype.val hkk), ?_⟩
      rintro ⟨Z, hZ⟩
      obtain ⟨k, hk⟩ := hsurj Z hZ.2
      exact ⟨k, Subtype.ext hk⟩
    · exact ⟨fun k ↦ absurd (η.app (op T) k).2.1 hT, fun Z ↦ absurd Z.2.1 hT⟩
  have : IsIso η := (NatTrans.isIso_iff_isIso_app _).2 fun T ↦
    (isIso_iff_bijective _).mpr (hbij T.unop)
  exact Functor.IsRepresentable.mk' (asIso η)

omit [IsSeparated X.hom] in
/-- **The charts cover** (condition (2)(c) of the gluing criterion): under the hypothesis of
Tag 0B9A every point of the base of a family lies in the open of some chart. -/
theorem exists_chart_mem (d : ℕ)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U)
    {T : Over S} (Z : HilbertFamily X T d) (t : T.left) :
    ∃ i : ChartIndex X, t ∈ T.hom ⁻¹ᵁ i.V ⊓
      ⟨(Z.notSupportedLocus i.U)ᶜ, (Z.isClosed_notSupportedLocus i.U).isOpen_compl⟩ := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (T.hom t)) isOpen_univ
  let κ := T.left.residueField t
  let p : Spec (CommRingCat.of κ) ⟶ T.left := T.left.fromSpecResidueField t
  let Zt := baseChange X (Over.homMk p rfl : Over.mk (p ≫ T.hom) ⟶ T) Z
  obtain ⟨U', hU', hsupp⟩ := exists_isAffineOpen_supportedIn_of_specField X d hX κ (p ≫ T.hom) Zt
  have ht' : t ∉ Z.notSupportedLocus U' := by
    have h := (HilbertFamily.baseChange_supportedIn_iff _ Z U').mp hsupp
      (IsLocalRing.closedPoint κ)
    rwa [← T.left.fromSpecResidueField_apply t (IsLocalRing.closedPoint κ)]
  let E : Set X.left := Z.toAmbient '' (Z.structural ⁻¹' {t})
  have hE : E.Finite := (Z.structural.finite_preimage_singleton t).image _
  have hEU' : E ⊆ U' := by
    rintro _ ⟨z, hz, rfl⟩
    by_contra h
    exact ht' ⟨z, h, hz⟩
  have hEV : E ⊆ X.hom ⁻¹ᵁ V := by
    rintro _ ⟨z, hz, rfl⟩
    change X.hom (Z.toAmbient z) ∈ V
    have e : Z.toAmbient ≫ X.hom = Z.structural ≫ T.hom := by
      simp only [HilbertFamily.toAmbient, HilbertFamily.structural, Category.assoc,
        familyProjection_comp]
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, show Z.structural z = t from hz]
    exact hsV
  obtain ⟨U, hU, hEU, hUV⟩ := exists_isAffineOpen_between_of_finite hU' hE hEU' hEV
  refine ⟨⟨V, hV, U, hU, hUV⟩, hsV, ?_⟩
  rintro ⟨z, hz, hzt⟩
  exact hz (hEU ⟨z, hzt, rfl⟩)

end Stacks.Hilbert.OpenChart

namespace Stacks.Hilbert

/-- **Stacks Project, Tag 0B9A, corrected: `X ⟶ S` separated (not registered).** Let `X ⟶ S` be a
separated morphism of schemes and `d ≥ 0`.
Assume that for every `s ∈ S` and all `x₁, …, x_d` in the fibre `X_s` there is an affine open of
`X` containing `x₁, …, x_d`. Then the degree-`d` Hilbert functor `Hilb^d_{X/S}` is representable
by a scheme.

Separatedness is not in the printed statement, but the statement is false without it. Let `X` be
the affine line with doubled origin over a field and `d = 1`, so that the hypothesis is vacuous. A
family of degree one over `T` is a section of `X ×_k T ⟶ T` that is a closed immersion, so
`Hilb^1_{X/k}` is the subfunctor of the functor of points of `X` of the morphisms with closed
graph. This subfunctor contains every field-valued point and is formally étale over `X` (closedness
of a graph is a topological condition, insensitive to nilpotent thickenings), so a representing
scheme would be an étale, surjective monomorphism to `X`, that is `X` itself; but the inclusion of
one of the two charts `𝔸¹ ⊂ X` does not have closed graph. The source's footnote, which treats the
non-separated case, needs an affine open containing `d + 1` points of a fibre. Every case of
Remark 0B9B is separated. -/
theorem exists_representsHilbertFunctorOfRank_of_isSeparated {S : Scheme.{u}} (X : Over S)
    [IsSeparated X.hom] (d : ℕ)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  have hrep := Stacks.OverGluing.isRepresentable_of_openSubfunctors (hilbertFunctorOfRank X d)
    (AffineSpaceChart.isSheaf_zariskiTopology_hilbertFunctorOfRank X)
    (fun i : OpenChart.ChartIndex X ↦ OpenChart.chartSubfunctor d i)
    (fun i ↦ OpenChart.chartSubfunctor_isRepresentable d i)
    (fun i T Z ↦ T.hom ⁻¹ᵁ i.V ⊓
      ⟨(Z.notSupportedLocus i.U)ᶜ, (Z.isClosed_notSupportedLocus i.U).isOpen_compl⟩)
    (fun i T Y Z h ↦ OpenChart.baseChange_mem_chartSubfunctor_iff d i h Z)
    (fun T Z t ↦ OpenChart.exists_chart_mem d hX Z t)
  obtain ⟨H, ⟨R⟩⟩ := hrep.has_representation
  exact ⟨⟨H, representsHilbertFunctorOfRankOfRepresentableBy R⟩⟩

end Stacks.Hilbert

end
