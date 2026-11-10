module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.SectionGysin
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two section Gysin maps of a family of projective lines agree on Chow groups

Let `B` be a scheme locally of finite type over the base scheme `S` of chapter 42, and let `V` be
a family of projective lines over `B`, presented by an isomorphism `Φ : B ×_S 𝐏¹_S ≅ V` over `S`.
The zero section and the infinity section of the family are effective Cartier divisors with
trivial normal bundle (Stacks 0F93), so each of them presents the zero scheme of a global section
of an invertible module and the Gysin map of Stacks 0B6Z may be read along it,
`Stacks.Chow.gysinCycleMapAlong`. The two resulting maps `Z_{k+1}(V) ⟶ Z_k(B)` are genuinely
different on cycles — one takes the fibre of a cycle at `0`, the other at `∞` — but Stacks 02S4
says that the two fibres of an integral closed subscheme of the family are rationally equivalent.
Summing that over the canonical presentation of a cycle by its integral components gives the
statement proved here: **the two Gysin maps agree after passing to the Chow group `A_k(B)`.**

The sum over components is the bookkeeping of Stacks 02S4 part (3), and the comparison at a single
integral component `W ⊆ V` splits into the three positions `W` can take relative to the two
sections. If `W` lies inside the zero section, the vanishing rule of Stacks 0B6Z kills the zero
component, while the infinity fibre of `W` is empty because the two sections are disjoint, so both
components vanish; symmetrically if `W` lies inside the infinity section; and if `W` avoids both
sections, the two components are exactly the two fibre cycles of Stacks 02S4 part (2), whose
difference is rationally equivalent to zero.

## Main results

* `Stacks.Chow.mk_gysinCycleMapAlong_zeroSection_eq_infinitySection` — the two section Gysin maps
  on cycles become equal in the Chow group `A_k(B)`.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinCycleMapComponentAlong_sub` — the
  comparison at a single integral component, with a carrier.
* `Stacks.Chow.support_subset_range_iff_ker_le` — the order/support bridge: a reduced closed
  subscheme is supported inside the image of a closed immersion exactly when the ideal sheaf of
  that closed immersion is contained in its own.

## Implementation notes

### Why the carriers are kept

Rational equivalences are summed over the components by
`Stacks.Chow.rationallyEquivalentToZero_finsum`, which asks for
`Stacks.Chow.IsRationallyEquivalentToZeroWithin`: the witnessing families of the summands must be
jointly locally finite, and only a carrier for each summand guarantees that. So the component
comparison is stated in the carrier-refined form, with the carrier
`Stacks.Chow.fibreCarrier` that Stacks 02S4 part (2) produces anyway, and part (2) is used in its
carrier-refined shape `Stacks.Chow.fibreCyclesRationallyEquivalentWithin`.

That form is not closed under multiplication by the coefficient of the component for free, since
the witnessing family is fixed and only the rational functions on it may change; the closure
property is `Stacks.Chow.isRationallyEquivalentToZeroWithin_zsmul`, proved by replacing each
witnessing rational function by its `n`-th power.

### Why the branch conditions have to be translated

`Stacks.Chow.gysinCycleMapComponentAlong` branches on the order relation
`Z(s) ≤ W` between ideal sheaves on `V`, while Stacks 02S4 part (2) is stated with the
set-theoretic nondegeneracy condition `Set.range W.subschemeι ⊄ Set.range (zeroSection sB)` on the
family. The two are the same condition, and identifying them is
`Stacks.Chow.support_subset_range_iff_ker_le`: for a *reduced* closed subscheme the ideal sheaf is
determined by its support (Stacks 01J3), so containment of ideal sheaves may be read off the
supports, and the support of the ideal sheaf of a closed immersion is its image.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 0F93](https://stacks.math.columbia.edu/tag/0F93)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Two closure properties of rational equivalence within a carrier -/

/-- **Rational equivalence to zero within a carrier is stable under scaling.** If `α` is
rationally equivalent to zero within `T` and the cycle `β` has `n` times the coefficients of `α`,
then `β` is rationally equivalent to zero within `T`.

The witnessing family is unchanged; what changes is the rational function on each member, which
is replaced by its `n`-th power. So the carrier is preserved, which is the point: the scaled
equivalences over the components of a cycle must still be summable. -/
theorem isRationallyEquivalentToZeroWithin_zsmul (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {α β : CycleGroup C p k} {T : Set X}
    (h : IsRationallyEquivalentToZeroWithin C p k α T) (n : ℤ)
    (hβ : ∀ x : X, β.1 x = n * α.1 x) :
    IsRationallyEquivalentToZeroWithin C p k β T := by
  obtain ⟨J, W, hW, hDim, hLocal, hsub, g, hg⟩ := h
  refine ⟨J, W, hW, hDim, hLocal, hsub, fun j ↦ g j ^ n, fun x ↦ ?_⟩
  rw [hβ x, hg x, principalDivisorFamilyCoefficient, principalDivisorFamilyCoefficient,
    mul_finsum]
  refine finsum_congr fun j ↦ ?_
  have _ := hW j
  have _ : IsLocallyNoetherian (W j).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((W j).subschemeι ≫ p)
  exact (Stacks.ChernCap42.principalDivisorPushforward_zpow C p k (W j) (hDim j) (g j) n x).symm

/-! ### The order/support bridge -/

/-- A surjective map detects inclusions between preimages. -/
theorem preimage_subset_preimage_iff_of_surjective {α β : Type*} {h : α → β}
    (hs : Function.Surjective h) {T R : Set β} : h ⁻¹' T ⊆ h ⁻¹' R ↔ T ⊆ R :=
  ⟨fun hsub y hy ↦ by
    obtain ⟨x, rfl⟩ := hs y
    exact hsub hy, fun hsub ↦ Set.preimage_mono hsub⟩

/-- **The order/support bridge, Stacks 01J3.** A reduced closed subscheme `W ⊆ V` is supported
inside the image of a closed immersion `m : A ⟶ V` exactly when the ideal sheaf cut out by `m` is
contained in the ideal sheaf of `W`.

Ideal sheaves are ordered oppositely to their closed subschemes, so `m.ker ≤ W` says that `W` sits
inside the closed subscheme cut out by `m`. One direction is monotonicity of the support; the
other uses that a reduced closed subscheme is the vanishing ideal of its support, which is the
uniqueness half of Stacks 01J3. -/
theorem support_subset_range_iff_ker_le {A V : Scheme.{u}} (m : A ⟶ V) [IsClosedImmersion m]
    (W : V.IdealSheafData) [IsReduced W.subscheme] :
    ((W.support : Set V) ⊆ Set.range m) ↔ m.ker ≤ W := by
  have hrange : (m.ker.support : Set V) = Set.range m := by
    rw [Scheme.Hom.support_ker]
    exact m.isClosedEmbedding.isClosed_range.closure_eq
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hle : W.support ≤ m.ker.support := by
      rw [← SetLike.coe_subset_coe, hrange]
      exact h
    rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme W W.support rfl]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1 hle
  · rw [← hrange]
    exact SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone h)

/-! ### Transport along the presenting isomorphism -/

/-- An isomorphism of schemes is injective on points. -/
theorem injective_base_hom_of_iso {A D : Scheme.{u}} (e : A ≅ D) :
    Function.Injective e.hom.base :=
  (Scheme.homeoOfIso e).injective

/-- An isomorphism of schemes is surjective on points. -/
theorem surjective_base_hom_of_iso {A D : Scheme.{u}} (e : A ≅ D) :
    Function.Surjective e.hom.base :=
  (Scheme.homeoOfIso e).surjective

/-- The image of a morphism is the preimage, under an isomorphism, of the image of the morphism
followed by that isomorphism. -/
theorem range_eq_preimage_range_comp {A D E : Scheme.{u}} (e : D ≅ E) (m : A ⟶ D) :
    Set.range m = e.hom.base ⁻¹' Set.range (m ≫ e.hom) := by
  have hcomp : ∀ a : A, (m ≫ e.hom).base a = e.hom.base (m.base a) := fun _ ↦ rfl
  ext z
  simp only [Set.mem_preimage, Set.mem_range]
  refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
  · obtain ⟨a, ha⟩ := hz
    exact ⟨a, (hcomp a).trans (congrArg e.hom.base ha)⟩
  · obtain ⟨a, ha⟩ := hz
    exact ⟨a, injective_base_hom_of_iso e ((hcomp a).symm.trans ha)⟩

/-- **The branch condition of Stacks 0B6Z read on the family.** For a reduced closed subscheme
`W ⊆ V` and a closed immersion `m` into the family, the pullback `Φ^{-1}W` lies inside the image
of `m` exactly when the ideal sheaf cut out by `m ≫ Φ` is contained in that of `W`.

This is the translation between the two forms of the nondegeneracy condition: the order relation
on ideal sheaves on `V`, which is what `Stacks.Chow.gysinCycleMapComponentAlong` branches on, and
the set-theoretic condition on the family, which is what Stacks 02S4 part (2) asks for. -/
@[ega "I 5.2.4" "special case"]
theorem range_comap_subschemeι_subset_iff {A D V : Scheme.{u}} (e : D ≅ V) (m : A ⟶ D)
    [IsClosedImmersion m] (W : V.IdealSheafData) [IsReduced W.subscheme] :
    Set.range (W.comap e.hom).subschemeι ⊆ Set.range m ↔ (m ≫ e.hom).ker ≤ W := by
  have hcoe : (((W.comap e.hom).support : Set D)) = e.hom.base ⁻¹' (W.support : Set V) := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  rw [Scheme.IdealSheafData.range_subschemeι, hcoe, range_eq_preimage_range_comp e m,
    preimage_subset_preimage_iff_of_surjective (surjective_base_hom_of_iso e),
    support_subset_range_iff_ker_le (m ≫ e.hom) W]

/-- A reduced closed subscheme contained in the image of a closed immersion `m₁` has empty inverse
image along any morphism `m₂` whose image is disjoint from that of `m₁`. -/
theorem isEmpty_subscheme_comap_of_ker_le {A V : Scheme.{u}} (m₁ m₂ : A ⟶ V)
    [IsClosedImmersion m₁] (W : V.IdealSheafData) [IsReduced W.subscheme]
    (hdisj : Disjoint (Set.range m₁) (Set.range m₂)) (h : m₁.ker ≤ W) :
    IsEmpty (W.comap m₂).subscheme := by
  have hsub : (W.support : Set V) ⊆ Set.range m₁ := (support_subset_range_iff_ker_le m₁ W).2 h
  have hcoe : (((W.comap m₂).support : Set A)) = m₂.base ⁻¹' (W.support : Set V) := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hempty : (((W.comap m₂).support : Set A)) = ∅ := by
    rw [hcoe]
    refine Set.eq_empty_of_subset_empty fun z hz ↦ ?_
    exact Set.disjoint_left.mp hdisj (hsub hz) ⟨z, rfl⟩
  refine (Scheme.Hom.ker_eq_top_iff_isEmpty (W.comap m₂).subschemeι).1 ?_
  rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.support_eq_bot_iff,
    ← TopologicalSpace.Closeds.coe_eq_empty]
  exact hempty

/-- The images of the two distinguished sections of a family of projective lines stay disjoint
after transport along an isomorphism presenting the family. -/
theorem disjoint_range_zeroSection_infinitySection_comp {B S V : Scheme.{u}} (sB : B ⟶ S)
    (e : projectiveLineProduct sB ≅ V) :
    Disjoint (Set.range (zeroSection sB ≫ e.hom)) (Set.range (infinitySection sB ≫ e.hom)) := by
  rw [Set.disjoint_left]
  rintro v ⟨b, rfl⟩ ⟨b', hb'⟩
  exact zeroSection_ne_infinitySection sB b b' (injective_base_hom_of_iso e hb'.symm)

/-- **The relative dimension of the transported component.** If an integral closed subscheme
`W ⊆ V` has delta-dimension `k + 1`, then its pullback along the presenting isomorphism has
relative dimension `k + 1` at each of its generic points, read on the family.

This is the dimension hypothesis of Stacks 02S4 part (2) for the transported subscheme: the
pullback is integral, so it has a single generic point, and the delta-dimension of an irreducible
scheme is the relative dimension there. -/
theorem relativeDimension_genericPoints_comap (C : ChowSituation.{u}) {B V : Scheme.{u}}
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (k : ℤ)
    (Φ : projectiveLineProduct sB ≅ V) (hΦ : Φ.hom ≫ sV = familyStructureMorphism sB)
    (W : V.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sV) = ((k + 1 : ℤ) : EInt))
    (ξ : genericPoints (W.comap Φ.hom).subscheme) :
    relativeDimension C.dimensionFunction (familyBase sB (W.comap Φ.hom)) ξ.1 = k + 1 := by
  have _ := hW
  have _ : IsIntegral (W.comap Φ.hom).subscheme :=
    IsIntegral.of_isIso (comapSubschemeIsoOfIsIso Φ.hom W).inv
  have hξ : (ξ : (W.comap Φ.hom).subscheme) = genericPoint (W.comap Φ.hom).subscheme := by
    have hmem : (ξ : (W.comap Φ.hom).subscheme) ∈
        ({genericPoint (W.comap Φ.hom).subscheme} : Set (W.comap Φ.hom).subscheme) := by
      rw [← genericPoints_eq_singleton]
      exact ξ.2
    exact hmem
  have hiso : (comapSubschemeIsoOfIsIso Φ.hom W).hom ≫ (W.subschemeι ≫ sV) =
      familyBase sB (W.comap Φ.hom) := by
    rw [← Category.assoc, comapSubschemeIsoOfIsIso_hom_subschemeι, Category.assoc, hΦ]
  have hsd := schemeDeltaDimension_of_iso C (familyBase sB (W.comap Φ.hom))
    (W.subschemeι ≫ sV) (comapSubschemeIsoOfIsIso Φ.hom W) hiso
  have hgen := schemeDeltaDimension_eq_genericPoint C (familyBase sB (W.comap Φ.hom))
  rw [← hsd, hDim] at hgen
  rw [hξ]
  exact (WithBotTop.coe_injective hgen).symm

/-! ### The comparison at a single integral component -/

/-- If `W` lies inside the zero scheme of the first section, then, the two sections having
disjoint images, the component cycles of Stacks 0B6Z along both sections vanish. -/
private theorem gysinCycleMapComponentAlong_eq_zero_of_le_of_disjoint (C : ChowSituation.{u})
    {B V : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sV : V ⟶ C.S)
    [LocallyOfFiniteType sV] (k : ℤ) (m₁ m₂ : B ⟶ V) [IsClosedImmersion m₁] (L₁ L₂ : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L₁]
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L₂]
    (s₁ : Γ(L₁, ⊤)) (s₂ : Γ(L₂, ⊤)) (hker : m₁.ker = Stacks.Divisors.zeroScheme V L₁ s₁)
    (W : V.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sV) = ((k + 1 : ℤ) : EInt))
    (hdisj : Disjoint (Set.range m₁) (Set.range m₂))
    (h : Stacks.Divisors.zeroScheme V L₁ s₁ ≤ W) :
    gysinCycleMapComponentAlong C sV sB k L₁ s₁ m₁ W hW hDim = 0 ∧
      gysinCycleMapComponentAlong C sV sB k L₂ s₂ m₂ W hW hDim = 0 := by
  have _ := hW
  refine ⟨gysinCycleMapComponentAlong_of_le C sV sB k L₁ s₁ _ W hW hDim h, ?_⟩
  have _ : IsEmpty (W.comap m₂).subscheme :=
    isEmpty_subscheme_comap_of_ker_le m₁ m₂ W hdisj (hker.trans_le h)
  by_cases h₂ : Stacks.Divisors.zeroScheme V L₂ s₂ ≤ W
  · exact gysinCycleMapComponentAlong_of_le C sV sB k L₂ s₂ _ W hW hDim h₂
  · rw [gysinCycleMapComponentAlong_of_not_le C sV sB k L₂ s₂ _ W hW hDim h₂]
    exact cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty C sB _ k

/-- **The comparison of the two section Gysin rules at one integral component.** Let `W ⊆ V` be an
integral closed subscheme of delta-dimension `k + 1` of a family of projective lines presented by
`Φ`, and let `n` be an integer. Then `n` times the difference of the two component cycles of
Stacks 0B6Z, read along the zero section and along the infinity section, is rationally equivalent
to zero within the carrier of `W` in `B`.

Three cases. If `W` lies inside the zero section, the vanishing rule of Stacks 0B6Z kills the zero
component and the infinity fibre of `W` is empty, the two sections being disjoint, so the
difference is zero; symmetrically if `W` lies inside the infinity section. If `W` lies inside
neither, the two component cycles are the cycles of the two fibres of `Φ^{-1}W`, and their
difference is rationally equivalent to zero by Stacks 02S4 part (2). -/
theorem isRationallyEquivalentToZeroWithin_gysinCycleMapComponentAlong_sub
    (C : ChowSituation.{u}) {B V : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (k : ℤ)
    (Φ : projectiveLineProduct sB ≅ V) (hΦ : Φ.hom ≫ sV = familyStructureMorphism sB)
    (L₀ : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L₀]
    (s₀ : Γ(L₀, ⊤)) (hker₀ : (zeroSection sB ≫ Φ.hom).ker = Stacks.Divisors.zeroScheme V L₀ s₀)
    (LI : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property LI]
    (sI : Γ(LI, ⊤))
    (hkerI : (infinitySection sB ≫ Φ.hom).ker = Stacks.Divisors.zeroScheme V LI sI)
    (W : V.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sV) = ((k + 1 : ℤ) : EInt)) (n : ℤ) :
    IsRationallyEquivalentToZeroWithin C sB k
      (n • (gysinCycleMapComponentAlong C sV sB k L₀ s₀ (zeroSection sB ≫ Φ.hom) W hW hDim -
        gysinCycleMapComponentAlong C sV sB k LI sI (infinitySection sB ≫ Φ.hom) W hW hDim))
      (fibreCarrier C sB (W.comap Φ.hom)) := by
  have _ := hW
  have hint : IsIntegral (W.comap Φ.hom).subscheme :=
    IsIntegral.of_isIso (comapSubschemeIsoOfIsIso Φ.hom W).inv
  have hdisj := disjoint_range_zeroSection_infinitySection_comp sB Φ
  by_cases h₀ : Stacks.Divisors.zeroScheme V L₀ s₀ ≤ W
  · obtain ⟨hz, hi⟩ := gysinCycleMapComponentAlong_eq_zero_of_le_of_disjoint C sB sV k
      (zeroSection sB ≫ Φ.hom) (infinitySection sB ≫ Φ.hom) L₀ LI s₀ sI hker₀ W hW hDim hdisj h₀
    rw [hz, hi, sub_zero, smul_zero]
    exact isRationallyEquivalentToZeroWithin_zero C sB k _
  by_cases hI : Stacks.Divisors.zeroScheme V LI sI ≤ W
  · obtain ⟨hi, hz⟩ := gysinCycleMapComponentAlong_eq_zero_of_le_of_disjoint C sB sV k
      (infinitySection sB ≫ Φ.hom) (zeroSection sB ≫ Φ.hom) LI L₀ sI s₀ hkerI W hW hDim
      hdisj.symm hI
    rw [hz, hi, sub_zero, smul_zero]
    exact isRationallyEquivalentToZeroWithin_zero C sB k _
  · have hnz : ¬ Set.range (W.comap Φ.hom).subschemeι ⊆ Set.range (zeroSection sB) := fun hc ↦
      h₀ (hker₀.symm.trans_le ((range_comap_subschemeι_subset_iff Φ (zeroSection sB) W).1 hc))
    have hni :
        ¬ Set.range (W.comap Φ.hom).subschemeι ⊆ Set.range (infinitySection sB) := fun hc ↦
      hI (hkerI.symm.trans_le
        ((range_comap_subschemeι_subset_iff Φ (infinitySection sB) W).1 hc))
    rw [gysinCycleMapComponentAlong_of_not_le C sV sB k L₀ s₀ _ W hW hDim h₀,
      gysinCycleMapComponentAlong_of_not_le C sV sB k LI sI _ W hW hDim hI,
      Scheme.IdealSheafData.comap_comp W (zeroSection sB) Φ.hom,
      Scheme.IdealSheafData.comap_comp W (infinitySection sB) Φ.hom]
    refine isRationallyEquivalentToZeroWithin_zsmul C sB k
      (fibreCyclesRationallyEquivalentWithin C sB k (W.comap Φ.hom) hint
        (relativeDimension_genericPoints_comap C sB sV k Φ hΦ W hW hDim) hnz hni) n fun y ↦ rfl

/-! ### The two Gysin maps agree on Chow groups -/

/-- The coefficients of a section Gysin map at a point are the locally finite sum of the
coefficients of the component cycles of the canonical presentation of the cycle. -/
private theorem gysinCycleMapAlong_apply_and_finite_support (C : ChowSituation.{u})
    {B V : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sV : V ⟶ C.S)
    [LocallyOfFiniteType sV] (k : ℤ) (m : B ⟶ V) [IsClosedImmersion m] (L : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme V L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme V L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme V L s).subschemeι).obj L))
    (hq : m ≫ sV = sB) (hker : m.ker = Stacks.Divisors.zeroScheme V L s)
    (δ : CycleGroup C sV (k + 1)) (y : B) :
    (gysinCycleMapAlong C sV sB k L s m htriv hq hker δ).1 y =
        ∑ᶠ x : cycleSupportIndex δ, δ.1 x.1 *
          (gysinCycleMapComponentAlong C sV sB k L s m (integralComponentAt x.1)
            (isIntegral_integralComponentAt x.1)
            (schemeDeltaDimension_cycleSupportIndex δ x)).1 y ∧
      (Function.support fun x : cycleSupportIndex δ ↦ δ.1 x.1 *
        (gysinCycleMapComponentAlong C sV sB k L s m (integralComponentAt x.1)
          (isIntegral_integralComponentAt x.1)
          (schemeDeltaDimension_cycleSupportIndex δ x)).1 y).Finite := by
  refine ⟨gysinCycleMapAlong_apply_of_presentation C sV sB k L s m htriv hq hker
    (fun x : cycleSupportIndex δ ↦ integralComponentAt x.1)
    (fun x ↦ isIntegral_integralComponentAt x.1)
    (fun x ↦ schemeDeltaDimension_cycleSupportIndex δ x)
    (locallyFinite_support_integralComponentAt δ) (fun x ↦ δ.1 x.1) δ
    (cycle_eq_finsum_primeCycles δ) y, ?_⟩
  refine finite_support_of_locallyFinite
    (fun x : cycleSupportIndex δ ↦ m.base ⁻¹' ((integralComponentAt x.1).support : Set V))
    ((locallyFinite_support_integralComponentAt δ).preimage_continuous m.continuous)
    (fun x y' ↦ δ.1 x.1 *
      (gysinCycleMapComponentAlong C sV sB k L s m (integralComponentAt x.1)
        (isIntegral_integralComponentAt x.1) (schemeDeltaDimension_cycleSupportIndex δ x)).1 y')
    (fun x y' hy' ↦ ?_) y
  exact support_gysinCycleMapComponentAlong_subset C sV sB k L s m (integralComponentAt x.1)
    (isIntegral_integralComponentAt x.1) (schemeDeltaDimension_cycleSupportIndex δ x)
    (right_ne_zero_of_mul hy')

/-- **Stacks 02S4 read through the Gysin map of Stacks 0B6Z.** Let `V` be a family of projective
lines over `B`, presented by an isomorphism `Φ : B ×_S 𝐏¹_S ≅ V` over the base, and let
`(L₀, s₀)` and `(L_∞, s_∞)` present the zero section and the infinity section as zero schemes of
sections of invertible modules with trivial restriction, as Stacks 0F93 provides. Then the two
Gysin maps on cycles of Stacks 0B6Z, read along the two sections, agree after passing to the Chow
group `A_k(B)`.

Both maps are coefficientwise extensions of a rule on integral components, so the difference of
their values on a cycle `δ` is the locally finite sum, over the components of `δ`, of the
differences of the two component rules weighted by the coefficients of `δ`; each summand is
rationally equivalent to zero by
`Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinCycleMapComponentAlong_sub`, and the carriers
make the sum of the equivalences an equivalence. -/
theorem mk_gysinCycleMapAlong_zeroSection_eq_infinitySection
    (C : ChowSituation.{u}) {B V : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (k : ℤ)
    (Φ : projectiveLineProduct sB ≅ V) (hΦ : Φ.hom ≫ sV = familyStructureMorphism sB)
    (L₀ : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L₀]
    (s₀ : Γ(L₀, ⊤))
    (htriv₀ : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme V L₀ s₀).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme V L₀ s₀).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme V L₀ s₀).subschemeι).obj L₀))
    (hker₀ : (zeroSection sB ≫ Φ.hom).ker = Stacks.Divisors.zeroScheme V L₀ s₀)
    (LI : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property LI]
    (sI : Γ(LI, ⊤))
    (htrivI : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme V LI sI).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme V LI sI).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme V LI sI).subschemeι).obj LI))
    (hkerI : (infinitySection sB ≫ Φ.hom).ker = Stacks.Divisors.zeroScheme V LI sI)
    (δ : CycleGroup C sV (k + 1)) :
    (QuotientAddGroup.mk (gysinCycleMapAlong C sV sB k L₀ s₀ (zeroSection sB ≫ Φ.hom) htriv₀
        (by rw [Category.assoc, hΦ, zeroSection_comp_familyStructureMorphism]) hker₀ δ)
          : chowGroup C sB k) =
      QuotientAddGroup.mk (gysinCycleMapAlong C sV sB k LI sI (infinitySection sB ≫ Φ.hom) htrivI
        (by rw [Category.assoc, hΦ, infinitySection_comp_familyStructureMorphism]) hkerI δ) := by
  classical
  have hq₀ : (zeroSection sB ≫ Φ.hom) ≫ sV = sB := by
    rw [Category.assoc, hΦ, zeroSection_comp_familyStructureMorphism]
  have hqI : (infinitySection sB ≫ Φ.hom) ≫ sV = sB := by
    rw [Category.assoc, hΦ, infinitySection_comp_familyStructureMorphism]
  rw [QuotientAddGroup.eq_iff_sub_mem, mem_rationalEquivalences]
  refine rationallyEquivalentToZero_finsum C sB k
    (fun x : cycleSupportIndex δ ↦ δ.1 x.1 •
      (gysinCycleMapComponentAlong C sV sB k L₀ s₀ (zeroSection sB ≫ Φ.hom)
          (integralComponentAt x.1) (isIntegral_integralComponentAt x.1)
          (schemeDeltaDimension_cycleSupportIndex δ x) -
        gysinCycleMapComponentAlong C sV sB k LI sI (infinitySection sB ≫ Φ.hom)
          (integralComponentAt x.1) (isIntegral_integralComponentAt x.1)
          (schemeDeltaDimension_cycleSupportIndex δ x)))
    (fun x ↦ fibreCarrier C sB ((integralComponentAt x.1).comap Φ.hom)) ?_ ?_ ?_
  · refine locallyFinite_fibreCarrier C sB
      (fun x : cycleSupportIndex δ ↦ (integralComponentAt x.1).comap Φ.hom) ?_
    refine ((locallyFinite_support_integralComponentAt δ).preimage_continuous
      Φ.hom.continuous).subset fun x ↦ ?_
    rw [Scheme.IdealSheafData.support_comap]
    exact subset_rfl
  · exact fun x ↦ isRationallyEquivalentToZeroWithin_gysinCycleMapComponentAlong_sub C sB sV k
      Φ hΦ L₀ s₀ hker₀ LI sI hkerI (integralComponentAt x.1)
      (isIntegral_integralComponentAt x.1) (schemeDeltaDimension_cycleSupportIndex δ x) (δ.1 x.1)
  · intro y
    obtain ⟨hA, hfin₀⟩ := gysinCycleMapAlong_apply_and_finite_support C sB sV k
      (zeroSection sB ≫ Φ.hom) L₀ s₀ htriv₀ hq₀ hker₀ δ y
    obtain ⟨hB, hfinI⟩ := gysinCycleMapAlong_apply_and_finite_support C sB sV k
      (infinitySection sB ≫ Φ.hom) LI sI htrivI hqI hkerI δ y
    change (gysinCycleMapAlong C sV sB k L₀ s₀ (zeroSection sB ≫ Φ.hom) htriv₀ hq₀ hker₀ δ).1 y -
        (gysinCycleMapAlong C sV sB k LI sI (infinitySection sB ≫ Φ.hom) htrivI hqI hkerI δ).1 y
      = _
    rw [hA, hB, ← finsum_sub_distrib hfin₀ hfinI]
    exact finsum_congr fun x ↦ (mul_sub _ _ _).symm

end Stacks.Chow

end
