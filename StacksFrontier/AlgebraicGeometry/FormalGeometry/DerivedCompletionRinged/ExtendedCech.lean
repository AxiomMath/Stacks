module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdeal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LeftAdjoint
public import StacksFrontier.RingTheory.Cech.Extended
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingCriterion

/-!
# The extended alternating Čech complex of sheaves of modules on a ringed site

Let `(C, 𝒪)` be a ringed site and let `f_1, …, f_r` be global sections of `𝒪`. Writing
`f_S = ∏_{i ∈ S} f_i` for `S ⊆ {1, …, r}` and `𝒪_{f_S}` for the sheaf obtained by inverting it,
the extended alternating Čech complex of sheaves of `𝒪`-modules is

`𝒪 → ∏_{i₀} 𝒪_{f_{i₀}} → ∏_{i₀ < i₁} 𝒪_{f_{i₀} f_{i₁}} → ⋯ → 𝒪_{f_1 ⋯ f_r}`,

with `∏_{|S| = p} 𝒪_{f_S}` in degree `p` and the alternating differential assembled from the
localization maps `𝒪_{f_S} ⟶ 𝒪_{f_T}` for `S ⊆ T`. Its degree-zero term is `𝒪_{f_∅} = 𝒪_1`, and
`𝒪 ⟶ 𝒪_{f_∅}` is the augmentation.

## Main definitions

* `SheafOfModules.unitRestrictScalarsMapOfComp`: a map `A ⟶ B` of sheaves of rings over `R`,
  viewed as a map of sheaves of `R`-modules, and `SheafOfModules.unitIsoRestrictScalarsUnit`
  for an isomorphism.
* `CategoryTheory.AlternatingCech.complex`: the extended alternating Čech complex of a functor on
  the poset of subsets of `Fin r`, as a cochain complex indexed by `ℤ`.
* `AlgebraicGeometry.RingedSite.awayModuleTransition`: the localization map
  `𝒪_{f_S} ⟶ 𝒪_{f_T}` for `S ⊆ T`, as a map of sheaves of `𝒪`-modules.
* `AlgebraicGeometry.RingedSite.awayLocalizationFunctor`: the system `S ↦ 𝒪_{f_S}` as a functor on
  the poset of subsets of `Fin r`.
* `AlgebraicGeometry.RingedSite.extendedAlternatingCech`: the extended alternating Čech complex of
  sheaves of `𝒪`-modules.
* `AlgebraicGeometry.RingedSite.extendedAlternatingCechAugmentation`: the map from `𝒪` into its
  degree-zero term.
* `AlgebraicGeometry.RingedSite.awaySheafIsoOfIsUnit`: `𝒪 ≅ 𝒪_f` when `f` is already
  invertible, specialised to `f_∅ = 1` by
  `AlgebraicGeometry.RingedSite.structureSheafIsoAwayEmpty` and
  `AlgebraicGeometry.RingedSite.unitIsoAwayModuleEmpty`, which identify the degree-zero term
  `𝒪_{f_∅}` with `𝒪`.

## Main results

* `CategoryTheory.AlternatingCech.d_comp_d`: the alternating differential squares to zero.
* `CategoryTheory.AlternatingCech.isEmpty_idx_of_neg` and
  `CategoryTheory.AlternatingCech.isEmpty_idx_of_lt`: the complex is concentrated in degrees
  `0, …, r`, because there is no subset of `Fin r` of negative cardinality or of cardinality
  larger than `r`.
* `AlgebraicGeometry.RingedSite.eq_awayTransition`: the transition map is pinned by the property
  that defines it — every map of sheaves of rings `𝒪_{f_S} ⟶ 𝒪_{f_T}` over `𝒪` equals it.
* `AlgebraicGeometry.RingedSite.awayModuleTransition_comp`: the localization maps compose, which
  is what makes the alternating differential square to zero.
* `AlgebraicGeometry.RingedSite.unitToAwayModule_comp_awayModuleTransition`: the augmentation is
  compatible with the localization maps.
* `AlgebraicGeometry.RingedSite.unitIsoAwayModuleEmpty_hom`: the augmentation is that
  identification of the degree-zero term with `𝒪`, read in the unique factor.

## Implementation notes

The degree-`p` term is indexed by the subtype `{S : Finset (Fin r) // (S.card : ℤ) = p}` rather
than by strictly increasing `p`-tuples. Two reasons: the transition maps are indexed by
inclusions, and `T.erase k ⊆ T` is immediate for a finset while for a tuple it involves an
order-shifting reindex; and the sign cancellation behind `d ∘ d = 0` is then exactly
`Finset.erase_right_comm`, so `ExtendedAlternatingCech.cechSign_mul_swap` — proved for the
ring-level complex of `StacksFrontier/RingTheory/Cech/Extended.lean` — applies verbatim. Indexing
the degrees by `ℤ` through the cardinality of a subset also means no term needs a case
distinction: the index type is empty outside `0 ≤ p ≤ r`, so the complex is automatically
concentrated there.

The combinatorics is isolated from the sheaf theory by stating it for an arbitrary functor
`F : Finset (Fin r) ⥤ 𝒜` into a preadditive category with finite products. A functor on the
subset poset is precisely a family of objects with transition maps that compose, since the
hom types of a poset are subsingletons; the cocycle identity that the differential needs is
`CategoryTheory.Functor.map_comp`.

`𝒪_{f_S}` is a sheaf of `𝒪`-modules by restriction of scalars along `𝒪 ⟶ 𝒪_{f_S}`, as
`AlgebraicGeometry.RingedSite.awayModule`, and a map of sheaves of rings `𝒪_{f_S} ⟶ 𝒪_{f_T}`
over `𝒪` induces a map of sheaves of `𝒪`-modules between them. Mathlib has no such
construction — `SheafOfModules.restrictScalars` comes with neither a composition isomorphism nor
anything relating it to `SheafOfModules.unit` — so it is built here, sectionwise, from the
underlying additive map of the ring homomorphism; the pattern is that of
`SheafOfModules.unitToPushforwardObjUnit`.

The transition maps themselves are not constructed but chosen, by the universal property
`AlgebraicGeometry.RingedSite.existsUnique_awayTransition`. Uniqueness is what gives the three
identities a localization system needs: a transition along `S ⊆ S` is the identity, and
transitions compose, both because the maps in question lift the same map out of `𝒪`.

That the choice is harmless is itself a statement, and it is
`AlgebraicGeometry.RingedSite.eq_awayTransition`: *every* map of sheaves of rings
`𝒪_{f_S} ⟶ 𝒪_{f_T}` over `𝒪` equals `awayTransition f hST`. So `Classical.choice` names here a
map that the property `toAwaySheaf_comp_awayTransition` determines up to equality, and no
statement about the complex below can depend on which map was returned — in particular the
differential of `extendedAlternatingCech` is the differential of the Čech complex and not of
some other complex that happens to be assembled from arbitrary maps.

No `@[stacks]` attribute is attached here. This is the construction that [Stacks, Tag 099B]
needs, not that tag, which is carried by
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_forall_isNilpotent` of
`NilpotentIdeal.lean` for an ideal sheaf with nilpotent local sections and by
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_generatedIdealSheaf` of
`GeneratedIdealAdjoint.lean` for the ideal sheaf generated by `f_1, …, f_r` themselves, with no
hypothesis beyond the ambient ringed site. The completion
functor `K ↦ R𝑆heafHom_𝒪(Č(f), K)` and its universal property further require
[Stacks, Tag 0997] in full together with [Stacks, Tag 0998].
**Both are present**: 0997 is registered in all three of its implications —
`isZero_derivedSheafHom_awayRestrictScalars_of_isZero` (VanishingCriterionCoextension.lean),
`isZero_derivedSheafHom_derivedAwayModule_iff_isDerivedCompleteAt`
(VanishingCriterionTelescope.lean) and
`isZero_derivedSheafHom_derivedAwayModule_of_forall` (VanishingCriterion.lean) — and 0998 has
registrants in `VanishingIdeal.lean`, `AwayAddShortExact.lean`, `VanishingIdealLocal.lean` and
`SliceRestrictionDescent.lean`. What is still open is [Stacks, Tag 099F] for an ideal sheaf that
is only *locally* generated by finitely many sections; the dependency-ordered account of that is
the "What remains for Tag 099F" note of `GeneratedIdealAdjoint.lean`.

## References

* [Stacks Project, Tag 0G6F](https://stacks.math.columbia.edu/tag/0G6F)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 0997](https://stacks.math.columbia.edu/tag/0997)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R A B D : Sheaf J RingCat.{w}}

/-- Sectionwise linearity of a map of sheaves of rings over `R`: it carries the `R`-action on `A`
to the `R`-action on `B` because both are given by multiplication by the image of a section. -/
private theorem map_smul_aux {αA : R ⟶ A} {αB : R ⟶ B} (β : A ⟶ B) (h : αA ≫ β = αB) (U : Cᵒᵖ)
    (r : R.obj.obj U) (a : A.obj.obj U) :
    (αB.hom.app U).hom r * (β.hom.app U).hom a =
      (β.hom.app U).hom ((αA.hom.app U).hom r * a) := by
  rw [(β.hom.app U).hom.map_mul, ← h]
  rfl

/-- A map `β : A ⟶ B` of sheaves of rings over `R`, viewed as a map `A ⟶ B` of sheaves of
`R`-modules. -/
def unitRestrictScalarsMapOfComp {αA : R ⟶ A} {αB : R ⟶ B} (β : A ⟶ B) (h : αA ≫ β = αB) :
    (restrictScalars.{w} αA).obj (unit A) ⟶ (restrictScalars.{w} αB).obj (unit B) where
  val.app U := ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (β.hom.app U))
    (fun r ↦ by ext a; exact map_smul_aux β h U r a)
  val.naturality g := by
    ext a
    exact congrArg (fun φ ↦ (RingCat.Hom.hom φ) a) (β.hom.naturality g)

/-- `unitRestrictScalarsMapOfComp` depends only on the underlying map of sheaves of rings. -/
theorem unitRestrictScalarsMap_congr {αA : R ⟶ A} {αB : R ⟶ B} {β β' : A ⟶ B}
    (h : αA ≫ β = αB) (h' : αA ≫ β' = αB) (hββ' : β = β') :
    unitRestrictScalarsMapOfComp β h = unitRestrictScalarsMapOfComp β' h' := by
  subst hββ'; rfl

/-- The identity of `A` induces the identity of `A` as a sheaf of `R`-modules. -/
theorem unitRestrictScalarsMap_id {αA : R ⟶ A} (h : αA ≫ 𝟙 A = αA) :
    unitRestrictScalarsMapOfComp (𝟙 A) h = 𝟙 ((restrictScalars.{w} αA).obj (unit A)) :=
  rfl

/-- Maps of sheaves of rings over `R` compose as maps of sheaves of `R`-modules. -/
theorem unitRestrictScalarsMap_comp {αA : R ⟶ A} {αB : R ⟶ B} {αD : R ⟶ D}
    {β : A ⟶ B} (h : αA ≫ β = αB) {δ : B ⟶ D} (h' : αB ≫ δ = αD)
    (h'' : αA ≫ (β ≫ δ) = αD) :
    unitRestrictScalarsMapOfComp β h ≫ unitRestrictScalarsMapOfComp δ h' =
      unitRestrictScalarsMapOfComp (β ≫ δ) h'' :=
  rfl

/-- A map `γ : R ⟶ B` of sheaves of rings, viewed as a map `R ⟶ B` of sheaves of
`R`-modules. -/
def unitToRestrictScalarsUnit (γ : R ⟶ B) :
    unit R ⟶ (restrictScalars.{w} γ).obj (unit B) where
  val.app U := ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (γ.hom.app U))
    (fun r ↦ by ext a; exact map_smul_aux γ (Category.id_comp γ) U r a)
  val.naturality g := by
    ext
    exact congrArg (fun φ ↦ (RingCat.Hom.hom φ) 1) (γ.hom.naturality g)

/-- The maps out of the unit sheaf are compatible with the maps of sheaves of rings over `R`. -/
theorem unitToRestrictScalarsUnit_comp {αA : R ⟶ A} {αB : R ⟶ B} {β : A ⟶ B}
    (h : αA ≫ β = αB) :
    unitToRestrictScalarsUnit αA ≫ unitRestrictScalarsMapOfComp β h =
      unitToRestrictScalarsUnit αB := by
  subst h; rfl

/-- A map `δ : B ⟶ R` of sheaves of rings retracting `γ : R ⟶ B`, viewed as a map `B ⟶ R` of
sheaves of `R`-modules. -/
def restrictScalarsUnitToUnit {γ : R ⟶ B} (δ : B ⟶ R) (h : γ ≫ δ = 𝟙 R) :
    (restrictScalars.{w} γ).obj (unit B) ⟶ unit R :=
  unitRestrictScalarsMapOfComp δ h

/-- An isomorphism `R ≅ B` of sheaves of rings is an isomorphism `R ≅ B` of sheaves of
`R`-modules. -/
def unitIsoRestrictScalarsUnit (e : R ≅ B) :
    unit R ≅ (restrictScalars.{w} e.hom).obj (unit B) where
  hom := unitToRestrictScalarsUnit e.hom
  inv := restrictScalarsUnitToUnit e.inv e.hom_inv_id
  hom_inv_id := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
    ext
    exact congrArg (fun φ : R ⟶ R ↦ (φ.hom.app U).hom 1) e.hom_inv_id
  inv_hom_id := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
    ext x
    exact congrArg (fun φ : B ⟶ B ↦ (φ.hom.app U).hom x) e.inv_hom_id

end SheafOfModules

namespace CategoryTheory.AlternatingCech

variable {r : ℕ}

/-- The index type of the degree-`p` term of the extended alternating Čech complex on `r`
sections: the subsets of `Fin r` of cardinality `p`. It is empty unless `0 ≤ p ≤ r`. -/
abbrev Idx (r : ℕ) (p : ℤ) := {S : Finset (Fin r) // (S.card : ℤ) = p}

/-- There is no subset of negative cardinality. -/
theorem isEmpty_idx_of_neg {p : ℤ} (hp : p < 0) : IsEmpty (Idx r p) :=
  ⟨fun S ↦ by have := S.2; omega⟩

/-- There is no subset of `Fin r` of cardinality larger than `r`. -/
theorem isEmpty_idx_of_lt {p : ℤ} (hp : (r : ℤ) < p) : IsEmpty (Idx r p) :=
  ⟨fun S ↦ by
    have h1 := S.2
    have h2 : S.1.card ≤ r := by simpa using Finset.card_le_univ S.1
    omega⟩

/-- The empty set is the unique subset of cardinality zero. -/
instance uniqueIdxZero : Unique (Idx r 0) where
  default := ⟨∅, by simp⟩
  uniq S := Subtype.ext (Finset.card_eq_zero.mp (by have := S.2; omega))

/-- Removing an element of `T` from a subset of cardinality `p + 1` gives one of cardinality
`p`. -/
def Idx.erase {p : ℤ} (T : Idx r (p + 1)) (k : T.1) : Idx r p :=
  ⟨T.1.erase k, by
    have h := T.2
    have h1 : 1 ≤ T.1.card := Finset.card_pos.mpr ⟨k.1, k.2⟩
    rw [Finset.card_erase_of_mem k.2]
    omega⟩

/-- The underlying finset of `T.erase k` is `T.1.erase k`. -/
@[simp]
theorem Idx.val_erase {p : ℤ} (T : Idx r (p + 1)) (k : T.1) :
    (T.erase k).1 = T.1.erase k :=
  rfl

/-- The subset `T.erase k` is contained in `T`. -/
theorem Idx.erase_subset {p : ℤ} (T : Idx r (p + 1)) (k : T.1) : (T.erase k).1 ⊆ T.1 :=
  Finset.erase_subset _ _

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasFiniteProducts 𝒜]

/-- The degree-`p` term of the extended alternating Čech complex of a system `F` of objects
indexed by the subsets of `Fin r`: the product of `F.obj S` over the subsets of cardinality
`p`. -/
abbrev term (F : Finset (Fin r) ⥤ 𝒜) (p : ℤ) : 𝒜 := ∏ᶜ fun S : Idx r p => F.obj S.1

/-- The projection of the degree-`p` term onto the factor indexed by `A`, followed by the
transition map into `F.obj W` for `A ⊆ W`. -/
def proj (F : Finset (Fin r) ⥤ 𝒜) {p : ℤ} (A : Idx r p) {W : Finset (Fin r)}
    (h : A.1 ⊆ W) : term F p ⟶ F.obj W :=
  Pi.π (fun S : Idx r p => F.obj S.1) A ≫ F.map (homOfLE h)

omit [Preadditive 𝒜] in
/-- `proj` depends on the inclusion only through its source. -/
theorem proj_congr (F : Finset (Fin r) ⥤ 𝒜) {p : ℤ} {W : Finset (Fin r)} {A A' : Idx r p}
    (hAA' : A = A') {h : A.1 ⊆ W} {h' : A'.1 ⊆ W} : proj F A h = proj F A' h' := by
  subst hAA'; rfl

omit [Preadditive 𝒜] in
/-- Composing `proj` with a further transition map gives `proj` for the composite inclusion. -/
theorem proj_comp_map (F : Finset (Fin r) ⥤ 𝒜) {p : ℤ} (A : Idx r p) {W W' : Finset (Fin r)}
    (h : A.1 ⊆ W) (h' : W ⊆ W') (h'' : A.1 ⊆ W') :
    proj F A h ≫ F.map (homOfLE h') = proj F A h'' := by
  rw [proj, proj, Category.assoc, ← F.map_comp, homOfLE_comp]

/-- The differential of the extended alternating Čech complex: its component at a subset `T` of
cardinality `p + 1` is the alternating sum, over the elements `k` of `T`, of the transition maps
out of the factors indexed by `T ∖ {k}`. -/
def d (F : Finset (Fin r) ⥤ 𝒜) (p : ℤ) : term F p ⟶ term F (p + 1) :=
  Pi.lift fun T ↦ ∑ k ∈ T.1.attach, Cech.cechSign T.1 k.1 •
    proj F (T.erase k) (T.erase_subset k)

/-- The component of the differential at a subset of cardinality `p + 1`. -/
theorem d_comp_pi (F : Finset (Fin r) ⥤ 𝒜) (p : ℤ) (T : Idx r (p + 1)) :
    d F p ≫ Pi.π (fun S : Idx r (p + 1) => F.obj S.1) T =
      ∑ k ∈ T.1.attach, Cech.cechSign T.1 k.1 • proj F (T.erase k) (T.erase_subset k) :=
  Pi.lift_π _ _

/-- The differential followed by a transition map out of the factor indexed by `T`. -/
theorem d_comp_proj (F : Finset (Fin r) ⥤ 𝒜) {p : ℤ} (T : Idx r (p + 1))
    {W : Finset (Fin r)} (h : T.1 ⊆ W) :
    d F p ≫ proj F T h = ∑ k ∈ T.1.attach, Cech.cechSign T.1 k.1 •
      proj F (T.erase k) ((T.erase_subset k).trans h) := by
  rw [proj, ← Category.assoc, d_comp_pi, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun k _ ↦ by
    rw [Preadditive.zsmul_comp, proj_comp_map F (T.erase k) _ h]

/-- **The alternating differential squares to zero.** At a subset `V` of cardinality `p + 2` the
composite is a double sum over the ordered pairs of distinct elements of `V`, and the two terms
of a pair differ by a sign because removing two elements in either order gives the same
subset. -/
theorem d_comp_d (F : Finset (Fin r) ⥤ 𝒜) (p : ℤ) : d F p ≫ d F (p + 1) = 0 := by
  apply Pi.hom_ext
  intro V
  rw [zero_comp, Category.assoc, d_comp_pi, Preadditive.comp_sum]
  have step : ∀ l ∈ V.1.attach,
      d F p ≫ (Cech.cechSign V.1 l.1 • proj F (V.erase l) (V.erase_subset l)) =
        ∑ k ∈ (V.erase l).1.attach,
          (Cech.cechSign V.1 l.1 * Cech.cechSign (V.erase l).1 k.1) •
            proj F ((V.erase l).erase k)
              (((V.erase l).erase_subset k).trans (V.erase_subset l)) := by
    intro l _
    rw [Preadditive.comp_zsmul, d_comp_proj, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ smul_smul _ _ _
  rw [Finset.sum_congr rfl step, Finset.sum_sigma']
  refine Finset.sum_involution
    (g := fun a _ ↦ (⟨⟨a.2.1, Finset.mem_of_mem_erase a.2.2⟩,
        ⟨a.1.1, Finset.mem_erase.mpr
          ⟨fun hh ↦ (Finset.ne_of_mem_erase a.2.2) (by simpa using hh.symm), a.1.2⟩⟩⟩ :
      (l : ↥(V.1)) × ↥((V.erase l).1))) ?_ ?_ ?_ ?_
  · rintro ⟨l, k⟩ -
    dsimp only
    have hkl : k.1 ≠ l.1 := Finset.ne_of_mem_erase k.2
    have hkV : k.1 ∈ V.1 := Finset.mem_of_mem_erase k.2
    have hlk : l.1 ∈ V.1.erase k.1 := Finset.mem_erase.mpr ⟨hkl.symm, l.2⟩
    have hidx : (V.erase l).erase k = (V.erase ⟨k.1, hkV⟩).erase ⟨l.1, hlk⟩ :=
      Subtype.ext Finset.erase_right_comm
    have hsign := ExtendedAlternatingCech.cechSign_mul_swap V.1 l.1 k.1 l.2 hkV hkl.symm
    rw [proj_congr F hidx (h := ((V.erase l).erase_subset k).trans (V.erase_subset l))
      (h' := ((V.erase ⟨k.1, hkV⟩).erase_subset ⟨l.1, hlk⟩).trans
        (V.erase_subset ⟨k.1, hkV⟩)), ← add_smul]
    simp only [Idx.val_erase]
    rw [hsign, neg_add_cancel, zero_smul]
  · rintro ⟨l, k⟩ - - hfix
    have hkl : k.1 ≠ l.1 := Finset.ne_of_mem_erase k.2
    simp only [Sigma.mk.injEq] at hfix
    exact hkl (by simpa using Subtype.ext_iff.mp hfix.1)
  · rintro ⟨l, k⟩ -
    exact Finset.mem_sigma.mpr ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩
  · rintro ⟨l, k⟩ -
    rfl

/-- The extended alternating Čech complex of a system of objects indexed by the subsets of
`Fin r`, as a cochain complex indexed by `ℤ`. Outside the degrees `0, …, r` the indexing type
is empty, so the term there is an empty product. -/
def complex (F : Finset (Fin r) ⥤ 𝒜) : CochainComplex 𝒜 ℤ :=
  CochainComplex.of (term F) (d F) (d_comp_d F)

/-- The degree-`p` object of `complex F` is `term F p`. -/
@[simp]
theorem complex_X (F : Finset (Fin r) ⥤ 𝒜) (p : ℤ) : (complex F).X p = term F p := rfl

/-- The differential of `complex F` from degree `p` to degree `p + 1` is `d F p`. -/
@[simp]
theorem complex_d (F : Finset (Fin r) ⥤ 𝒜) (p : ℤ) : (complex F).d p (p + 1) = d F p :=
  CochainComplex.of_d _ _ _

end CategoryTheory.AlternatingCech

namespace AlgebraicGeometry.RingedSite

section Transition

variable {X : RingedSite.{u, v, w}} [HasWeakSheafify X.J CommRingCat.{w}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}))

/-- The transition map `𝒪_{f_S} ⟶ 𝒪_{f_T}` for `S ⊆ T`, the unique map of sheaves of rings
through which `𝒪 ⟶ 𝒪_{f_T}` factors. -/
def awayTransition {S T : Finset (Fin r)} (hST : S ⊆ T) :
    awaySheaf (prodGlobalSection f S) ⟶ awaySheaf (prodGlobalSection f T) :=
  (existsUnique_awayTransition f hST).choose

/-- The transition map `𝒪_{f_S} ⟶ 𝒪_{f_T}` is a map over `𝒪`. -/
theorem toAwaySheaf_comp_awayTransition {S T : Finset (Fin r)} (hST : S ⊆ T) :
    toAwaySheaf (prodGlobalSection f S) ≫ awayTransition f hST =
      toAwaySheaf (prodGlobalSection f T) :=
  (existsUnique_awayTransition f hST).choose_spec.1

/-- **The transition map is pinned by the property that defines it**: *every* map of sheaves of
rings `𝒪_{f_S} ⟶ 𝒪_{f_T}` over `𝒪` equals `awayTransition f hST`.

This is the uniqueness half of `AlgebraicGeometry.RingedSite.existsUnique_awayTransition`, named
rather than reached through `Exists.choose_spec` at each use. It is what makes the choice in
`AlgebraicGeometry.RingedSite.awayTransition` a *name* for a determined map rather than a
selection among several: anything else satisfying
`AlgebraicGeometry.RingedSite.toAwaySheaf_comp_awayTransition` is equal to it. -/
theorem eq_awayTransition {S T : Finset (Fin r)} (hST : S ⊆ T)
    (ψ : awaySheaf (prodGlobalSection f S) ⟶ awaySheaf (prodGlobalSection f T))
    (hψ : toAwaySheaf (prodGlobalSection f S) ≫ ψ = toAwaySheaf (prodGlobalSection f T)) :
    ψ = awayTransition f hST :=
  (existsUnique_awayTransition f hST).choose_spec.2 ψ hψ

/-- The transition map along `S ⊆ S` is the identity, since the identity of `𝒪_{f_S}` is a map
over `𝒪`. -/
theorem awayTransition_refl (S : Finset (Fin r)) :
    awayTransition f (Finset.Subset.refl S) = 𝟙 (awaySheaf (prodGlobalSection f S)) := by
  exact (eq_awayTransition f _ _ (Category.comp_id _)).symm

end Transition

section Unitary

variable {X : RingedSite.{u, v, w}} [HasWeakSheafify X.J CommRingCat.{w}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}))
  (hu : ∀ (U : X.Cᵒᵖ) (n : ℕ), IsUnit (globalSectionVal h U ^ n))

/-- The retraction of `𝒪 ⟶ 𝒪_f` available when every power of `f` is already invertible in `𝒪`:
the unique factorisation of the identity of `𝒪` through `𝒪_f`. -/
def awaySheafSection : awaySheaf h ⟶ X.O :=
  (existsUnique_lift_toAwaySheaf h X.O (𝟙 X.O) (fun U n ↦ by simpa using hu U n)).choose

/-- The retraction splits the canonical map `𝒪 ⟶ 𝒪_f`. -/
theorem toAwaySheaf_comp_awaySheafSection :
    toAwaySheaf h ≫ awaySheafSection h hu = 𝟙 X.O :=
  (existsUnique_lift_toAwaySheaf h X.O (𝟙 X.O)
    (fun U n ↦ by simpa using hu U n)).choose_spec.1

/-- Inverting an already invertible global section changes nothing: `𝒪 ≅ 𝒪_f`. The retraction is
a two-sided inverse because both composites with `𝒪 ⟶ 𝒪_f` lift the same map out of `𝒪`. -/
def awaySheafIsoOfIsUnit : X.O ≅ awaySheaf h where
  hom := toAwaySheaf h
  inv := awaySheafSection h hu
  hom_inv_id := toAwaySheaf_comp_awaySheafSection h hu
  inv_hom_id := by
    obtain ⟨ψ, -, huniq⟩ :=
      existsUnique_lift_toAwaySheaf h (awaySheaf h) (toAwaySheaf h) (isUnit_toAwaySheaf h)
    have h1 : awaySheafSection h hu ≫ toAwaySheaf h = ψ :=
      huniq _ (by
        change toAwaySheaf h ≫ awaySheafSection h hu ≫ toAwaySheaf h = toAwaySheaf h
        rw [← Category.assoc, toAwaySheaf_comp_awaySheafSection, Category.id_comp])
    have h2 : 𝟙 (awaySheaf h) = ψ := huniq _ (by
      change toAwaySheaf h ≫ 𝟙 (awaySheaf h) = toAwaySheaf h
      rw [Category.comp_id])
    rw [h1, h2]

end Unitary

section Empty

variable {X : RingedSite.{u, v, w}} [HasWeakSheafify X.J CommRingCat.{w}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}))

omit [HasWeakSheafify X.J CommRingCat.{w}] in
/-- The empty subproduct `f_∅` is the global section `1`, so all its powers are invertible. -/
theorem isUnit_pow_globalSectionVal_prodGlobalSection_empty (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (globalSectionVal (prodGlobalSection f (∅ : Finset (Fin r))) U ^ n) := by
  simp

/-- `𝒪_{f_∅}` is `𝒪`: the empty subproduct of the `f_i` is `1`. -/
def structureSheafIsoAwayEmpty : X.O ≅ awaySheaf (prodGlobalSection f (∅ : Finset (Fin r))) :=
  awaySheafIsoOfIsUnit _ (isUnit_pow_globalSectionVal_prodGlobalSection_empty f)

end Empty

section Modules

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The canonical map `𝒪 ⟶ 𝒪_f`, as a map of sheaves of `𝒪`-modules. -/
def unitToAwayModule (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶ awayModule X h :=
  SheafOfModules.unitToRestrictScalarsUnit (toAwayRingSheaf X h)

/-- The transition map `𝒪_{f_S} ⟶ 𝒪_{f_T}` for `S ⊆ T`, as a map of sheaves of
`𝒪`-modules. -/
def awayModuleTransition {S T : Finset (Fin r)} (hST : S ⊆ T) :
    awayModule X (prodGlobalSection f S) ⟶ awayModule X (prodGlobalSection f T) :=
  SheafOfModules.unitRestrictScalarsMapOfComp
    ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map (awayTransition f hST))
    (toAwayRingSheaf_comp_awayRingSheafMap X _ (toAwaySheaf_comp_awayTransition f hST))

/-- The transition map along `S ⊆ S` is the identity. -/
theorem awayModuleTransition_refl (S : Finset (Fin r)) :
    awayModuleTransition X f (Finset.Subset.refl S) = 𝟙 (awayModule X (prodGlobalSection f S)) :=
  (SheafOfModules.unitRestrictScalarsMap_congr _ (Category.comp_id _)
      ((congrArg _ (awayTransition_refl f S)).trans (CategoryTheory.Functor.map_id _ _))).trans
    (SheafOfModules.unitRestrictScalarsMap_id _)

/-- The transition maps compose: this is the cocycle identity that makes the alternating
differential of the Čech complex square to zero. -/
theorem awayModuleTransition_comp {S T V : Finset (Fin r)} (hST : S ⊆ T) (hTV : T ⊆ V)
    (hSV : S ⊆ V) :
    awayModuleTransition X f hST ≫ awayModuleTransition X f hTV =
      awayModuleTransition X f hSV := by
  have hcomp :
      (sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map (awayTransition f hST) ≫
          (sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map (awayTransition f hTV) =
        (sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map (awayTransition f hSV) := by
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg _ (awayTransition_comp_eq f hSV (toAwaySheaf_comp_awayTransition f hST)
      (toAwaySheaf_comp_awayTransition f hTV) (toAwaySheaf_comp_awayTransition f hSV))
  exact (SheafOfModules.unitRestrictScalarsMap_comp _ _
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (toAwayRingSheaf_comp_awayRingSheafMap X _
          (toAwaySheaf_comp_awayTransition f hST))).trans
          (toAwayRingSheaf_comp_awayRingSheafMap X _
            (toAwaySheaf_comp_awayTransition f hTV))))).trans
    (SheafOfModules.unitRestrictScalarsMap_congr _ _ hcomp)

/-- The augmentation is compatible with the transition maps, because all of them are maps
over `𝒪`. -/
theorem unitToAwayModule_comp_awayModuleTransition {S T : Finset (Fin r)} (hST : S ⊆ T) :
    unitToAwayModule X (prodGlobalSection f S) ≫ awayModuleTransition X f hST =
      unitToAwayModule X (prodGlobalSection f T) :=
  SheafOfModules.unitToRestrictScalarsUnit_comp _

/-- The system `S ↦ 𝒪_{f_S}` of localizations of the structure sheaf, as a functor on the poset
of subsets of `Fin r` with values in sheaves of `𝒪`-modules. -/
def awayLocalizationFunctor :
    Finset (Fin r) ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) where
  obj S := awayModule X (prodGlobalSection f S)
  map h := awayModuleTransition X f (leOfHom h)
  map_id S := awayModuleTransition_refl X f S
  map_comp h h' := (awayModuleTransition_comp X f (leOfHom h) (leOfHom h') _).symm

/-- **The extended alternating Čech complex of sheaves of `𝒪`-modules** on a finite family of
global sections `f_1, …, f_r` of `𝒪`: the complex
`𝒪_{f_∅} → ∏_{i₀} 𝒪_{f_{i₀}} → ∏_{i₀ < i₁} 𝒪_{f_{i₀} f_{i₁}} → ⋯ → 𝒪_{f_1 ⋯ f_r}`
with `∏_{|S| = p} 𝒪_{f_S}` in degree `p`, and zero outside degrees `0, …, r`. -/
def extendedAlternatingCech :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  AlternatingCech.complex (awayLocalizationFunctor X f)

/-- The augmentation of the extended alternating Čech complex: the canonical map from `𝒪` into
its degree-zero term `𝒪_{f_∅}`. -/
def extendedAlternatingCechAugmentation :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (extendedAlternatingCech X f).X 0 :=
  Pi.lift fun S : AlternatingCech.Idx r 0 => unitToAwayModule X (prodGlobalSection f S.1)

/-- The augmentation is the canonical map `𝒪 ⟶ 𝒪_{f_S}` in each factor of the degree-zero
term. -/
@[simp]
theorem extendedAlternatingCechAugmentation_comp_pi (S : AlternatingCech.Idx r 0) :
    extendedAlternatingCechAugmentation X f ≫
        Pi.π (fun S : AlternatingCech.Idx r 0 => awayModule X (prodGlobalSection f S.1)) S =
      unitToAwayModule X (prodGlobalSection f S.1) :=
  Pi.lift_π _ _

/-- The degree-zero term of the extended alternating Čech complex is `𝒪`: it is the single
factor `𝒪_{f_∅}`, and inverting the empty subproduct `f_∅ = 1` changes nothing. -/
def unitIsoAwayModuleEmpty :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      awayModule X (prodGlobalSection f (∅ : Finset (Fin r))) :=
  SheafOfModules.unitIsoRestrictScalarsUnit
    ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
      (structureSheafIsoAwayEmpty f))

/-- That isomorphism is the canonical map `𝒪 ⟶ 𝒪_{f_∅}`, which is the augmentation read in the
unique factor of the degree-zero term. -/
theorem unitIsoAwayModuleEmpty_hom :
    (unitIsoAwayModuleEmpty X f).hom =
      unitToAwayModule X (prodGlobalSection f (∅ : Finset (Fin r))) :=
  rfl

end Modules

end AlgebraicGeometry.RingedSite

end
