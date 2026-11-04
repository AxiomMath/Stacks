module

public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwise
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The parity Euler class of a complex with locally bounded coherent cohomology

Let `X` be a locally Noetherian scheme and `K` an object of `D(𝒪_X)` whose cohomology sheaves
`H^n(K)` are coherent and form a locally finite family: every point has a neighbourhood meeting
the supports of only finitely many of them. The two sums

  `⨁_{i ∈ ℤ} H^{2i}(K)`   and   `⨁_{i ∈ ℤ} H^{2i+1}(K)`

are then coherent, and the *parity Euler class*

  `χ(K) = [⨁_i H^{2i}(K)] − [⨁_i H^{2i+1}(K)] ∈ K'₀(X)`

is additive along distinguished triangles. When `X` is quasi-compact the sums are finite and
`χ(K) = ∑ (−1)ⁿ [H^n(K)]`; the even and odd sums are the form of this alternating sum that
makes sense on a locally Noetherian scheme, exactly as in [Stacks, Tag 0FDL].

## Main definitions

* `AlgebraicGeometry.ParityEulerClass.IsLocallyBoundedCoherent`: coherent cohomology sheaves
  with a locally finite family of supports.
* `AlgebraicGeometry.ParityEulerClass.paritySum`: the sum `⨁_i H^{2i+r}(K)`.
* `AlgebraicGeometry.ParityEulerClass.parityEulerClass`: the class `χ(K)`.

## Main results

* `AlgebraicGeometry.ParityEulerClass.nonempty_exactHexagon_of_longExact_int`: a long exact
  sequence indexed by `ℤ`, summed by the parity of the degree, is an exact hexagon.
* `AlgebraicGeometry.ParityEulerClass.isCoherent_sigma_of_locallyFinite`: a direct sum of
  coherent modules with locally finite supports is coherent.
* `AlgebraicGeometry.ParityEulerClass.parityEulerClass_obj₂`: additivity of `χ` along a
  distinguished triangle.

## References

* [Stacks Project, Tag 0FDL](https://stacks.math.columbia.edu/tag/0FDL)
* [Stacks Project, Tag 0FCR](https://stacks.math.columbia.edu/tag/0FCR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Topology

universe u

namespace AlgebraicGeometry.ParityEulerClass

open ProperPushforwardKZero (ExactHexagon)

/-! ### Exact hexagons from long exact sequences indexed by `ℤ` -/

section Hexagon

variable {C : Type*} [Category C] [Abelian C] [HasCoproductsOfShape ℤ C]
  [HasExactColimitsOfShape (Discrete ℤ) C]

/-- The coproduct of a family indexed by `ℤ`, reindexed along `i ↦ i + 1`. -/
def sigmaSuccIso (E : ℤ → C) : (∐ fun i : ℤ => E (i + 1)) ≅ ∐ E :=
  Limits.Sigma.reindex (Equiv.addRight (1 : ℤ)) E

omit [Abelian C] [HasExactColimitsOfShape (Discrete ℤ) C] in
/-- `sigmaSuccIso E` sends the `i`-th summand of `∐ i, E (i + 1)` to the `(i + 1)`-th summand of
`∐ E`. -/
theorem ι_sigmaSuccIso_hom (E : ℤ → C) (i : ℤ) :
    Limits.Sigma.ι (fun i : ℤ => E (i + 1)) i ≫ (sigmaSuccIso E).hom =
      Limits.Sigma.ι E (i + 1) :=
  Limits.Sigma.ι_reindex_hom (Equiv.addRight (1 : ℤ)) E i

omit [Abelian C] [HasExactColimitsOfShape (Discrete ℤ) C] in
/-- `sigmaSuccIso` is natural in the family: it commutes with the maps induced by a family of
morphisms `u i : E i ⟶ F i`. -/
theorem sigmaSuccIso_hom_naturality {E F : ℤ → C} (u : ∀ i, E i ⟶ F i) :
    (sigmaSuccIso E).hom ≫ Limits.Sigma.map u =
      Limits.Sigma.map (fun i => u (i + 1)) ≫ (sigmaSuccIso F).hom := by
  refine Limits.Sigma.hom_ext _ _ fun i => ?_
  rw [← Category.assoc, ι_sigmaSuccIso_hom, Limits.Sigma.ι_map, Limits.Sigma.ι_map_assoc,
    ι_sigmaSuccIso_hom]

/-- **A long exact sequence indexed by `ℤ`, collected by parity, is an exact hexagon.** The
even terms `E₀ i ⟶ E₁ i ⟶ E₂ i` and the odd terms `O₀ i ⟶ O₁ i ⟶ O₂ i`, with connecting maps
`E₂ i ⟶ O₀ i` and `O₂ i ⟶ E₀ (i + 1)`, form one exact sequence; summing over `i` gives the six
sums and an exact cycle between them. -/
theorem nonempty_exactHexagon_of_longExact_int (E₀ E₁ E₂ O₀ O₁ O₂ : ℤ → C)
    (ue : ∀ i, E₀ i ⟶ E₁ i) (ve : ∀ i, E₁ i ⟶ E₂ i) (we : ∀ i, E₂ i ⟶ O₀ i)
    (uo : ∀ i, O₀ i ⟶ O₁ i) (vo : ∀ i, O₁ i ⟶ O₂ i) (wo : ∀ i, O₂ i ⟶ E₀ (i + 1))
    (h₀ : ∀ i, ue i ≫ ve i = 0) (h₁ : ∀ i, ve i ≫ we i = 0) (h₂ : ∀ i, we i ≫ uo i = 0)
    (h₃ : ∀ i, uo i ≫ vo i = 0) (h₄ : ∀ i, vo i ≫ wo i = 0) (h₅ : ∀ i, wo i ≫ ue (i + 1) = 0)
    (e₀ : ∀ i, (ShortComplex.mk _ _ (h₀ i)).Exact) (e₁ : ∀ i, (ShortComplex.mk _ _ (h₁ i)).Exact)
    (e₂ : ∀ i, (ShortComplex.mk _ _ (h₂ i)).Exact) (e₃ : ∀ i, (ShortComplex.mk _ _ (h₃ i)).Exact)
    (e₄ : ∀ i, (ShortComplex.mk _ _ (h₄ i)).Exact)
    (e₅ : ∀ i, (ShortComplex.mk _ _ (h₅ i)).Exact) :
    Nonempty (ExactHexagon (∐ E₀) (∐ E₁) (∐ E₂) (∐ O₀) (∐ O₁) (∐ O₂)) := by
  have hz : ∀ {A B D : ℤ → C} (a : ∀ i, A i ⟶ B i) (b : ∀ i, B i ⟶ D i),
      (∀ i, a i ≫ b i = 0) → Limits.Sigma.map a ≫ Limits.Sigma.map b = 0 := by
    intro A B D a b h
    rw [Limits.Sigma.map_comp_map]
    exact Limits.Sigma.hom_ext _ _ fun i => by simp [h i]
  let R := sigmaSuccIso E₀
  let R' := sigmaSuccIso E₁
  let d₅ : (∐ O₂) ⟶ ∐ E₀ := Limits.Sigma.map wo ≫ R.hom
  have w₄ : Limits.Sigma.map vo ≫ d₅ = 0 := by
    rw [← Category.assoc, hz _ _ h₄, zero_comp]
  have hnat : R.hom ≫ Limits.Sigma.map ue = Limits.Sigma.map (fun i => ue (i + 1)) ≫ R'.hom :=
    sigmaSuccIso_hom_naturality ue
  have w₅ : d₅ ≫ Limits.Sigma.map ue = 0 := by
    show (Limits.Sigma.map wo ≫ R.hom) ≫ Limits.Sigma.map ue = 0
    rw [Category.assoc, hnat, ← Category.assoc, hz _ _ h₅, zero_comp]
  have ex₄ : (ShortComplex.mk (Limits.Sigma.map vo) d₅ w₄).Exact :=
    ShortComplex.exact_of_iso
      (ShortComplex.isoMk (S₁ := .mk (Limits.Sigma.map vo) (Limits.Sigma.map wo) (hz _ _ h₄))
        (Iso.refl _) (Iso.refl _) R (by simp) (by simp [d₅]))
      (Stacks.SigmaExactness.exact_sigmaMap _ _ _ vo wo h₄ e₄)
  have ex₅ : (ShortComplex.mk d₅ (Limits.Sigma.map ue) w₅).Exact :=
    ShortComplex.exact_of_iso
      (ShortComplex.isoMk (S₁ := .mk (Limits.Sigma.map wo) (Limits.Sigma.map fun i => ue (i + 1))
        (hz _ _ h₅)) (Iso.refl _) R R' (by simp [d₅]) hnat)
      (Stacks.SigmaExactness.exact_sigmaMap _ _ _ wo (fun i => ue (i + 1)) h₅ e₅)
  exact ⟨{ d₀ := Limits.Sigma.map ue, d₁ := Limits.Sigma.map ve, d₂ := Limits.Sigma.map we
           d₃ := Limits.Sigma.map uo, d₄ := Limits.Sigma.map vo, d₅ := d₅
           w₀ := hz _ _ h₀, w₁ := hz _ _ h₁, w₂ := hz _ _ h₂, w₃ := hz _ _ h₃
           w₄ := w₄, w₅ := w₅
           exact₀ := Stacks.SigmaExactness.exact_sigmaMap _ _ _ ue ve h₀ e₀
           exact₁ := Stacks.SigmaExactness.exact_sigmaMap _ _ _ ve we h₁ e₁
           exact₂ := Stacks.SigmaExactness.exact_sigmaMap _ _ _ we uo h₂ e₂
           exact₃ := Stacks.SigmaExactness.exact_sigmaMap _ _ _ uo vo h₃ e₃
           exact₄ := ex₄, exact₅ := ex₅ }⟩

end Hexagon

/-! ### Coproducts with finitely many nonzero summands -/

section FiniteSupport

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- A coproduct all of whose summands outside a set `S` vanish is the coproduct of the summands
indexed by `S`. -/
def sigmaSubtypeIsoOfIsZero {ι : Type*} (F : ι → C) [HasCoproduct F] (S : Set ι)
    [HasCoproduct fun i : S => F i] (hz : ∀ i, i ∉ S → IsZero (F i)) :
    (∐ fun i : S => F i) ≅ ∐ F := by
  classical
  let c : Cofan F := Cofan.mk _ fun i =>
    if hi : i ∈ S then Limits.Sigma.ι (fun j : S => F j) ⟨i, hi⟩ else 0
  have hc : IsColimit c := by
    refine Cofan.IsColimit.mk c (fun t => Limits.Sigma.desc fun j : S => t.inj j) ?_ ?_
    · intro t i
      by_cases hi : i ∈ S
      · simp [c, hi]
      · exact (hz i hi).eq_of_src _ _
    · intro t m hm
      refine Limits.Sigma.hom_ext (f := fun j : S => F j) _ _ fun j => ?_
      simpa [c, j.2] using hm j
  exact hc.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor F))

end FiniteSupport

/-! ### Supports and restriction to an open -/

section Support

variable {X : Scheme.{u}}

/-- A point outside the support of a module has zero stalk. -/
theorem isZero_stalk_of_notMem_supp (M : X.Modules) (x : X) (hx : x ∉ SheafOfModules.supp M) :
    IsZero (M.presheaf.stalk x) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  have key : ∀ c : M.presheaf.stalk x, c = 0 := fun c => by
    by_contra hc
    exact hx ⟨c, hc⟩
  rw [key a, key b]

/-- A point with zero stalk is outside the support. -/
theorem notMem_supp_of_isZero_stalk (M : X.Modules) (x : X)
    (hx : IsZero (M.presheaf.stalk x)) : x ∉ SheafOfModules.supp M := by
  rintro ⟨a, ha⟩
  exact ha ((AddCommGrpCat.isZero_iff_subsingleton.1 hx).elim a 0)

/-- **A module vanishes on an open disjoint from its support.** -/
theorem isZero_restrict_of_disjoint (M : X.Modules) (V : X.Opens)
    (h : Disjoint (SheafOfModules.supp M) (V : Set X)) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj M) := by
  refine isZero_of_forall_isZero_stalk _ fun y => ?_
  refine IsZero.of_iso ?_ ((Scheme.Modules.restrictStalkNatIso V.ι y).app M)
  exact isZero_stalk_of_notMem_supp M _ fun hm => Set.disjoint_left.1 h hm y.2

/-- **The support of a module vanishing on an open is disjoint from it.** -/
theorem disjoint_of_isZero_restrict (M : X.Modules) (V : X.Opens)
    (h : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj M)) :
    Disjoint (SheafOfModules.supp M) (V : Set X) := by
  refine Set.disjoint_left.2 fun x hx hxV => ?_
  have hz : IsZero (((Scheme.Modules.restrictFunctor V.ι).obj M).presheaf.stalk ⟨x, hxV⟩) :=
    (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff _ _ _).1
      ((AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj _ _).1 h _)
  exact notMem_supp_of_isZero_stalk M x
    (IsZero.of_iso hz ((Scheme.Modules.restrictStalkNatIso V.ι ⟨x, hxV⟩).app M).symm) hx

/-- **A direct sum of coherent modules with locally finite supports is coherent.** -/
theorem isCoherent_sigma_of_locallyFinite {ι : Type*} (A : ι → X.Modules) [HasCoproduct A]
    [∀ V : X.Opens, HasCoproduct fun i => (Scheme.Modules.restrictFunctor V.ι).obj (A i)]
    (hA : ∀ i, (A i).IsCoherent) (hlf : LocallyFinite fun i => SheafOfModules.supp (A i)) :
    (∐ A).IsCoherent := by
  classical
  have hloc : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      {i | (SheafOfModules.supp (A i) ∩ (V : Set X)).Nonempty}.Finite := by
    intro x
    obtain ⟨t, ht, hfin⟩ := hlf x
    obtain ⟨W, hWt, hW, hxW⟩ := mem_nhds_iff.1 ht
    exact ⟨⟨W, hW⟩, hxW, hfin.subset fun i hi => hi.mono (Set.inter_subset_inter_right _ hWt)⟩
  choose V hxV hfin using hloc
  refine Modules.isCoherent_of_restrict (∐ A) V
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩) fun x => ?_
  let R := Scheme.Modules.restrictFunctor (V x).ι
  let S : Set ι := {i | (SheafOfModules.supp (A i) ∩ (V x : Set X)).Nonempty}
  have : Finite S := (hfin x).to_subtype
  have hiso : R.obj (∐ A) ≅ ∐ fun i => R.obj (A i) :=
    preservesColimitIso R (Discrete.functor A) ≪≫
      HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)
  have hz : ∀ i, i ∉ S → IsZero (R.obj (A i)) := fun i hi =>
    isZero_restrict_of_disjoint (A i) (V x)
      (Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hi))
  have hfinCoh : (∐ fun i : S => R.obj (A i)).IsCoherent :=
    CoherentAbelian.isCoherent_of_stacksIsCoherent
      (Stacks.SheafOfModules.isCoherent_sigma _ fun j =>
        CoherentAbelian.stacksIsCoherent_of_isCoherent
          (Modules.isCoherent_restrict (hM := hA j.val) (A j.val) _))
  exact ObjectProperty.prop_of_iso (P := fun M => SheafOfModules.IsCoherent M)
    ((sigmaSubtypeIsoOfIsZero (fun i => R.obj (A i)) S hz).trans hiso.symm) hfinCoh

end Support

/-! ### The parity Euler class -/

section Euler

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- An object of `D(𝒪_X)` has *locally bounded coherent cohomology* when every cohomology sheaf
is coherent and the supports of the cohomology sheaves form a locally finite family. On a
quasi-compact scheme this says that the object lies in `D^b_Coh(𝒪_X)`. -/
def IsLocallyBoundedCoherent (K : DerivedCategory X.Modules) : Prop :=
  (∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsCoherent) ∧
    LocallyFinite fun n : ℤ =>
      SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules n).obj K)

/-- The direct sum `⨁_{i ∈ ℤ} H^{2i+r}(K)` of the cohomology sheaves of `K` in the degrees
congruent to `r` modulo `2`. -/
def paritySum (K : DerivedCategory X.Modules) (r : ℤ) : X.Modules :=
  ∐ fun i : ℤ => (DerivedCategory.homologyFunctor X.Modules (2 * i + r)).obj K

/-- The parity sums of an object with locally bounded coherent cohomology are coherent. -/
theorem isCoherent_paritySum {K : DerivedCategory X.Modules} (hK : IsLocallyBoundedCoherent K)
    (r : ℤ) : (paritySum K r).IsCoherent :=
  isCoherent_sigma_of_locallyFinite _ (fun _ => hK.1 _)
    (hK.2.comp_injective fun a b h => by simpa using h)

/-- A parity sum of an object with locally bounded coherent cohomology, as a coherent module. -/
def parityObject (K : DerivedCategory X.Modules) (hK : IsLocallyBoundedCoherent K) (r : ℤ) :
    Stacks.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ⟨paritySum K r, CoherentAbelian.stacksIsCoherent_of_isCoherent (isCoherent_paritySum hK r)⟩

open Classical in
/-- **The parity Euler class** `χ(K) = [⨁_i H^{2i}(K)] − [⨁_i H^{2i+1}(K)]` in `K'₀(X)` of an
object with locally bounded coherent cohomology, and `0` for any other object. -/
def parityEulerClass (K : DerivedCategory X.Modules) : CoherentKZero X :=
  if hK : IsLocallyBoundedCoherent K then
    KZero.mk _ (parityObject K hK 0) - KZero.mk _ (parityObject K hK 1)
  else 0

/-- For an object with locally bounded coherent cohomology, `χ(K)` is the difference of the
classes of its even and odd parity sums. -/
theorem parityEulerClass_eq {K : DerivedCategory X.Modules} (hK : IsLocallyBoundedCoherent K) :
    parityEulerClass K = KZero.mk _ (parityObject K hK 0) - KZero.mk _ (parityObject K hK 1) :=
  dif_pos hK

/-- Locally bounded coherent cohomology is invariant under isomorphism. -/
theorem IsLocallyBoundedCoherent.of_iso {K L : DerivedCategory X.Modules} (e : K ≅ L)
    (hK : IsLocallyBoundedCoherent K) : IsLocallyBoundedCoherent L := by
  refine ⟨fun n => ?_, ?_⟩
  · exact ObjectProperty.prop_of_iso (P := fun M => SheafOfModules.IsCoherent M)
      ((DerivedCategory.homologyFunctor X.Modules n).mapIso e) (hK.1 n)
  · convert hK.2 using 2 with n
    exact (SheafOfModules.supp_eq_of_iso
      ((DerivedCategory.homologyFunctor X.Modules n).mapIso e)).symm

/-- The parity Euler class is invariant under isomorphism. -/
theorem parityEulerClass_congr {K L : DerivedCategory X.Modules} (e : K ≅ L) :
    parityEulerClass K = parityEulerClass L := by
  by_cases hK : IsLocallyBoundedCoherent K
  · have hL := hK.of_iso e
    rw [parityEulerClass_eq hK, parityEulerClass_eq hL]
    have hr : ∀ r, KZero.mk _ (parityObject K hK r) = KZero.mk _ (parityObject L hL r) := fun r =>
      KZero.mk_eq_of_iso (ObjectProperty.isoMk _
        (Limits.Sigma.mapIso fun i => (DerivedCategory.homologyFunctor X.Modules _).mapIso e))
    rw [hr 0, hr 1]
  · have hL : ¬ IsLocallyBoundedCoherent L := fun hL => hK (hL.of_iso e.symm)
    rw [parityEulerClass, dif_neg hK, parityEulerClass, dif_neg hL]

/-- **The parity Euler class is additive along distinguished triangles** of objects with locally
bounded coherent cohomology: `χ(K₂) = χ(K₁) + χ(K₃)` for a distinguished triangle
`K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]`. -/
theorem parityEulerClass_obj₂ [IsLocallyNoetherian X] (T : Triangle (DerivedCategory X.Modules))
    (hT : T ∈ distTriang _) (h₁ : IsLocallyBoundedCoherent T.obj₁)
    (h₂ : IsLocallyBoundedCoherent T.obj₂) (h₃ : IsLocallyBoundedCoherent T.obj₃) :
    parityEulerClass T.obj₂ = parityEulerClass T.obj₁ + parityEulerClass T.obj₃ := by
  let H := fun n : ℤ => DerivedCategory.homologyFunctor X.Modules n
  have hc : ∀ n, (H n).map T.mor₁ ≫ (H n).map T.mor₂ = 0 := fun n => by
    simp only [H, ← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero]
  obtain ⟨Hx⟩ := nonempty_exactHexagon_of_longExact_int
    (fun i => (H (2 * i + 0)).obj T.obj₁) (fun i => (H (2 * i + 0)).obj T.obj₂)
    (fun i => (H (2 * i + 0)).obj T.obj₃) (fun i => (H (2 * i + 1)).obj T.obj₁)
    (fun i => (H (2 * i + 1)).obj T.obj₂) (fun i => (H (2 * i + 1)).obj T.obj₃)
    (fun i => (H (2 * i + 0)).map T.mor₁) (fun i => (H (2 * i + 0)).map T.mor₂)
    (fun i => DerivedCategory.HomologySequence.δ T (2 * i + 0) (2 * i + 1) (by ring))
    (fun i => (H (2 * i + 1)).map T.mor₁) (fun i => (H (2 * i + 1)).map T.mor₂)
    (fun i => DerivedCategory.HomologySequence.δ T (2 * i + 1) (2 * (i + 1) + 0) (by ring))
    (fun i => hc _)
    (fun i => DerivedCategory.HomologySequence.comp_δ T hT _ _ _)
    (fun i => DerivedCategory.HomologySequence.δ_comp T hT _ _ _)
    (fun i => hc _)
    (fun i => DerivedCategory.HomologySequence.comp_δ T hT _ _ _)
    (fun i => DerivedCategory.HomologySequence.δ_comp T hT _ _ _)
    (fun i => DerivedCategory.HomologySequence.exact₂ T hT _)
    (fun i => DerivedCategory.HomologySequence.exact₃ T hT _ _ _)
    (fun i => DerivedCategory.HomologySequence.exact₁ T hT _ _ _)
    (fun i => DerivedCategory.HomologySequence.exact₂ T hT _)
    (fun i => DerivedCategory.HomologySequence.exact₃ T hT _ _ _)
    (fun i => DerivedCategory.HomologySequence.exact₁ T hT _ _ _)
  obtain ⟨Hc⟩ := ProperPushforwardKZero.nonempty_exactHexagon_of_obj
    (parityObject T.obj₁ h₁ 0) (parityObject T.obj₂ h₂ 0) (parityObject T.obj₃ h₃ 0)
    (parityObject T.obj₁ h₁ 1) (parityObject T.obj₂ h₂ 1) (parityObject T.obj₃ h₃ 1) Hx
  have h := ExactHexagon.mk_add_eq _ Hc
  rw [parityEulerClass_eq h₁, parityEulerClass_eq h₂, parityEulerClass_eq h₃,
    sub_add_sub_comm, sub_eq_sub_iff_add_eq_add, h]
  abel

end Euler

end AlgebraicGeometry.ParityEulerClass
