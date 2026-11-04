module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDegreeZero.Augmentation

/-!
# Sections of a sheaf of modules as alternating Čech `0`-cocycles

Let `f : X ⟶ Spec A` and let `U : I → X.Opens` be a family of opens. Restricting a section of an
`𝒪_X`-module `F` over an open `W` containing every `U i` to the members of the family is an
`A`-linear map `Γ(F, W) → Č⁰_alt(U, F)`. When the family covers `W` it is injective and its image
is the kernel of the alternating Čech differential, by the sheaf property; and it is compatible
with the base change of Čech cochains of
`StacksFrontier/AlgebraicGeometry/Modules/AlternatingCechModuleBaseChange.lean`, through the canonical
pullback of sections.

## Main definitions

* `Stacks.Cech.sectionsToAlternatingₗ`: the restriction map `Γ(F, W) → Č⁰_alt(U, F)`.

## Main results

* `Stacks.Cech.sectionsToAlternatingₗ_injective` and `Stacks.Cech.range_sectionsToAlternatingₗ`:
  for a family covering `W`, the restriction map identifies `Γ(F, W)` with the kernel of the
  alternating Čech differential out of degree `0`.
* `Stacks.Cech.alternatingCochainBaseChangeₗ_sectionsToAlternatingₗ`: the base change of the
  restriction of a section is the restriction of its pullback.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Cech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (F : X.Modules) {W : X.Opens} (hUW : ∀ i, U i ≤ W)

/-- Every member of the family lies in `W`, hence so does every finite intersection of members
indexed by a nonempty tuple. -/
theorem inter_le_of_le (hUW : ∀ i, U i ≤ W) (i : Fin 1 → I) : CechCochains.inter U i ≤ W :=
  (iInf_le _ 0).trans (hUW (i 0))

/-- The restriction of a section over `W` to the members of the family, as a `0`-cochain. -/
def toCochainZero (s : Γ(F, W)) : CechCochains.Cochain U F.presheaf 0 :=
  fun i => CechCochains.restr F.presheaf (inter_le_of_le U hUW i) s

/-- A `0`-cochain is always alternating. -/
theorem toCochainZero_isAlternating (s : Γ(F, W)) :
    CechCochains.IsAlternating U F.presheaf (toCochainZero U F hUW s) :=
  ⟨fun i hi => absurd (fun a b _ => Fin.ext (by have := a.2; have := b.2; omega)) hi,
    fun _ a b hab => absurd (Fin.ext (by have := a.2; have := b.2; omega)) hab⟩

/-- **The restriction map `Γ(F, W) → Č⁰_alt(U, F)`**, linear over the base ring. -/
def sectionsToAlternatingₗ :
    letI := sectionsModule f F W
    letI := cochainModule f U F 0
    Γ(F, W) →ₗ[A] alternatingSubmodule f U F 0 :=
  letI := sectionsModule f F W
  letI := cochainModule f U F 0
  { toFun := fun s => ⟨toCochainZero U F hUW s, by exact toCochainZero_isAlternating U F hUW s⟩
    map_add' := fun s t => Subtype.ext (funext fun i => map_add _ s t)
    map_smul' := fun a s => Subtype.ext (funext fun i => by
      rw [RingHom.id_apply, Submodule.coe_smul, cochain_smul_apply]
      change (F.presheaf.map (homOfLE (inter_le_of_le U hUW i)).op).hom
          ((baseRingHom f W).hom a • s) =
        (baseRingHom f (CechCochains.inter U i)).hom a •
          (F.presheaf.map (homOfLE (inter_le_of_le U hUW i)).op).hom s
      rw [Scheme.Modules.map_smul, map_baseRingHom_apply]) }

/-- The component of `sectionsToAlternatingₗ` at a `1`-tuple `i` is the restriction of the section
to `U (i 0)`. -/
@[simp]
theorem sectionsToAlternatingₗ_apply_coe (s : Γ(F, W)) (i : Fin 1 → I) :
    (sectionsToAlternatingₗ f U F hUW s : CechCochains.Cochain U F.presheaf 0) i =
      CechCochains.restr F.presheaf (inter_le_of_le U hUW i) s :=
  rfl

/-- A family covering `W` also covers it through the intersections over `1`-tuples. -/
private theorem le_iSup_inter_of_le_iSup (hcov : W ≤ ⨆ i, U i) :
    W ≤ ⨆ i : Fin 1 → I, CechCochains.inter U i := by
  intro x hx
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hcov hx)
  refine Opens.mem_iSup.2 ⟨fun _ => j, ?_⟩
  simpa [CechCochains.inter] using hj

variable (hcov : W ≤ ⨆ i, U i)

include hcov in
/-- For a family covering `W`, a section over `W` is determined by its restrictions. -/
theorem sectionsToAlternatingₗ_injective :
    Function.Injective (sectionsToAlternatingₗ f U F hUW) := by
  intro s s' h
  refine Stacks.Cohomology.CechZero.eq_of_res_eq F.presheaf F.isSheaf
    (fun i : Fin 1 → I => CechCochains.inter U i) W (inter_le_of_le U hUW)
    (le_iSup_inter_of_le_iSup U hcov) s s' fun i => congrFun (congrArg Subtype.val h) i

/-- Sections of a presheaf at propositionally equal tuples have equal restrictions. -/
theorem restr_cochain_congr {p : ℕ} (t : CechCochains.Cochain U F.presheaf p)
    {i i' : Fin (p + 1) → I} (h : i = i') {O : X.Opens} (h₁ : O ≤ CechCochains.inter U i)
    (h₂ : O ≤ CechCochains.inter U i') :
    CechCochains.restr F.presheaf h₁ (t i) = CechCochains.restr F.presheaf h₂ (t i') := by
  subst h
  rfl

include hcov in
/-- The members of the family cover `W`, read as intersections over `1`-tuples. -/
theorem le_iSup_inter : W ≤ ⨆ i : Fin 1 → I, CechCochains.inter U i :=
  le_iSup_inter_of_le_iSup U hcov

/-- A `0`-cochain killed by the Čech differential is a compatible family: its members agree on
every open contained in two of the intersections. -/
private theorem restr_eq_restr_of_cechD_eq_zero (t : CechCochains.Cochain U F.presheaf 0)
    (hd : ∀ j : Fin 2 → I, CechCochains.cechD U F.presheaf 0 t j = 0)
    (O : X.Opens) (i i' : Fin 1 → I) (h₁ : O ≤ CechCochains.inter U i)
    (h₂ : O ≤ CechCochains.inter U i') :
    CechCochains.restr F.presheaf h₁ (t i) = CechCochains.restr F.presheaf h₂ (t i') := by
  let j : Fin 2 → I := ![i 0, i' 0]
  have hO : O ≤ CechCochains.inter U j := by
    refine le_iInf fun k => ?_
    refine Fin.cases ?_ (fun k => ?_) k
    · exact h₁.trans (iInf_le _ 0)
    · rw [Fin.fin_one_eq_zero k]
      exact h₂.trans (iInf_le _ 0)
  have h0 : j ∘ (0 : Fin 2).succAbove = i' := funext fun k => by
    rw [Fin.fin_one_eq_zero k]
    rfl
  have h1 : j ∘ (1 : Fin 2).succAbove = i := funext fun k => by
    rw [Fin.fin_one_eq_zero k]
    rfl
  have e := congrArg (CechCochains.restr F.presheaf hO) (hd j)
  change CechCochains.restr F.presheaf hO (∑ k : Fin 2, ((-1 : ℤ) ^ (k : ℕ)) •
    CechCochains.restr F.presheaf (CechCochains.inter_le_omit U j k)
      (t (j ∘ k.succAbove))) = CechCochains.restr F.presheaf hO 0 at e
  rw [Fin.sum_univ_two, map_add, map_zsmul, map_zsmul, CechCochains.restr_restr,
    CechCochains.restr_restr, map_zero, restr_cochain_congr U F t h0 _ h₂,
    restr_cochain_congr U F t h1 _ h₁] at e
  symm
  simpa [sub_eq_zero, neg_one_zsmul, ← sub_eq_add_neg] using e

include hcov in
/-- **For a family covering `W`, the sections over `W` are the alternating `0`-cocycles.** The
restriction map `Γ(F, W) → Č⁰_alt(U, F)` has image the kernel of the alternating Čech
differential: a cocycle is a compatible family of sections, which glues by the sheaf property. -/
theorem range_sectionsToAlternatingₗ :
    letI := sectionsModule f F W
    letI := cochainModule f U F 0
    letI := cochainModule f U F 1
    LinearMap.range (sectionsToAlternatingₗ f U F hUW) =
      LinearMap.ker (alternatingCechModuleD f U F 0) := by
  let := sectionsModule f F W
  let := cochainModule f U F 0
  let := cochainModule f U F 1
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    rw [LinearMap.mem_ker]
    refine Subtype.ext (funext fun i => ?_)
    show ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • CechCochains.restr F.presheaf
      (CechCochains.inter_le_omit U i j)
        (CechCochains.restr F.presheaf (inter_le_of_le U hUW (i ∘ j.succAbove)) s) = 0
    rw [Fin.sum_univ_two, CechCochains.restr_restr, CechCochains.restr_restr]
    simp
  · intro ht
    rw [LinearMap.mem_ker] at ht
    obtain ⟨s, hs, -⟩ := Stacks.Cohomology.CechZero.existsUnique_glue F.presheaf F.isSheaf
      (fun i : Fin 1 → I => CechCochains.inter U i) W (inter_le_of_le U hUW)
      (le_iSup_inter U hcov) t.1
      (restr_eq_restr_of_cechD_eq_zero U F t.1 fun j => congrFun (congrArg Subtype.val ht) j)
    exact ⟨s, Subtype.ext (funext hs)⟩

section BaseChange

variable {X' : Scheme.{u}} (g : X' ⟶ X) {I' : Type u} (U' : I' → X'.Opens) (e : I' ≃ I)
  (hU' : ∀ i, U' i = g ⁻¹ᵁ U (e i)) {A' : Type u} [CommRing A'] (φ : A →+* A')
  (f' : X' ⟶ Spec (.of A'))
  (hbase : ∀ W : X.Opens,
    baseRingHom f W ≫ g.app W = CommRingCat.ofHom φ ≫ baseRingHom f' (g ⁻¹ᵁ W))

include hUW hU' in
/-- Every member of the inverse-image family lies in the preimage of `W`. -/
theorem preimage_le_of_le (i : I') : U' i ≤ g ⁻¹ᵁ W :=
  (hU' i).le.trans (Scheme.Hom.preimage_mono g (hUW (e i)))

/-- **Base change of Čech cochains commutes with restricting sections.** The comparison of
alternating `0`-cochains carries the restriction of a section `s` over `W` to the restriction of
its pullback over `g⁻¹ W`. -/
theorem alternatingCochainBaseChangeₗ_sectionsToAlternatingₗ (s : Γ(F, W)) :
    alternatingCochainBaseChangeₗ g U U' e F hU' φ f f' hbase 0
        (sectionsToAlternatingₗ f U F hUW s) =
      sectionsToAlternatingₗ f' U' ((Scheme.Modules.pullback g).obj F)
        (preimage_le_of_le U hUW g U' e hU') (pullbackSections g F W s) :=
  Subtype.ext <| funext fun i => pullbackSections_restr g F (inter_le_of_le U hUW (e ∘ i))
    (inter_le_of_le U' (preimage_le_of_le U hUW g U' e hU') i)
    (inter_eq_preimage g U U' e hU' i).le s

end BaseChange

end Stacks.Cech

end
