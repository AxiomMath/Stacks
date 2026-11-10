module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.CoherentDecomposition
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerObject
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.UnitHom

/-!
# Siblings out of `D^b(Coh(𝒪_X))` for `X` reduced and projective over a field

Let `k` be a field and `X` a reduced scheme, proper over `k`, with an ample invertible module
`ℒ`. Sibling exact functors `F, F' : D^b(Coh(𝒪_X)) ⥤ 𝒟`, with `F` fully faithful, are
isomorphic. This is the first sentence of [Stacks, Tag 0G01].

Write `X₁` for the complement of the isolated points of `X`.

## Main results

* `AlgebraicGeometry.exists_epi_subsingleton_hom_of_cohPiece_none`: every coherent module `𝓕`
  supported on `X₁` is a quotient of a coherent module `N` with `Hom(𝓕, N) = 0`.
* `AlgebraicGeometry.nonempty_iso_of_areSiblings_of_isReduced_of_isAmple`: sibling exact functors
  out of `D^b(Coh(𝒪_X))`, the first fully faithful, are isomorphic.

## References

* [Stacks Project, Tag 0G01](https://stacks.math.columbia.edu/tag/0G01)
* [Stacks Project, Tag 0G0C](https://stacks.math.columbia.edu/tag/0G0C)
* [Stacks Project, Tag 0FZW](https://stacks.math.columbia.edu/tag/0FZW)
* [Stacks Project, Tag 0FD7](https://stacks.math.columbia.edu/tag/0FD7)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v' u u'

namespace AlgebraicGeometry

/-! ### Tensoring by an invertible module -/

section TensorRight

variable {X : Scheme.{u}}

/-- Tensoring on the right by a module `W`, as a functor. -/
abbrev tensorRightModules (W : X.Modules) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.sheaf.obj,
    Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
      (X.ringCatSheaf.property)⟩).flip.obj W

/-- Tensoring on the right by an invertible module is additive, being an equivalence. -/
instance additive_tensorRightModules (W : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W] :
    (tensorRightModules W).Additive := by
  have := Scheme.Modules.isEquivalence_invertibleTensorRightFunctor W
  have : PreservesLimitsOfSize.{0, 0} (tensorRightModules W) :=
    Adjunction.rightAdjoint_preservesLimits
      (@Functor.asEquivalence _ _ _ _ (tensorRightModules W)
        (Scheme.Modules.isEquivalence_invertibleTensorRightFunctor W)).symm.toAdjunction
  exact Functor.additive_of_preserves_binary_products _

/-- A module without nonzero global sections receives no nonzero morphism from `𝒪_X`. -/
lemma subsingleton_hom_unit_of_forall_eq_zero (M : X.Modules) (h : ∀ t : Γ(M, ⊤), t = 0) :
    Subsingleton (SheafOfModules.unit X.ringCatSheaf ⟶ M) :=
  ⟨fun _ _ => M.unitHomEquiv.injective
    ((Stacks.NonvanishingSpelling.sectionsEquiv X M).injective ((h _).trans (h _).symm))⟩

end TensorRight

attribute [local instance 100000] CoherentAbelian.coherentModulesAbelian

attribute [local instance] cohHasFiniteBiproducts

/-! ### The structure sheaf, restricted to the complement of the isolated points -/

section Structure

variable (X : Scheme.{u}) [IsNoetherian X]

/-- The structure sheaf, as a coherent module. -/
def cohUnit : SheafOfModules.CoherentModules X.ringCatSheaf :=
  ⟨SheafOfModules.unit X.ringCatSheaf, Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit X⟩

/-- The `X₁`-summand `𝒪_{X₁}` of the structure sheaf, `X₁` being the complement of the isolated
points. -/
def unitSummand : SheafOfModules.CoherentModules X.ringCatSheaf :=
  (cohDecomposition X).summand (cohUnit X) none

variable {X}

/-- On a reduced scheme, no associated point of `𝒪_{X₁}` is closed. -/
lemma not_isClosed_of_mem_associatedPoints_unitSummand [IsReduced X] (x : X)
    (hx : x ∈ Stacks.Divisors.associatedPoints (unitSummand X).obj) :
    ¬ IsClosed ({x} : Set X) := by
  intro hcl
  let i : ((unitSummand X).obj : X.Modules) ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    ((cohDecomposition X).incl (cohUnit X) none).hom
  let r : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ ((unitSummand X).obj : X.Modules) :=
    ((cohDecomposition X).proj (cohUnit X) none).hom
  have hid : i ≫ r = 𝟙 _ :=
    congrArg (fun φ => φ.hom) ((cohDecomposition X).incl_proj (cohUnit X) none)
  have : IsSplitMono i := IsSplitMono.mk' ⟨r, hid⟩
  have hgen : x ∈ genericPoints X := by
    rw [← weaklyAssociatedPointsOfScheme_eq_genericPoints]
    exact associatedPoints_subset_weaklyAssociatedPoints _
      (@associatedPoints_subset_of_mono X _ _ i (IsSplitMono.mono i) x hx)
  exact (cohDecomposition X).summand_mem (cohUnit X) none (associatedPoints_subset_support _ hx)
    (mem_isolatedPoints_of_mem_genericPoints_of_isClosed hgen hcl)

end Structure

/-! ### Twisting -/

section Twist

variable {X : Scheme.{u}} [IsNoetherian X]

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The tensor powers of `ℒ`, as coherent modules. -/
def cohPow (m : ℤ) : SheafOfModules.CoherentModules X.ringCatSheaf :=
  ⟨Stacks.Ample.tensorPowModule X L m,
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _⟩

/-- The twist `𝓕 ⊗ ℒ^{⊗ m}` of a coherent module, as a coherent module. -/
def cohTwist (G : SheafOfModules.CoherentModules X.ringCatSheaf) (m : ℤ) :
    SheafOfModules.CoherentModules X.ringCatSheaf :=
  ⟨Stacks.EnriquesSeveriZariski.twist L G.obj m,
    Stacks.EnriquesSeveriZariski.isCoherent_twist L G.obj m⟩

variable {L} in
/-- Twisting does not enlarge the support. -/
lemma cohPiece_cohTwist {i : Option (Fin (Nat.card (isolatedPoints X)))}
    {G : SheafOfModules.CoherentModules X.ringCatSheaf} (hG : cohPiece X i G) (m : ℤ) :
    cohPiece X i (cohTwist L G m) :=
  (Stacks.Chow.supp_tensorModules_subset _ _).trans hG

omit [IsNoetherian X] [Stacks.Ample.IsInvertibleModule X L] in
/-- The underlying morphism of a finite sum of morphisms of coherent modules is the sum of the
underlying morphisms. -/
lemma hom_sum {G G' : SheafOfModules.CoherentModules X.ringCatSheaf} {ι : Type*} (s : Finset ι)
    (f : ι → (G ⟶ G')) : (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  map_sum (⟨⟨fun φ => φ.hom, rfl⟩, fun _ _ => rfl⟩ : (G ⟶ G') →+ (G.obj ⟶ G'.obj)) f s

/-- The underlying module of a coherent module, as an object of `X.Modules`. -/
abbrev cohModule (G : SheafOfModules.CoherentModules X.ringCatSheaf) : X.Modules := G.obj

/-- The underlying morphism of modules of a morphism of coherent modules. -/
abbrev cohModuleMap {G G' : SheafOfModules.CoherentModules X.ringCatSheaf} (f : G ⟶ G') :
    cohModule G ⟶ cohModule G' := f.hom

/-- A morphism `𝒪_X ⟶ P ⟶ ℒ^{⊗ j}` through a coherent module `P` supported away from the
isolated points vanishes when `𝒪_{X₁} ⊗ ℒ^{⊗ j}` has no nonzero global section. -/
lemma comp_eq_zero_of_cohPiece_none (j : ℤ)
    (hvan : ∀ t : Γ(Stacks.EnriquesSeveriZariski.twist L (unitSummand X).obj j, ⊤), t = 0)
    {P : SheafOfModules.CoherentModules X.ringCatSheaf} (hP : cohPiece X none P)
    (a : Stacks.Ample.unitModule X ⟶ cohModule P)
    (k : cohModule P ⟶ Stacks.Ample.tensorPowModule X L j) : a ≫ k = 0 := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule X L j) := Stacks.Ample.isInvertibleModule_tensorPowModule X L j
  let T := tensorRightModules (Stacks.Ample.tensorPowModule X L j)
  have : T.Additive := additive_tensorRightModules _
  let d := cohDecomposition X
  let O := cohUnit X
  let e : T.obj (cohModule O) ≅ Stacks.Ample.tensorPowModule X L j :=
    Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.sheaf.obj
      X.ringCatSheaf.property (Stacks.Ample.tensorPowModule X L j)
  let k' : cohModule P ⟶ T.obj (cohModule O) := k ≫ e.inv
  have hsum : 𝟙 (cohModule O) = ∑ i, cohModuleMap (d.proj O i) ≫ cohModuleMap (d.incl O i) := by
    have h := congrArg (fun φ => φ.hom) (d.sum_proj_incl O)
    simp only [hom_sum] at h
    exact h.symm
  have hk' : k' = k' ≫ T.map (cohModuleMap (d.proj O none)) ≫
      T.map (cohModuleMap (d.incl O none)) := by
    conv_lhs => rw [← Category.comp_id k']
    rw [show 𝟙 (T.obj (cohModule O)) = T.map (𝟙 (cohModule O)) from (T.map_id _).symm, hsum,
      T.map_sum, Preadditive.comp_sum, Finset.sum_eq_single none]
    · rw [T.map_comp]
    · intro i _ hi
      have h0 := cohPiece_hom_eq_zero none i (Ne.symm hi) hP
        (cohPiece_cohTwist (L := L) (d.summand_mem O i) j)
        (ObjectProperty.homMk (k' ≫ T.map (cohModuleMap (d.proj O i))))
      have h0' : k' ≫ T.map (cohModuleMap (d.proj O i)) = 0 := congrArg (fun φ => φ.hom) h0
      rw [T.map_comp, ← Category.assoc, h0', zero_comp]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hsub : Subsingleton (Stacks.Ample.unitModule X ⟶ T.obj (cohModule (d.summand O none))) :=
    subsingleton_hom_unit_of_forall_eq_zero _ hvan
  have hk : k = k' ≫ e.hom := by simp only [k', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h1 : a ≫ k = (a ≫ k' ≫ T.map (cohModuleMap (d.proj O none))) ≫
      T.map (cohModuleMap (d.incl O none)) ≫ e.hom := by
    conv_lhs => rw [hk, hk']
    simp only [Category.assoc]
  rw [h1, hsub.elim (a ≫ k' ≫ T.map (cohModuleMap (d.proj O none))) 0, zero_comp]

end Twist

/-! ### Enough negative objects away from the isolated points -/

section Negative

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

include f in
/-- A scheme proper over a field is Noetherian. -/
lemma isNoetherian_of_isProper_spec : IsNoetherian X :=
  isNoetherian_of_locallyOfFiniteType f

variable [IsNoetherian X] [IsReduced X]

include f in
/-- The twists of `𝒪_{X₁}` by sufficiently negative powers of an ample `ℒ` have no nonzero global
section ([Stacks, Tag 0FD7] for `𝒪_{X₁}`). -/
lemma exists_forall_le_sections_twist_unitSummand_eq_zero (hL : Stacks.Ample.IsAmple X L) :
    ∃ j₀ : ℤ, ∀ j ≤ j₀,
      ∀ t : Γ(Stacks.EnriquesSeveriZariski.twist L (unitSummand X).obj j, ⊤), t = 0 :=
  Stacks.EnriquesSeveriZariski.forall_le_eq_zero_sections_twist L k f hL (unitSummand X).obj
    fun x hcl hx => not_isClosed_of_mem_associatedPoints_unitSummand x hx hcl

omit [IsReduced X] in
/-- Let `𝓕` be a coherent module supported away from the isolated points which is a quotient of a
sum of copies of `ℒ^{⊗ -n}`. If `𝒪_{X₁} ⊗ ℒ^{⊗ j}` has no nonzero global section for `j ≤ j₀`,
then there is no nonzero morphism `𝓕 ⟶ ℒ^{⊗ c}` for `c + n ≤ j₀`. -/
lemma subsingleton_hom_tensorPow {G : SheafOfModules.CoherentModules X.ringCatSheaf}
    (hG : cohPiece X none G) {n : ℤ} {ι : Type u}
    {b : Bicone fun _ : ι => Stacks.Ample.tensorPowModule X L (-n)} (hb : b.IsBilimit)
    (p : b.pt ⟶ cohModule G) [Epi p] {j₀ : ℤ}
    (hj₀ : ∀ j ≤ j₀,
      ∀ t : Γ(Stacks.EnriquesSeveriZariski.twist L (unitSummand X).obj j, ⊤), t = 0)
    (c : ℤ) (hc : c + n ≤ j₀) :
    Subsingleton (cohModule G ⟶ Stacks.Ample.tensorPowModule X L c) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule X L n) := Stacks.Ample.isInvertibleModule_tensorPowModule X L n
  let T := tensorRightModules (Stacks.Ample.tensorPowModule X L n)
  let e₁ : T.obj (Stacks.Ample.tensorPowModule X L (-n)) ≅ Stacks.Ample.unitModule X :=
    Stacks.Ample.tensorPowModuleAddIso X L (-n) n ≪≫
      eqToIso (congrArg (Stacks.Ample.tensorPowModule X L) (neg_add_cancel n)) ≪≫
      Stacks.Ample.tensorPowModuleZeroIso X L
  let e₂ : T.obj (Stacks.Ample.tensorPowModule X L c) ≅ Stacks.Ample.tensorPowModule X L (c + n) :=
    Stacks.Ample.tensorPowModuleAddIso X L c n
  have hzero : ∀ (m : ι) (φ : cohModule G ⟶ Stacks.Ample.tensorPowModule X L c),
      b.ι m ≫ p ≫ φ = 0 := by
    intro m φ
    apply Scheme.Modules.eq_zero_of_tensorRightMap_eq_zero (Stacks.Ample.tensorPowModule X L n)
    change T.map (b.ι m ≫ p ≫ φ) = 0
    have h := comp_eq_zero_of_cohPiece_none L (c + n) (hj₀ _ hc) (P := cohTwist L G n)
      (cohPiece_cohTwist hG n) (e₁.inv ≫ T.map (b.ι m ≫ p)) (T.map φ ≫ e₂.hom)
    have h' : T.map (b.ι m ≫ p ≫ φ) =
        e₁.hom ≫ ((e₁.inv ≫ T.map (b.ι m ≫ p)) ≫ T.map φ ≫ e₂.hom) ≫ e₂.inv := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id,
        T.map_comp]
    exact h'.trans ((congrArg (fun z => e₁.hom ≫ z ≫ e₂.inv) h).trans (by simp))
  refine ⟨fun φ₁ φ₂ => (cancel_epi p).1 (hb.isColimit.hom_ext fun ⟨m⟩ => ?_)⟩
  change b.ι m ≫ p ≫ φ₁ = b.ι m ≫ p ≫ φ₂
  rw [hzero, hzero]

include f in
/-- The coherent modules supported away from the isolated points have enough negative objects in
the sense of [Stacks, Tag 0G0C]: every such `𝓕` is a quotient `N ⟶ 𝓕` of a coherent module `N`
with `Hom(𝓕, N) = 0`. -/
lemma exists_epi_subsingleton_hom_of_cohPiece_none (hL : Stacks.Ample.IsAmple X L)
    (G : SheafOfModules.CoherentModules X.ringCatSheaf) (hG : cohPiece X none G) :
    ∃ (N : SheafOfModules.CoherentModules X.ringCatSheaf) (p : N ⟶ G),
      Epi p ∧ Subsingleton (G ⟶ N) := by
  obtain ⟨j₀, hj₀⟩ := exists_forall_le_sections_twist_unitSummand_eq_zero f L hL
  have hqc : G.obj.IsQuasicoherent := GroupoidScheme.isQuasicoherent_of_isCoherent _ G.property
  have hft : SheafOfModules.IsFiniteType.{u, u, u} G.obj := G.property.isFiniteType
  obtain ⟨n₀, hn₀⟩ :=
    Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple L hL G.obj hqc hft
  obtain ⟨σ, hσ⟩ := hn₀ n₀ le_rfl
  obtain ⟨b, hb, p, hp, -⟩ :=
    Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free L n₀ G.obj _ σ.epi
  let n' := max n₀ (n₀ - j₀)
  obtain ⟨σ', hσ'⟩ := hn₀ n' (le_max_left _ _)
  obtain ⟨b', hb', p', hp', -⟩ :=
    Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free L n' G.obj _ σ'.epi
  have hvan : Subsingleton (cohModule G ⟶ Stacks.Ample.tensorPowModule X L (-n')) :=
    subsingleton_hom_tensorPow L hG hb p hj₀ (-n') (by omega)
  have := hσ'
  obtain ⟨r, ⟨eI⟩⟩ := Finite.exists_equiv_fin σ'.I
  let b'' := b'.whisker eI.symm
  have hb'' : b''.IsBilimit := (b'.whiskerIsBilimitIff eI.symm).symm hb'
  let N : SheafOfModules.CoherentModules X.ringCatSheaf := ⨁ fun _ : Fin r => cohPow L (-n')
  let eN : cohModule N ≅ b''.pt :=
    (ObjectProperty.ι _).mapBiproduct (fun _ : Fin r => cohPow L (-n')) ≪≫
      (biproduct.uniqueUpToIso _ hb'').symm
  refine ⟨N, ObjectProperty.homMk (eN.hom ≫ p'), ?_, ⟨fun g₁ g₂ => ObjectProperty.hom_ext _ ?_⟩⟩
  · apply (ObjectProperty.ι _).epi_of_epi_map
    change Epi (eN.hom ≫ p')
    exact @epi_comp _ _ _ _ _ eN.hom inferInstance p' hp'
  · exact (cancel_mono eN.hom).1 (hb''.isLimit.hom_ext fun _ => hvan.elim _ _)

end Negative

/-! ### The siblings -/

section Siblings

/-- Let `X` be a reduced scheme projective over a field `k`. Sibling exact functors
`F, F' : D^b(Coh(𝒪_X)) ⥤ 𝒟`, with `F` fully faithful, are isomorphic. This is the first sentence
of [Stacks, Tag 0G01]. "Projective over `k`" is read as "proper over `k` with an ample invertible
module", which it implies. -/
theorem nonempty_iso_of_areSiblings_of_isReduced_of_isAmple
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    [HasDerivedCategory.{w} (SheafOfModules.CoherentModules X.ringCatSheaf)]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (F F' : DerivedCategory.Bounded (SheafOfModules.CoherentModules X.ringCatSheaf) ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : AreSiblings F F') (hF : Nonempty F.FullyFaithful) : Nonempty (F ≅ F') := by
  have : IsNoetherian X := isNoetherian_of_isProper_spec f
  refine (cohDecomposition X).nonempty_iso_of_areSiblings F F' h hF fun i => ?_
  rcases i with _ | j
  · exact Or.inl fun G hG => exists_epi_subsingleton_hom_of_cohPiece_none f L hL G hG
  · refine Or.inr fun {G G'} hG hG' p hp => ?_
    have hx := (isolatedPointsEnum X j).2
    have : Epi p.hom := (ObjectProperty.ι _).map_epi p
    obtain ⟨s, hs⟩ := exists_section_of_supp_subset_singleton hx hG hG' p.hom
    exact IsSplitEpi.mk' ⟨ObjectProperty.homMk s, ObjectProperty.hom_ext _ hs⟩

end Siblings

end AlgebraicGeometry

end
