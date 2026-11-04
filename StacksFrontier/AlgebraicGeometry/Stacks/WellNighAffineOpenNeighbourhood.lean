module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatChartOpenChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatChartInvariantOpens
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPointSetObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeOfRepresented
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineOpenWithin
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineOpenQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Groupoids.CechDescentInvariantOpen
public import StacksFrontier.AlgebraicGeometry.Properties.FiniteSetInBasicOpen

/-!
# Well-nigh affine open neighbourhoods inside an open substack

Let `𝒰` be a well-nigh affine algebraic stack (Stacks 0DUL), with chart `f : W ⟶ 𝒰` from an
affine scheme, surjective, flat, finite and of finite presentation, and let `𝒰' ⊆ 𝒰` be an open
substack containing a point `v`. Then `v` has a well-nigh affine open neighbourhood inside `𝒰'`.
This is the step of the proof of Stacks 0DUE that shrinks the étale chart of Stacks 0DU4 to the
stabilizer-preserving locus of Stacks 0DUA, and it is the source's argument: the inverse image
`f⁻¹(𝒰')` is an `R`-invariant open of `W` for the groupoid `R = W ×_𝒰 W` (Stacks 0507), whose
source and target are finite locally free; the `R`-orbit of a point `w` of `W` over `v` is finite
and lies in `f⁻¹(𝒰')`, so `w` has an `R`-invariant affine open neighbourhood `Q ⊆ f⁻¹(𝒰')`
(Properties, Lemma 01ZY, and Groupoids, Lemma 03JE); the open substack `𝒰''` with `f⁻¹(𝒰'') = Q`
is well-nigh affine, with chart `Q ⟶ 𝒰''`.

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.property_iff_pointClass_mem_pointSet`: an open substack
  contains a field-valued point exactly when it contains its class.
* `AlgebraicGeometry.Stack.exists_openSubstack_isWellNighAffine_of_mem`: the shrinking step.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An open substack contains a field-valued point exactly when its point set contains the
class of that point**: one direction is the definition of the point set, the other is that the
property of an open substack is read on points (`OpenSubstack.property_eq_pointsWithin`), every
field-valued point mapping to the given one having the same class. -/
theorem OpenSubstack.property_iff_pointClass_mem_pointSet {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : OpenSubstack 𝒳) (p : FieldValuedPoint B S hS 𝒳.val.val) :
    U.property p.obj ↔ pointClass B S hS 𝒳.val.val 𝒳.val.property p ∈ U.pointSet B S hS := by
  refine ⟨fun h => (OpenSubstack.mem_pointSet_iff B S hS U _).2 ⟨p, h, rfl⟩, fun h => ?_⟩
  rw [U.property_eq_pointsWithin]
  intro q m
  rwa [(class_eq_class_iff_hasCommonExtension B S hS _ _ q p).2 ⟨q, ⟨𝟙 _⟩, ⟨m⟩⟩]

/-- An open subscheme `Z` of the target of two morphisms `s t : V ⟶ W` of the site has
`s⁻¹(Z) ⊆ t⁻¹(Z)` as soon as the inverse images of the subspace it cuts out satisfy the same
inclusion: test it on the open subscheme `s⁻¹(Z)` of `V`. -/
theorem preimage_le_of_subspaceOfOpens_preimage_le {V W : BigFppfOver B S hS} (s t : V ⟶ W)
    (Z : ((BigFppfOver.toScheme B S hS).obj W).Opens)
    (h : (Space.subspaceOfOpens B S hS W Z).preimage (yoneda.map s) ≤
      (Space.subspaceOfOpens B S hS W Z).preimage (yoneda.map t)) :
    (BigFppfOver.toScheme B S hS).map s ⁻¹ᵁ Z ≤ (BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ Z := by
  intro x hx
  let O := (BigFppfOver.toScheme B S hS).map s ⁻¹ᵁ Z
  let i := BigFppfOver.openSubHom B S hS V O
  have hi : (BigFppfOver.toScheme B S hS).map i = O.ι := Space.openSubHom_toScheme B S hS V O
  have hmem : i ≫ s ∈ (Space.subspaceOfOpens B S hS W Z).obj (op _) := by
    rw [Space.mem_subspaceOfOpens_iff]
    intro y
    rw [Functor.map_comp, hi, Scheme.Hom.comp_apply]
    exact y.2
  have ht : i ∈ ((Space.subspaceOfOpens B S hS W Z).preimage (yoneda.map t)).obj (op _) :=
    h (op _) (show i ∈ ((Space.subspaceOfOpens B S hS W Z).preimage (yoneda.map s)).obj (op _)
      from hmem)
  change i ≫ t ∈ (Space.subspaceOfOpens B S hS W Z).obj (op _) at ht
  rw [Space.mem_subspaceOfOpens_iff] at ht
  obtain ⟨y, rfl⟩ : x ∈ Set.range O.ι := by rwa [O.range_ι]
  have := ht y
  rwa [Functor.map_comp, hi, Scheme.Hom.comp_apply] at this

/-- In a groupoid scheme with affine objects and finite locally free source and target, a point
of an invariant open `Z` has an invariant affine open neighbourhood contained in `Z`: its orbit is
finite and lies in `Z`, so it lies in a basic open of the objects inside `Z` (Properties, Lemma
01ZY), and Groupoids, Lemma 03JE, applies inside that basic open. -/
private theorem exists_isInvariantOpen_isAffineOpen_mem_le_of_mem
    {X : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme X) [IsAffine G.objects.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.target.left] (Z : G.objects.left.Opens)
    (hZ : Stacks.Groupoids.IsInvariantOpen G Z) (w : G.objects.left) (hw : w ∈ Z) :
    ∃ Q : G.objects.left.Opens,
      Stacks.Groupoids.IsInvariantOpen G Q ∧ IsAffineOpen Q ∧ w ∈ Q ∧ Q ≤ Z := by
  have hT : G.target.left.base '' (G.source.left.base ⁻¹' {w}) ⊆ (Z : Set G.objects.left) := by
    rintro _ ⟨r, hr, rfl⟩
    exact hZ r (show G.source.left.base r ∈ (Z : Set G.objects.left) from hr ▸ hw)
  have : IsFinite G.source.left :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      G.source.left).mp inferInstance).1
  obtain ⟨r, hrT, hrZ⟩ := (isAffineOpen_top G.objects.left).exists_basicOpen_subset_of_finite
    ((G.source.left.finite_preimage_singleton w).image _) (fun x _ => trivial) Z hT
  obtain ⟨Q, hQinv, hQaff, hwQ, hQr⟩ := GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem_le
    G w _ ((isAffineOpen_top G.objects.left).basicOpen r) hrT
  exact ⟨Q, hQinv, hQaff, hwQ, hQr.trans hrZ⟩

/-- **A point of an open substack of a well-nigh affine algebraic stack has a well-nigh affine
open neighbourhood inside it.** Let `𝒰` be well-nigh affine (Stacks 0DUL), `𝒰' ⊆ 𝒰` an open
substack and `v ∈ |𝒰'|`. Then there is an open substack `𝒰'' ⊆ 𝒰` with `v ∈ |𝒰''|`,
`|𝒰''| ⊆ |𝒰'|` and `𝒰''` well-nigh affine.

This is the step of the proof of Stacks 0DUE between Lemma 0DUA and Lemma 0DUM: for a chart
`f : W ⟶ 𝒰` as in 0DUL, the inverse image of `𝒰'` is an invariant open of `W` for the groupoid
`R = W ×_𝒰 W` (Stacks 0507), the orbit of a point of `W` over `v` is finite since `s` is
finite, and Properties, Lemma 01ZY, with Groupoids, Lemma 03JE, give an invariant affine open
`Q ⊆ f⁻¹(𝒰')` containing it; `𝒰''` is the open substack with `f⁻¹(𝒰'') = Q`, with chart
`Q ⟶ 𝒰''`. -/
theorem exists_openSubstack_isWellNighAffine_of_mem (𝒰 : AlgebraicStacks.{u, w} B S hS)
    (h𝒰 : IsWellNighAffine.{u, w} B S hS 𝒰) (𝒰' : OpenSubstack 𝒰)
    (v : AlgebraicStacks.points B S hS 𝒰) (hv : v ∈ 𝒰'.pointSet B S hS) :
    ∃ 𝒰'' : OpenSubstack 𝒰, v ∈ 𝒰''.pointSet B S hS ∧
      𝒰''.pointSet B S hS ⊆ 𝒰'.pointSet B S hS ∧
        IsWellNighAffine.{u, w} B S hS 𝒰''.toAlgebraicStack := by
  classical
  obtain ⟨W, hW, f, hsurj, hflat, hfin, hfp⟩ := h𝒰
  let eU : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
      (presheafOfCategories
        ((⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS).obj ⋙
          typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver W
  obtain ⟨V, eR, s, t, c, hG, hs, ht, hsF, htF, ⟨hE⟩⟩ :=
    exists_flatChartPresentation 𝒰 f eU hsurj hflat hfin hfp
  -- the invariant open `Z = f⁻¹(𝒰')` of `W` (Stacks 0507)
  have hP : ∀ {a b : 𝒰.val.val.obj}, (a ⟶ b) → 𝒰'.property b → 𝒰'.property a :=
    fun m h => OpenSubstack.prop_of_hom B S hS 𝒰' m h
  have : 𝒰'.property.IsClosedUnderIsomorphisms := 𝒰'.strictlyFull
  let π := presentationProjection (FlatChart.groupoid eU eR) (FlatChart.canonical eU eR)
    (FlatChart.canonical_comp_p eU eR)
  let ZP := presentationSubfunctor hP π
  have hZP : Space.IsOpenSubspace B S hS ZP :=
    isSubspaceWith_presentationSubfunctor hP π (OpenSubstack.equivIsSubstackWith 𝒰 𝒰').2
      (isAlgebraicSpace_yoneda B S hS W)
  let Z := Space.opensOfOpenSubspace B S hS W ZP hZP
  have hZ : Space.subspaceOfOpens B S hS W Z = ZP :=
    Space.subspaceOfOpens_opensOfOpenSubspace B S hS W ZP hZP
  have hchar : ∀ z : (schemeStack.{u, w} B S hS W).val.val.obj,
      𝒰'.property (f.hom.hom.obj z) ↔
        ∀ y, ((BigFppfOver.toScheme B S hS).map z.hom).base y ∈ Z := by
    intro z
    rw [← 𝒰'.property.prop_iff_of_iso ((FlatChart.presentation eU eR).extends_f.1.app z),
      ← Space.mem_subspaceOfOpens_iff B S hS W Z z.hom, hZ]
    rfl
  have hinvZ : (Space.subspaceOfOpens B S hS W Z).preimage (yoneda.map t) =
      (Space.subspaceOfOpens B S hS W Z).preimage (yoneda.map s) := by
    rw [hZ, hs, ht]
    exact presentationSubfunctor_preimage_target (FlatChart.groupoid eU eR)
      (FlatChart.canonical eU eR) (FlatChart.canonical_comp_p eU eR) hP
  have hst : (BigFppfOver.toScheme B S hS).map s ⁻¹ᵁ Z =
      (BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ Z :=
    le_antisymm (preimage_le_of_subspaceOfOpens_preimage_le s t Z hinvZ.symm.le)
      (preimage_le_of_subspaceOfOpens_preimage_le t s Z hinvZ.le)
  -- the groupoid scheme `(W, V, s, t, c)` and a point `w` of `W` over `v`
  let G := Space.representedGroupoidScheme s t c hG
  have : Stacks.Morphisms.IsFiniteLocallyFree G.source.left := hsF
  have : Stacks.Morphisms.IsFiniteLocallyFree G.target.left := htF
  let Z' : Set G.objects.left := (Z : Set ((BigFppfOver.toScheme B S hS).obj W))
  have hZinv : Stacks.Groupoids.IsInvariantSet G Z' :=
    (Stacks.Groupoids.isInvariantSet_iff_preimage_eq G Z').2 (congrArg SetLike.coe hst)
  obtain ⟨z₀, hz₀⟩ := hsurj v
  obtain ⟨pz, rfl⟩ := Quotient.exists_rep z₀
  let τ : (BigFppfOver.toScheme B S hS).obj pz.obj.left :=
    ((BigFppfOver.toScheme B S hS).mapIso (eqToIso pz.over) ≪≫ pz.isSpec).inv.base
      (IsLocalRing.closedPoint pz.carrier)
  have hτ : ∀ y : (BigFppfOver.toScheme B S hS).obj pz.obj.left, y = τ := fun y =>
    (Scheme.homeoOfIso ((BigFppfOver.toScheme B S hS).mapIso (eqToIso pz.over) ≪≫
      pz.isSpec)).injective (Subsingleton.elim _ _)
  let w : G.objects.left := ((BigFppfOver.toScheme B S hS).map pz.obj.hom).base τ
  rw [← hz₀] at hv
  have hwZ : w ∈ Z :=
    (hchar pz.obj).1 ((OpenSubstack.property_iff_pointClass_mem_pointSet 𝒰' _).2 hv) τ
  -- the orbit of `w` lies in `Z`; an invariant affine open `Q ∋ w` inside `Z`
  have : IsAffine G.objects.left := hW
  obtain ⟨Q, hQinv, hQaff, hwQ, hQZ⟩ :=
    exists_isInvariantOpen_isAffineOpen_mem_le_of_mem G
      (show G.objects.left.Opens from Z) hZinv w hwZ
  -- the open substack `𝒰''` with `f⁻¹(𝒰'') = Q`
  have hQst : (BigFppfOver.toScheme B S hS).map s ⁻¹ᵁ Q =
      (BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ Q :=
    GroupoidScheme.source_preimage_eq_target_preimage_of_isInvariantOpen G Q hQinv
  obtain ⟨𝒰'', h𝒰'', -⟩ := FlatChart.exists_openSubstack hE (Space.subspaceOfOpens B S hS W Q)
    (Space.isOpenSubspace_subspaceOfOpens B S hS W Q)
    (by
      rw [← hs, ← ht]
      exact FlatChart.preimage_subspaceOfOpens_le s t Q hQst)
  have hchar'' : ∀ z : (schemeStack.{u, w} B S hS W).val.val.obj,
      𝒰''.property (f.hom.hom.obj z) ↔
        ∀ y, ((BigFppfOver.toScheme B S hS).map z.hom).base y ∈ Q := fun z =>
    (h𝒰'' z).trans (Space.mem_subspaceOfOpens_iff B S hS W Q z.hom)
  refine ⟨𝒰'', ?_, ?_, ?_⟩
  · rw [← hz₀]
    exact (OpenSubstack.property_iff_pointClass_mem_pointSet 𝒰'' _).1
      ((hchar'' pz.obj).2 fun y => hτ y ▸ hwQ)
  · intro q hq
    obtain ⟨z₁, hz₁⟩ := hsurj q
    obtain ⟨pz₁, rfl⟩ := Quotient.exists_rep z₁
    rw [← hz₁] at hq ⊢
    exact (OpenSubstack.property_iff_pointClass_mem_pointSet 𝒰' _).1 ((hchar pz₁.obj).2 fun y =>
      hQZ ((hchar'' pz₁.obj).1 ((OpenSubstack.property_iff_pointClass_mem_pointSet 𝒰'' _).2 hq) y))
  · exact FlatChart.isWellNighAffine_of_isAffineOpen f 𝒰'' Q
      (fun z => (hchar'' z).trans Set.range_subset_iff.symm) hQaff hsurj hflat hfin hfp

end AlgebraicGeometry.Stack

end
