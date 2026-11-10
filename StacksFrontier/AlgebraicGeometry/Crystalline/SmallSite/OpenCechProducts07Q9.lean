module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalFlat
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelCoproduct07Q9

/-!
# The pro-products of the Čech system of an affine open

Fix a global crystalline situation `(p, (S, I, γ), X)`, affine opens `V ⊆ S` and `W ⊆ X` with `W`
mapping into `V`, and a surjective polynomial presentation of `Γ(W, ⊤)` over `Γ(V, ⊤)`, and let
`T = openSystem07Q9` be the cosimplicial system `(W, Spec D(n)/(p)^{N + e}, δ(n))` of that
presentation carried into `Cris(X/S)`.  [Stacks, Tag 07L4] says that `D(n)` is the coproduct of
`n + 1` copies of `D(0)`; on the levels of the system this says that `T(n)` is the product of
`n + 1` copies of `T(0)` in the pro-category, against every object with affine ambient scheme.

* **Existence.**  For every object `B` with affine ambient scheme and every family of `n + 1`
  morphisms `B ⟶ T(0)_e`, there is a morphism `B ⟶ T(n)_{e'}`, for some `e' ≥ e`, whose composites
  with the vertex maps `T(n)_{e'} ⟶ T(0)_{e'}` are the members of the family followed by the tower
  map `T(0)_e ⟶ T(0)_{e'}`.
* **Uniqueness.**  Two morphisms `B ⟶ T(n)_e` with the same composites with all the vertex maps
  are equal.

The proof reduces to thickenings of the whole of `W`, where it is
`exists_wholeSpaceSystemOf_desc` and `wholeSpaceSystemOf_hom_ext`, by the cofilteredness of the
comma categories of the inclusion of the chaotic subsite into the affine objects,
`SmallSite.isCofiltered_structuredArrow_wholeToAffineSubsite`.

## Main results

* `exists_wholeSpaceSystemOf_desc_of_isAffineObject` and
  `wholeSpaceSystemOf_hom_ext_of_isAffineObject` — the two halves for `X` and `S` affine and an
  arbitrary affine object.
* `exists_openSystem07Q9_desc` and `openSystem07Q9_hom_ext` — the two halves for the transported
  system.

## References

* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

/-- In a cofiltered category, two objects `X` and `X'` with morphisms `f i` and `f' i` to each
member of a finite family of objects are dominated by one object on which the two agree. -/
private theorem CategoryTheory.IsCofiltered.exists_comp_eq_comp_of_finite {C : Type*} [Category C]
    [IsCofiltered C] {ι : Type*} [Finite ι] {X X' : C} {Z : ι → C} (f : ∀ i, X ⟶ Z i)
    (f' : ∀ i, X' ⟶ Z i) :
    ∃ (P : C) (t : P ⟶ X) (t' : P ⟶ X'), ∀ i, t ≫ f i = t' ≫ f' i := by
  classical
  cases nonempty_fintype ι
  let O : Finset C := insert X (insert X' (Finset.univ.image Z))
  have mX : X ∈ O := Finset.mem_insert_self _ _
  have mX' : X' ∈ O := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have mZ (i : ι) : Z i ∈ O :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_univ i)))
  let H : Finset (Σ' (P Q : C) (_ : P ∈ O) (_ : Q ∈ O), P ⟶ Q) :=
    Finset.univ.image (fun i ↦ ⟨X, Z i, mX, mZ i, f i⟩) ∪
      Finset.univ.image (fun i ↦ ⟨X', Z i, mX', mZ i, f' i⟩)
  obtain ⟨P, T, hT⟩ := IsCofiltered.inf_exists O H
  refine ⟨P, T mX, T mX', fun i ↦ ?_⟩
  rw [hT mX (mZ i) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))),
    hT mX' (mZ i) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))]

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

section Affine

/-- The structure morphism of a comma object, followed by the image of the right component of a
morphism of comma objects, is the structure morphism of the target. -/
private theorem hom_hom_comp_wholeι_map_right {S : GlobalCrystallineSituation.{u}}
    [IsAffine S.X] [IsAffine S.S.scheme]
    {A : AffineCrystallineThickening S} {P Q : StructuredArrow A (wholeToAffineSubsite (S := S))}
    (t : P ⟶ Q) : P.hom.hom ≫ (wholeι S).map t.right = Q.hom.hom :=
  congrArg (fun x ↦ x.hom) (StructuredArrow.w t)

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme] {ι : Type u}
  (g : MvPolynomial ι (affineSituation S hp).A →ₐ[(affineSituation S hp).A]
    (affineSituation S hp).C) (hg : Function.Surjective g)

/-- **The existence half of [Stacks, Tag 07L4] against an affine object**, for `X` and `S`
affine: a family of `n + 1` morphisms from an object of `Cris(X/S)` with affine thickened and
ambient schemes into a level of `wholeSpaceSystemOf` in degree `0` is induced, after a tower map,
by a morphism into a deeper level in degree `n`.  The family factors through a single thickening
of the whole of `X`, by cofilteredness of the comma category, and there it is
`exists_wholeSpaceSystemOf_desc`. -/
theorem exists_wholeSpaceSystemOf_desc_of_isAffineObject (B : CrystallineThickening S)
    (hB : IsAffineObject S B) (n e : ℕ)
    (q : Fin (n + 1) → (B ⟶ ((wholeSpaceSystemOf S hp g hg).obj (op ⦋0⦌)).obj e)) :
    ∃ (e' : ℕ) (hee' : e ≤ e')
      (k : B ⟶ ((wholeSpaceSystemOf S hp g hg).obj (op ⦋n⦌)).obj e'),
      ∀ i : Fin (n + 1),
        k ≫ ((wholeSpaceSystemOf S hp g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op).app e' =
          q i ≫ ((wholeSpaceSystemOf S hp g hg).obj (op ⦋0⦌)).map (homOfLE hee') := by
  let A : AffineCrystallineThickening S := ⟨B, hB⟩
  have := isCofiltered_structuredArrow_wholeToAffineSubsite hp A
  let Y₀ : WholeSpaceThickening S := ((wholeSiteEquivLittleAffine hp).inverse.obj
    (((affineLevelSystem (affineSituation S hp) g hg).obj ⦋0⦌).obj (op e))).unop
  let X : Fin (n + 1) → StructuredArrow A (wholeToAffineSubsite (S := S)) := fun i ↦
    StructuredArrow.mk (Y := Y₀) (ObjectProperty.homMk (q i))
  let c := IsCofiltered.cone (Discrete.functor X)
  obtain ⟨e', hee', k₀, hk₀⟩ := exists_wholeSpaceSystemOf_desc hp g hg c.pt.right n e
    fun i ↦ (wholeι S).map (c.π.app ⟨i⟩).right
  refine ⟨e', hee', c.pt.hom.hom ≫ k₀, fun i ↦ ?_⟩
  exact (Category.assoc _ _ _).trans ((congrArg (c.pt.hom.hom ≫ ·) (hk₀ i)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (hom_hom_comp_wholeι_map_right (c.π.app ⟨i⟩)))))

/-- **The uniqueness half of [Stacks, Tag 07L4] against an affine object**, for `X` and `S`
affine: two morphisms from an object of `Cris(X/S)` with affine thickened and ambient schemes into
a level of `wholeSpaceSystemOf` in degree `n` which agree after every vertex map are equal.  Both
factor through a single thickening of the whole of `X` on which the vertex composites already
agree, by cofilteredness of the comma category, and there it is `wholeSpaceSystemOf_hom_ext`. -/
theorem wholeSpaceSystemOf_hom_ext_of_isAffineObject (B : CrystallineThickening S)
    (hB : IsAffineObject S B) {n e : ℕ}
    (k k' : B ⟶ ((wholeSpaceSystemOf S hp g hg).obj (op ⦋n⦌)).obj e)
    (h : ∀ i : Fin (n + 1),
      k ≫ ((wholeSpaceSystemOf S hp g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op).app e =
        k' ≫ ((wholeSpaceSystemOf S hp g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op).app e) :
    k = k' := by
  let A : AffineCrystallineThickening S := ⟨B, hB⟩
  have := isCofiltered_structuredArrow_wholeToAffineSubsite hp A
  let L := affineLevelSystem (affineSituation S hp) g hg
  let Yn : WholeSpaceThickening S :=
    ((wholeSiteEquivLittleAffine hp).inverse.obj ((L.obj ⦋n⦌).obj (op e))).unop
  let Y₀ : WholeSpaceThickening S :=
    ((wholeSiteEquivLittleAffine hp).inverse.obj ((L.obj ⦋0⦌).obj (op e))).unop
  let v : Fin (n + 1) → (Yn ⟶ Y₀) := fun i ↦ ((wholeSiteEquivLittleAffine hp).inverse.map
    ((L.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)).app (op e))).unop
  let X : StructuredArrow A (wholeToAffineSubsite (S := S)) :=
    StructuredArrow.mk (Y := Yn) (ObjectProperty.homMk k)
  let X' : StructuredArrow A (wholeToAffineSubsite (S := S)) :=
    StructuredArrow.mk (Y := Yn) (ObjectProperty.homMk k')
  let Z : Fin (n + 1) → StructuredArrow A (wholeToAffineSubsite (S := S)) := fun i ↦
    StructuredArrow.mk (Y := Y₀) (ObjectProperty.homMk
      (k ≫ ((wholeSpaceSystemOf S hp g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op).app e))
  let f : ∀ i, X ⟶ Z i := fun i ↦ StructuredArrow.homMk (v i) rfl
  let f' : ∀ i, X' ⟶ Z i := fun i ↦ StructuredArrow.homMk (v i)
    (ObjectProperty.hom_ext _ (h i).symm)
  obtain ⟨P, t, t', ht⟩ := IsCofiltered.exists_comp_eq_comp_of_finite f f'
  have heq : (wholeι S).map t.right = (wholeι S).map t'.right :=
    wholeSpaceSystemOf_hom_ext hp g hg P.right _ _ fun i ↦
      congrArg (fun x : P ⟶ Z i ↦ (wholeι S).map x.right) (ht i)
  exact (hom_hom_comp_wholeι_map_right t).symm.trans
    ((congrArg (P.hom.hom ≫ ·) heq).trans (hom_hom_comp_wholeι_map_right t'))

end Affine

section Open

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V) {ι : Type u}
  (g : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A →ₐ[(openAffineSituation07Q9 S hW hVW).A]
    (openAffineSituation07Q9 S hW hVW).C) (hg : Function.Surjective g)

/-- An object of `Cris(X/S)` admitting a morphism to an object of the transported system lies over
`W`. -/
theorem range_toX_subset_of_hom_openSystem07Q9 (B : CrystallineThickening S) {n e : ℕ}
    (k : B ⟶ ((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e) :
    Set.range B.obj.toX.base ⊆ (W : Set S.X) := by
  rw [← k.hom.toX_naturality, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    ← range_toX_openSystem07Q9 S hV hW hVW g hg n e]
  exact Set.image_subset_range _ _

/-- The local reading in `Cris(W/S|_V)` of an object of `Cris(X/S)` with affine ambient scheme
lying over `W` is an affine object. -/
theorem isAffineObject_localObject (B : CrystallineThickening S)
    (hB : IsAffine B.obj.thickening.target.scheme)
    (hBW : Set.range B.obj.toX.base ⊆ (W : Set S.X)) :
    IsAffineObject (restrict S V W hVW) (CrystallineThickening.localObject S V W hVW B hBW) :=
  have : IsAffine
      (CrystallineThickening.localObject S V W hVW B hBW).obj.thickening.target.scheme := hB
  isAffineObject_of_isAffine (restrict S V W hVW) _

/-- **The existence half of the pro-product property of the Čech system of an affine open**,
[Stacks, Tag 07L4] read on finite levels: for an object `B` of `Cris(X/S)` with affine ambient
scheme and a family of `n + 1` morphisms `B ⟶ T(0)_e`, there are `e' ≥ e` and a morphism
`B ⟶ T(n)_{e'}` whose composite with the `i`-th vertex map is the `i`-th member of the family
followed by the tower map `T(0)_e ⟶ T(0)_{e'}`. -/
theorem exists_openSystem07Q9_desc (B : CrystallineThickening S)
    (hB : IsAffine B.obj.thickening.target.scheme) (n e : ℕ)
    (q : Fin (n + 1) → (B ⟶ ((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋0⦌)).obj e)) :
    ∃ (e' : ℕ) (hee' : e ≤ e')
      (k : B ⟶ ((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e'),
      ∀ i : Fin (n + 1),
        k ≫ ((openSystem07Q9 S hV hW hVW g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op).app e' =
          q i ≫ ((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋0⦌)).map (homOfLE hee') := by
  have hBW := range_toX_subset_of_hom_openSystem07Q9 S hV hW hVW g hg B (q 0)
  let ε := CrystallineThickening.extendLocalObjectIso S V W hVW B hBW
  obtain ⟨e', hee', k₀, hk₀⟩ := @exists_wholeSpaceSystemOf_desc_of_isAffineObject
    (restrict S V W hVW) (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (isAffine_restrictX07Q9 S hW hVW)
    (isAffine_restrictS07Q9 S hV hVW) ι g hg _
    (isAffineObject_localObject S hVW B hB hBW) n e
    fun i ↦ (smallExtend S V W hVW).preimage (ε.hom ≫ q i)
  refine ⟨e', hee', ε.inv ≫ (smallExtend S V W hVW).map k₀, fun i ↦ ?_⟩
  have h := congrArg (smallExtend S V W hVW).map (hk₀ i)
  rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage] at h
  change (ε.inv ≫ (smallExtend S V W hVW).map k₀) ≫ (smallExtend S V W hVW).map
      (((openLocalSystem07Q9 S hV hW hVW g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op).app e') =
    q i ≫ (smallExtend S V W hVW).map
      (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋0⦌)).map (homOfLE hee'))
  rw [Category.assoc, h]
  exact (congrArg (ε.inv ≫ ·) (Category.assoc _ _ _)).trans (Iso.inv_hom_id_assoc ε _)

/-- **The uniqueness half of the pro-product property of the Čech system of an affine open**:
two morphisms from an object of `Cris(X/S)` with affine ambient scheme into `T(n)_e` with the same
composites with all the vertex maps `T(n)_e ⟶ T(0)_e` are equal. -/
theorem openSystem07Q9_hom_ext (B : CrystallineThickening S)
    (hB : IsAffine B.obj.thickening.target.scheme) {n e : ℕ}
    (k k' : B ⟶ ((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e)
    (h : ∀ i : Fin (n + 1),
      k ≫ ((openSystem07Q9 S hV hW hVW g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op).app e =
        k' ≫ ((openSystem07Q9 S hV hW hVW g hg).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op).app e) :
    k = k' := by
  have hBW := range_toX_subset_of_hom_openSystem07Q9 S hV hW hVW g hg B k
  let ε := CrystallineThickening.extendLocalObjectIso S V W hVW B hBW
  have hpre := @wholeSpaceSystemOf_hom_ext_of_isAffineObject
    (restrict S V W hVW) (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (isAffine_restrictX07Q9 S hW hVW)
    (isAffine_restrictS07Q9 S hV hVW) ι g hg _
    (isAffineObject_localObject S hVW B hB hBW) n e
    ((smallExtend S V W hVW).preimage (ε.hom ≫ k)) ((smallExtend S V W hVW).preimage (ε.hom ≫ k'))
    fun i ↦ (smallExtend S V W hVW).map_injective (by
      rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
      exact (Category.assoc _ _ _).trans ((congrArg (ε.hom ≫ ·) (h i)).trans
        (Category.assoc _ _ _).symm))
  have h' := congrArg (fun x ↦ ε.inv ≫ (smallExtend S V W hVW).map x) hpre
  simp only [Functor.map_preimage] at h'
  exact ((Iso.inv_hom_id_assoc ε k).symm.trans h').trans (Iso.inv_hom_id_assoc ε k')

end Open

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
