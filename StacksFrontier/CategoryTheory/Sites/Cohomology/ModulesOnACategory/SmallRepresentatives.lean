module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.SmallSubcomplexesOfSections
import StacksCore.Tactic.StacksAttribute

/-!
# Small representatives in the derived category of modules on a category

Let `C` be a category with the chaotic topology and `R` a sheaf of rings on it. Stacks 0GYY
produces a cardinal `κ`, depending only on `C` and `R`, such that every complex `F` of
`R`-modules representing an object `K` of `D(R)` contains a subcomplex `H ⊆ F` which still
represents `K` and whose size is at most `max κ |K|`, where `|K|` is the least size of a
complex representing `K`.

The construction runs from Stacks 0GYX. One starts with a subcomplex
`H₀ ⊆ F` of size at most `max κ |K|` whose sections contain, in every degree and over every
object, a chosen cycle representative for each cycle of a *minimal* representative `G` of `K`;
this makes `H₀ ⟶ F` surjective on homology. It need not be injective on homology, so the
subcomplex is enlarged in countably many steps: at stage `n + 1` one adds, for each section of
`H_n` which becomes a boundary in `F`, a chosen bounding section of `F`. Each stage is again
bounded by Stacks 0GYX, and the union of the stages — a sectionwise supremum of subpresheaves,
which is a sheaf because the topology is chaotic — is a subcomplex of size at most
`max κ |K|` whose inclusion is both surjective and injective on homology, hence a
quasi-isomorphism.

## Main definitions

* `Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence`: the equivalence
  `SheafOfModules R ≌ PresheafOfModules R.obj` for the chaotic topology.
* `Stacks.ModulesOnACategory.derivedObjectSize`: the size `|K|` of an object of the derived
  category, the least size of a complex representing it.

## Main results

* `Stacks.ModulesOnACategory.exists_small_quasiIso_subcomplex`: Stacks 0GYY, the uniformly
  bounded quasi-isomorphic subcomplex.

## Implementation notes

The chaotic topology is the bottom Grothendieck topology, for which every presheaf is a sheaf;
that is what makes the sectionwise supremum of the stages a sheaf of modules without any
sheafification, and what makes `SheafOfModules R` equivalent to `PresheafOfModules R.obj`, so
that monomorphisms, epimorphisms and exactness can all be read off on sections.

"Subcomplex" is represented by a monomorphism of cochain complexes and "represents the same
derived object" by requiring that monomorphism to be a quasi-isomorphism; the minimum defining
`derivedObjectSize` is the infimum of the sizes of all representatives, which is attained
because the set of such sizes is a nonempty set of cardinals.

## References

* [Stacks Project, Tag 0GYY](https://stacks.math.columbia.edu/tag/0GYY)
* [Stacks Project, Tag 0GYX](https://stacks.math.columbia.edu/tag/0GYX)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.ModulesOnACategory

section ChaoticEquivalence

universe u v m r

/-- For the chaotic topology every presheaf is a sheaf, so sheaves of `R`-modules are the same
thing as presheaves of modules over the underlying presheaf of rings. The functor is the
forgetful functor and the inverse equips a presheaf of modules with the sheaf condition. -/
def chaoticSheafPresheafEquivalence {C : Type u} [Category.{v} C]
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r}) :
    SheafOfModules.{m} R ≌ PresheafOfModules.{m} R.obj where
  functor := SheafOfModules.forget R
  inverse.obj P := ⟨P, Presheaf.isSheaf_bot P.presheaf⟩
  inverse.map f := ⟨f⟩
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    apply SheafOfModules.hom_ext
    rfl)
  counitIso := NatIso.ofComponents (fun P => Iso.refl P) (by
    intro X Y f
    rfl)

end ChaoticEquivalence

universe v m r u

variable {C : Type u} [Category.{v} C]
variable (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
variable [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
variable [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [HasDerivedCategory (SheafOfModules.{m} R)]

/-- The size of a derived object is the least size of a complex representing it. -/
noncomputable def derivedObjectSize
    (K : DerivedCategory (SheafOfModules.{m} R)) : Cardinal.{max u v m r} :=
  sInf {c | ∃ F : CochainComplex (SheafOfModules.{m} R) ℤ,
    Nonempty (DerivedCategory.Q.obj F ≅ K) ∧
      c = complexSectionSize F}

private abbrev BaseBound (κ₀ : Cardinal.{max u v m r}) : Prop :=
  ∀ (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Ω : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (Opposite.op U))),
    ∃ (H : CochainComplex (SheafOfModules.{m} R) ℤ) (g : H ⟶ F),
      Mono g ∧
        (∀ (i : ℤ) (U : C) (x : (F.X i).val.obj (Opposite.op U)), x ∈ Ω i U →
          ∃ y : (H.X i).val.obj (Opposite.op U),
            (g.f i).val.app (Opposite.op U) y = x) ∧
        complexSectionSize H ≤
          max κ₀ (sectionFamilySize Ω)

private noncomputable def derivedIso_homologyIso
    {F G : CochainComplex (SheafOfModules.{m} R) ℤ}
    (e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj G) (i : ℤ) :
  F.homology i ≅ G.homology i :=
  ((DerivedCategory.homologyFunctorFactors (SheafOfModules.{m} R) i).app F).symm ≪≫
    (DerivedCategory.homologyFunctor (SheafOfModules.{m} R) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (SheafOfModules.{m} R) i).app G

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma epi_sections_surjective
    {X Y : SheafOfModules.{m} R} (f : X ⟶ Y) [Epi f] (U : C) :
    Function.Surjective (f.val.app (Opposite.op U)) := by
  have hf : Epi f.val := by
    refine ⟨?_⟩
    intro Z g h hgh
    let Z' : SheafOfModules.{m} R := ⟨Z, Presheaf.isSheaf_bot Z.presheaf⟩
    let g' : Y ⟶ Z' := ⟨g⟩
    let h' : Y ⟶ Z' := ⟨h⟩
    have hcomp : f ≫ g' = f ≫ h' := by
      apply SheafOfModules.hom_ext
      exact hgh
    have heq : g' = h' := (cancel_epi f).mp hcomp
    exact congrArg (fun q : Y ⟶ Z' => q.val) heq
  exact (PresheafOfModules.epi_iff_surjective f.val).mp hf (X := Opposite.op U)

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma sectionMap_injective_of_mono
    {X Y : SheafOfModules.{m} R} (f : X ⟶ Y) [Mono f] (U : C) :
    Function.Injective (f.val.app (Opposite.op U)) := by
  have hmono : Mono ((SheafOfModules.forget R).map f) := by infer_instance
  have hU : Mono ((PresheafOfModules.evaluation R.obj (Opposite.op U)).map
      ((SheafOfModules.forget R).map f)) := by infer_instance
  exact (ModuleCat.mono_iff_injective _).mp hU

/-- Sections of a commuting square of sheaves of modules commute. -/
private lemma sectionMap_comp_eq {D : Type u} [Category.{v} D]
    {R' : Sheaf (⊥ : GrothendieckTopology D) RingCat.{r}} {X Y Z W : SheafOfModules.{m} R'}
    {f : X ⟶ Y} {g : Y ⟶ W} {h : X ⟶ Z} {k : Z ⟶ W} (hfg : f ≫ g = h ≫ k)
    (V : Dᵒᵖ) (x : X.val.obj V) :
    g.val.app V (f.val.app V x) = k.val.app V (h.val.app V x) :=
  congrArg (fun φ : X ⟶ W => φ.val.app V x) hfg

/-- Sections of a composite of sheaf morphisms that equals `k` are given by applying `k`. -/
private lemma sectionMap_comp_eq_apply {D : Type u} [Category.{v} D]
    {R' : Sheaf (⊥ : GrothendieckTopology D) RingCat.{r}} {X Y W : SheafOfModules.{m} R'}
    {f : X ⟶ Y} {g : Y ⟶ W} {k : X ⟶ W} (hfg : f ≫ g = k) (V : Dᵒᵖ) (x : X.val.obj V) :
    g.val.app V (f.val.app V x) = k.val.app V x :=
  congrArg (fun φ : X ⟶ W => φ.val.app V x) hfg

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma sectionFamilySize_range_le
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    (A : ∀ (_i : ℤ) (_U : C), Type m)
    (g : ∀ (i : ℤ) (U : C), A i U → (F.X i).val.obj (Opposite.op U)) :
    sectionFamilySize (fun i U => Set.range (g i U)) ≤
      Cardinal.lift.{max v r} (Cardinal.mk (Σ i : ℤ, Σ U : C, A i U)) := by
  classical
  unfold sectionFamilySize
  apply Cardinal.lift_le.mpr
  apply Cardinal.mk_le_of_surjective (f := fun x : Σ i : ℤ, Σ U : C, A i U =>
    ⟨x.1, x.2.1, ⟨g x.1 x.2.1 x.2.2, ⟨x.2.2, rfl⟩⟩⟩)
  rintro ⟨i, U, x, ⟨a, rfl⟩⟩
  exact ⟨⟨i, U, a⟩, rfl⟩

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma sectionSigmaSize_le_of_component_injective
    {G : CochainComplex (SheafOfModules.{m} R) ℤ}
    (A : ∀ (_i : ℤ) (_U : C), Type m)
    (f : ∀ (i : ℤ) (U : C), A i U → (G.X i).val.obj (Opposite.op U))
    (hf : ∀ i U, Function.Injective (f i U)) :
    Cardinal.lift.{max v r} (Cardinal.mk (Σ i : ℤ, Σ U : C, A i U)) ≤
      complexSectionSize G := by
  let eA : ∀ i U, A i U ↪ (G.X i).val.obj (Opposite.op U) :=
    fun i U => ⟨f i U, hf i U⟩
  let e : (Σ i : ℤ, Σ U : C, A i U) ↪
      (Σ i : ℤ, Σ U : C, (G.X i).val.obj (Opposite.op U)) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl ℤ) fun i =>
      Function.Embedding.sigmaMap (Function.Embedding.refl C) fun U => eA i U
  exact Cardinal.lift_le.mpr (Cardinal.mk_le_of_injective e.injective)

private noncomputable def cycleRepresentativeCycle
    {F G : CochainComplex (SheafOfModules.{m} R) ℤ}
    (e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj G)
    (i : ℤ) (U : C) :
    (G.cycles i).val.obj (Opposite.op U) → (F.cycles i).val.obj (Opposite.op U) :=
  fun z => Classical.choose (epi_sections_surjective R (F.homologyπ i) U
      (((derivedIso_homologyIso R e i).inv.val.app (Opposite.op U))
        ((G.homologyπ i).val.app (Opposite.op U) z)))

private noncomputable def cycleRepresentative
    {F G : CochainComplex (SheafOfModules.{m} R) ℤ}
    (e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj G)
    (i : ℤ) (U : C) :
    (G.cycles i).val.obj (Opposite.op U) → (F.X i).val.obj (Opposite.op U) :=
  fun z => (F.iCycles i).val.app (Opposite.op U)
    (cycleRepresentativeCycle R e i U z)

private lemma cycleRepresentativeCycle_homologyπ
    {F G : CochainComplex (SheafOfModules.{m} R) ℤ}
    (e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj G)
    (i : ℤ) (U : C) (z : (G.cycles i).val.obj (Opposite.op U)) :
    (F.homologyπ i).val.app (Opposite.op U) (cycleRepresentativeCycle R e i U z) =
      ((derivedIso_homologyIso R e i).inv.val.app (Opposite.op U))
        ((G.homologyπ i).val.app (Opposite.op U) z) :=
  Classical.choose_spec (epi_sections_surjective R (F.homologyπ i) U
    (((derivedIso_homologyIso R e i).inv.val.app (Opposite.op U))
      ((G.homologyπ i).val.app (Opposite.op U) z)))

private lemma cycleRepresentativeFamily_size_le
    {F G : CochainComplex (SheafOfModules.{m} R) ℤ}
    (e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj G) :
    sectionFamilySize
      (fun i U => Set.range (cycleRepresentative R e i U)) ≤
      complexSectionSize G := by
  calc
    _ ≤ Cardinal.lift.{max v r}
        (Cardinal.mk (Σ i : ℤ, Σ U : C, (G.cycles i).val.obj (Opposite.op U))) :=
          sectionFamilySize_range_le R (fun i U =>
            (G.cycles i).val.obj (Opposite.op U)) (cycleRepresentative R e)
    _ ≤ complexSectionSize G :=
      sectionSigmaSize_le_of_component_injective R
        (fun i U => (G.cycles i).val.obj (Opposite.op U))
        (fun i U z => (G.iCycles i).val.app (Opposite.op U) z)
        fun i U => sectionMap_injective_of_mono R (G.iCycles i) U

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma sectionSigma_succ_sum_size_le
    {H : CochainComplex (SheafOfModules.{m} R) ℤ}
    {κ : Cardinal.{max u v m r}}
    (hκ : Cardinal.aleph0 ≤ κ) (hH : complexSectionSize H ≤ κ) :
    Cardinal.lift.{max v r}
      (Cardinal.mk (Σ i : ℤ, Σ U : C,
        (H.X i).val.obj (Opposite.op U) ⊕ (H.X (i + 1)).val.obj (Opposite.op U))) ≤ κ := by
  let A := Σ i : ℤ, Σ U : C, (H.X i).val.obj (Opposite.op U)
  let B := Σ i : ℤ, Σ U : C, (H.X (i + 1)).val.obj (Opposite.op U)
  let S := Σ i : ℤ, Σ U : C,
    (H.X i).val.obj (Opposite.op U) ⊕ (H.X (i + 1)).val.obj (Opposite.op U)
  let eShift : B ↪ A := Function.Embedding.sigmaMap
    ⟨fun i : ℤ => i + 1, add_left_injective 1⟩ fun i =>
      Function.Embedding.sigmaMap (Function.Embedding.refl C) fun U =>
        Function.Embedding.refl ((H.X (i + 1)).val.obj (Opposite.op U))
  let eSum : S ≃ A ⊕ B := {
    toFun := fun
      | ⟨i, U, Sum.inl x⟩ => Sum.inl ⟨i, U, x⟩
      | ⟨i, U, Sum.inr x⟩ => Sum.inr ⟨i, U, x⟩
    invFun := fun
      | Sum.inl ⟨i, U, x⟩ => ⟨i, U, Sum.inl x⟩
      | Sum.inr ⟨i, U, x⟩ => ⟨i, U, Sum.inr x⟩
    left_inv := by intro x; cases x with | mk i x => cases x with | mk U x => cases x <;> rfl
    right_inv := by intro x; cases x <;> rfl }
  have hA : Cardinal.lift.{max v r} (Cardinal.mk A) ≤ κ := by
    simpa [A, complexSectionSize] using hH
  have hB : Cardinal.lift.{max v r} (Cardinal.mk B) ≤ κ :=
    (Cardinal.lift_le.mpr (Cardinal.mk_le_of_injective eShift.injective)).trans hA
  calc
    Cardinal.lift.{max v r} (Cardinal.mk S) =
    Cardinal.lift.{max v r} (Cardinal.mk A) +
          Cardinal.lift.{max v r} (Cardinal.mk B) := by
      rw [Cardinal.mk_congr eSum, Cardinal.mk_sum]
      simp [Cardinal.lift_add]
    _ ≤ κ := (Cardinal.add_le_max _ _).trans
      (max_le (max_le hA hB) hκ)

private lemma exists_representative_of_derivedObjectSize
    (K : DerivedCategory (SheafOfModules.{m} R))
    (hK : ∃ F : CochainComplex (SheafOfModules.{m} R) ℤ,
      Nonempty (DerivedCategory.Q.obj F ≅ K)) :
    ∃ F : CochainComplex (SheafOfModules.{m} R) ℤ,
      Nonempty (DerivedCategory.Q.obj F ≅ K) ∧
        complexSectionSize F = derivedObjectSize R K := by
  classical
  obtain ⟨F, hF, hsize⟩ := csInf_mem (show
    {c : Cardinal.{max u v m r} | ∃ F : CochainComplex (SheafOfModules.{m} R) ℤ,
      Nonempty (DerivedCategory.Q.obj F ≅ K) ∧
        c = complexSectionSize F}.Nonempty from by
          obtain ⟨F, hF⟩ := hK
          exact ⟨_, F, hF, rfl⟩)
  exact ⟨F, hF, hsize.symm⟩

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma exists_bounded_subcomplex_containing_family
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Ω : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (Opposite.op U)))
    {μ : Cardinal.{max u v m r}}
    (hΩ : sectionFamilySize Ω ≤ μ) :
    ∃ (H : CochainComplex (SheafOfModules.{m} R) ℤ) (f : H ⟶ F),
        Mono f ∧
          (∀ (i : ℤ) (U : C) (x : (F.X i).val.obj (Opposite.op U)), x ∈ Ω i U →
            ∃ y : (H.X i).val.obj (Opposite.op U),
              (f.f i).val.app (Opposite.op U) y = x) ∧
          complexSectionSize H ≤ max κ₀ μ := by
  obtain ⟨H, f, hf, hcont, hsize⟩ := hbase F Ω
  exact ⟨H, f, hf, hcont, hsize.trans (max_le_max_left _ hΩ)⟩

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma factors_through_of_sectionwise
    {X Y Z : SheafOfModules.{m} R} (f : X ⟶ Z) (g : Y ⟶ Z) [Mono g]
    (h : ∀ (U : C) (x : (X.val.obj (Opposite.op U))),
      ∃ y : Y.val.obj (Opposite.op U), (g.val.app (Opposite.op U)) y =
        (f.val.app (Opposite.op U)) x) :
    ∃ q : X ⟶ Y, q ≫ g = f := by
  classical
  have h' : ∀ (U : Cᵒᵖ) (x : X.val.obj U),
      ∃ y : Y.val.obj U, (g.val.app U) y = (f.val.app U) x := by
    intro U x
    obtain ⟨U⟩ := U
    exact h U x
  have hgmono : Mono g.val := by
    change Mono ((SheafOfModules.forget R).map g)
    infer_instance
  have hinj (U : Cᵒᵖ) : Function.Injective (g.val.app U) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  let qval : X.val ⟶ Y.val :=
    { app := fun U =>
        ModuleCat.ofHom
          { toFun := fun x => Classical.choose (h' U x)
            map_add' := by
              intro x y
              apply hinj U
              calc
                _ = (f.val.app U) (x + y) := Classical.choose_spec (h' U (x + y))
                _ = (f.val.app U) x + (f.val.app U) y := map_add _ _ _
                _ = (g.val.app U) (Classical.choose (h' U x)) +
                    (g.val.app U) (Classical.choose (h' U y)) := by
                      rw [Classical.choose_spec (h' U x),
                        Classical.choose_spec (h' U y)]
                _ = (g.val.app U) (Classical.choose (h' U x) +
                    Classical.choose (h' U y)) := (map_add _ _ _).symm
            map_smul' := by
              intro a x
              apply hinj U
              calc
                _ = (f.val.app U) (a • x) := Classical.choose_spec (h' U (a • x))
                _ = a • (f.val.app U) x := map_smul _ _ _
                _ = a • (g.val.app U) (Classical.choose (h' U x)) := by
                      rw [Classical.choose_spec (h' U x)]
                _ = (g.val.app U) (a • Classical.choose (h' U x)) :=
                      (map_smul _ _ _).symm }
      naturality := by
        intro U V p
        apply ModuleCat.hom_ext
        ext x
        apply hinj V
        have e₁ := Classical.choose_spec (h' V ((X.val.map p) x))
        have e₂ := PresheafOfModules.naturality_apply f.val p x
        have e₃ : (Z.val.map p) ((f.val.app U) x) =
            (Z.val.map p) ((g.val.app U) (Classical.choose (h' U x))) :=
          congrArg (fun t => (Z.val.map p) t) (Classical.choose_spec (h' U x)).symm
        have e₄ :=
          (PresheafOfModules.naturality_apply g.val p (Classical.choose (h' U x))).symm
        exact e₁.trans (e₂.trans (e₃.trans e₄)) }
  refine ⟨⟨qval⟩, SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)⟩
  ext x
  exact Classical.choose_spec (h' U x)

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma factors_complex_through_of_sectionwise
    {H G F : CochainComplex (SheafOfModules.{m} R) ℤ}
    (f : H ⟶ F) (g : G ⟶ F) [Mono g]
    (h : ∀ (i : ℤ) (U : C) (x : (H.X i).val.obj (Opposite.op U)),
      ∃ y : (G.X i).val.obj (Opposite.op U),
        (g.f i).val.app (Opposite.op U) y = (f.f i).val.app (Opposite.op U) x) :
    ∃ q : H ⟶ G, q ≫ g = f := by
  classical
  choose q hq using fun i => factors_through_of_sectionwise R (f.f i) (g.f i) (h i)
  let q : H ⟶ G :=
    { f := q
      comm' i j _ := by
        rw [← cancel_mono (g.f j), Category.assoc, Category.assoc, ← g.comm,
          reassoc_of% (hq i), hq j, f.comm] }
  exact ⟨q, HomologicalComplex.hom_ext _ _ hq⟩

private noncomputable def enlargementGenerator
  {H F : CochainComplex (SheafOfModules.{m} R) ℤ}
    (f : H ⟶ F) (i : ℤ) (U : C) :
    (H.X i).val.obj (Opposite.op U) ⊕ (H.X (i + 1)).val.obj (Opposite.op U) →
      (F.X i).val.obj (Opposite.op U) := by
  classical
  intro x
  cases x with
  | inl x => exact (f.f i).val.app (Opposite.op U) x
  | inr x =>
      exact if h : ∃ y : (F.X i).val.obj (Opposite.op U),
          (F.d i (i + 1)).val.app (Opposite.op U) y =
            (f.f (i + 1)).val.app (Opposite.op U) x
        then Classical.choose h else 0

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma enlargementGeneratorFamily_size_le
    {H F : CochainComplex (SheafOfModules.{m} R) ℤ} (f : H ⟶ F)
    {κ : Cardinal.{max u v m r}} (hκ : Cardinal.aleph0 ≤ κ)
    (hH : complexSectionSize H ≤ κ) :
    sectionFamilySize (fun i U =>
      Set.range (enlargementGenerator R f i U)) ≤ κ := by
  calc
    _ ≤ Cardinal.lift.{max v r} (Cardinal.mk (Σ i : ℤ, Σ U : C,
        (H.X i).val.obj (Opposite.op U) ⊕ (H.X (i + 1)).val.obj (Opposite.op U))) :=
      sectionFamilySize_range_le R
        (fun i U => (H.X i).val.obj (Opposite.op U) ⊕
          (H.X (i + 1)).val.obj (Opposite.op U)) (enlargementGenerator R f)
    _ ≤ κ := sectionSigma_succ_sum_size_le R hκ hH

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma exists_bounded_enlargement_with_boundary_preimages
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    {H : CochainComplex (SheafOfModules.{m} R) ℤ} (f : H ⟶ F) [Mono f]
    {κ : Cardinal.{max u v m r}} (hκ : Cardinal.aleph0 ≤ κ)
    (hH : complexSectionSize H ≤ κ) :
    ∃ (G : CochainComplex (SheafOfModules.{m} R) ℤ) (g : G ⟶ F),
        Mono g ∧ (∃ q : H ⟶ G, q ≫ g = f) ∧
        (∀ (i : ℤ) (U : C) (x : (H.X (i + 1)).val.obj (Opposite.op U)),
          ∀ (y : (F.X i).val.obj (Opposite.op U))
            (hy : (F.d i (i + 1)).val.app (Opposite.op U) y =
              (f.f (i + 1)).val.app (Opposite.op U) x),
          ∃ z : (G.X i).val.obj (Opposite.op U),
            (g.f i).val.app (Opposite.op U) z =
              Classical.choose (⟨y, hy⟩ : ∃ y' : (F.X i).val.obj (Opposite.op U),
                (F.d i (i + 1)).val.app (Opposite.op U) y' =
                  (f.f (i + 1)).val.app (Opposite.op U) x)) ∧
        complexSectionSize G ≤ max κ₀ κ := by
  let Ω : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (Opposite.op U)) :=
    fun i U => Set.range (enlargementGenerator R f i U)
  have hΩ : sectionFamilySize Ω ≤ κ := enlargementGeneratorFamily_size_le R f hκ hH
  obtain ⟨G, g, hg, hcont, hsize⟩ :=
    exists_bounded_subcomplex_containing_family R κ₀ hbase F Ω hΩ
  have hfactor : ∀ (i : ℤ) (U : C) (x : (H.X i).val.obj (Opposite.op U)),
      ∃ z : (G.X i).val.obj (Opposite.op U),
        (g.f i).val.app (Opposite.op U) z = (f.f i).val.app (Opposite.op U) x :=
    fun i U x => hcont i U _ ⟨Sum.inl x, rfl⟩
  obtain ⟨q, hq⟩ := factors_complex_through_of_sectionwise R f g hfactor
  refine ⟨G, g, hg, ⟨q, hq⟩, ?_, hsize⟩
  intro i U x y hy
  have hpre : ∃ y' : (F.X i).val.obj (Opposite.op U),
      (F.d i (i + 1)).val.app (Opposite.op U) y' =
        (f.f (i + 1)).val.app (Opposite.op U) x := ⟨y, hy⟩
  obtain ⟨z, hz⟩ := hcont i U _ ⟨Sum.inr x, rfl⟩
  exact ⟨z, by simpa [enlargementGenerator, hpre] using hz⟩

private structure SmallStage
    (F : CochainComplex (SheafOfModules.{m} R) ℤ)
    (Λ : Cardinal.{max u v m r}) where
  H : CochainComplex (SheafOfModules.{m} R) ℤ
  inc : H ⟶ F
  mono_inc : Mono inc
  size_le : complexSectionSize H ≤ Λ

private structure SmallStageExtension
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (S : SmallStage R F Λ) where
  next : SmallStage R F Λ
  inclusion : S.H ⟶ next.H
  factor : inclusion ≫ next.inc = S.inc
  boundary_preimage : ∀ (i : ℤ) (U : C)
    (x : (S.H.X (i + 1)).val.obj (Opposite.op U))
    (y : (F.X i).val.obj (Opposite.op U))
    (hy : (F.d i (i + 1)).val.app (Opposite.op U) y =
      (S.inc.f (i + 1)).val.app (Opposite.op U) x),
    ∃ z : (next.H.X i).val.obj (Opposite.op U),
      (next.inc.f i).val.app (Opposite.op U) z =
        Classical.choose (⟨y, hy⟩ : ∃ y' : (F.X i).val.obj (Opposite.op U),
          (F.d i (i + 1)).val.app (Opposite.op U) y' =
            (S.inc.f (i + 1)).val.app (Opposite.op U) x)

private noncomputable def extendSmallStage
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S : SmallStage R F Λ) :
    SmallStageExtension R S := by
  classical
  letI : Mono S.inc := S.mono_inc
  let hstep :=
    exists_bounded_enlargement_with_boundary_preimages R κ₀ hbase F S.inc
      hℵ₀ S.size_le
  let G := Classical.choose hstep
  have hG := Classical.choose_spec hstep
  let g := Classical.choose hG
  have hg_rest := Classical.choose_spec hG
  have hg : Mono g := hg_rest.1
  let hrest := hg_rest.2
  let q := Classical.choose hrest.1
  have hq := Classical.choose_spec hrest.1
  have hboundary := hrest.2.1
  have hsize := hrest.2.2
  refine ⟨⟨G, g, hg, ?_⟩, q, hq, hboundary⟩
  exact hsize.trans (max_le hκ₀ le_rfl)

private noncomputable def rangePresheafSubmodule
    {X Y : PresheafOfModules.{m} R.obj} (f : X ⟶ Y) : Y.Submodule where
  obj U := LinearMap.range (f.app U).hom
  map := by
    intro U V p
    rintro x ⟨y, rfl⟩
    exact ⟨X.map p y, PresheafOfModules.naturality_apply f p y⟩

private noncomputable def smallStageSequence
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) :
    ℕ → SmallStage R F Λ
  | 0 => S₀
  | n + 1 => (extendSmallStage R κ₀ hbase hκ₀ hℵ₀
      (smallStageSequence κ₀ hbase hκ₀ hℵ₀ S₀ n)).next

private noncomputable def smallStageSequenceMap
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) (n : ℕ) :
    (smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n).H ⟶
      (smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ (n + 1)).H := by
  simpa [smallStageSequence] using (extendSmallStage R κ₀ hbase hκ₀ hℵ₀
    (smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n)).inclusion

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma smallStageSequenceMap_factor
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) (n : ℕ) :
    smallStageSequenceMap R κ₀ hbase hκ₀ hℵ₀ S₀ n ≫
      (smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ (n + 1)).inc =
        (smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n).inc := by
  simpa [smallStageSequence, smallStageSequenceMap] using
    (extendSmallStage R κ₀ hbase hκ₀ hℵ₀
      (smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n)).factor

private noncomputable def stageRangeSubmodule
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (S : SmallStage R F Λ) (i : ℤ) :
    (F.X i).val.Submodule := rangePresheafSubmodule R (S.inc.f i).val

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma stageRange_le_next
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) (n : ℕ) (i : ℤ) :
    stageRangeSubmodule R (smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n) i ≤
      stageRangeSubmodule R (smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ (n + 1)) i := by
  let S := smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n
  let T := smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ (n + 1)
  let q := smallStageSequenceMap R κ₀ hbase hκ₀ hℵ₀ S₀ n
  have hfac := smallStageSequenceMap_factor R κ₀ hbase hκ₀ hℵ₀ S₀ n
  intro U x hx
  rcases hx with ⟨y, rfl⟩
  refine ⟨(q.f i).val.app U y, ?_⟩
  have hcomp := congrArg (fun η : S.H ⟶ F =>
    ((η.f i).val.app U) y) hfac
  simpa [S, T, q] using hcomp

private noncomputable def stageRangeSequence
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) (i : ℤ) :
    ℕ → (F.X i).val.Submodule :=
  fun n => stageRangeSubmodule R
    (smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n) i

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma stageRangeSequence_monotone
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) (i : ℤ) :
    Monotone (stageRangeSequence R κ₀ hbase hκ₀ hℵ₀ S₀ i) :=
  monotone_nat_of_le_succ fun n => stageRange_le_next R κ₀ hbase hκ₀ hℵ₀ S₀ n i

/-- An element of the supremum of a monotone sequence of subpresheaves lies in one of them. -/
private lemma exists_mem_of_mem_iSup_obj {D : Type u} [Category.{v} D]
    {R' : Dᵒᵖ ⥤ RingCat.{r}} {M : PresheafOfModules.{m} R'}
    {P : ℕ → M.Submodule} (hP : Monotone P) {U : Dᵒᵖ} {x : M.obj U}
    (hx : x ∈ ⨆ n, (P n).obj U) : ∃ n, x ∈ (P n).obj U :=
  (Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun _ _ hab => hP hab U)).mp hx

private noncomputable def stageUnionSubmodule
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) (i : ℤ) :
    (F.X i).val.Submodule := by
  classical
  let P := stageRangeSequence R κ₀ hbase hκ₀ hℵ₀ S₀ i
  refine { obj := fun U => ⨆ n, (P n).obj U, map := ?_ }
  intro U V p x hx
  obtain ⟨n, hx⟩ := exists_mem_of_mem_iSup_obj
    (stageRangeSequence_monotone R κ₀ hbase hκ₀ hℵ₀ S₀ i) hx
  apply Submodule.mem_iSup_of_mem n
  exact (P n).map p hx

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma stageUnionSubmodule_differential_mem
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ)
    (i j : ℤ) (U : Cᵒᵖ) (x : (F.X i).val.obj U)
    (hx : x ∈ (stageUnionSubmodule R κ₀ hbase hκ₀ hℵ₀ S₀ i).obj U) :
    (F.d i j).val.app U x ∈ (stageUnionSubmodule R κ₀ hbase hκ₀ hℵ₀ S₀ j).obj U := by
  let P := stageRangeSequence R κ₀ hbase hκ₀ hℵ₀ S₀ i
  obtain ⟨n, y, rfl⟩ := exists_mem_of_mem_iSup_obj
    (stageRangeSequence_monotone R κ₀ hbase hκ₀ hℵ₀ S₀ i) (P := P) hx
  let S := smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n
  by_cases hij : (ComplexShape.up ℤ).Rel i j
  · exact Submodule.mem_iSup_of_mem n ⟨(S.H.d i j).val.app U y,
      (congrArg (fun k : S.H.X i ⟶ F.X j => (k.val.app U) y) (S.inc.comm i j)).symm⟩
  · rw [F.shape i j hij]
    exact Submodule.zero_mem _

private noncomputable def stageUnionSheafTerm
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) (i : ℤ) :
    SheafOfModules.{m} R := by
  let P := stageUnionSubmodule R κ₀ hbase hκ₀ hℵ₀ S₀ i
  exact ⟨P.toPresheafOfModules, Presheaf.isSheaf_bot _⟩

private noncomputable def stageUnionTermInclusion
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) (i : ℤ) :
    stageUnionSheafTerm R κ₀ hbase hκ₀ hℵ₀ S₀ i ⟶ F.X i := by
  let P := stageUnionSubmodule R κ₀ hbase hκ₀ hℵ₀ S₀ i
  exact ⟨P.ι⟩

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma stageUnionTermInclusion_mono
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) (i : ℤ) :
    Mono (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ i) := by
  apply (SheafOfModules.forget R).mono_of_mono_map
  change Mono ((stageUnionSubmodule R κ₀ hbase hκ₀ hℵ₀ S₀ i).ι)
  infer_instance

private noncomputable def stageUnionDifferential
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) (i j : ℤ) :
    stageUnionSheafTerm R κ₀ hbase hκ₀ hℵ₀ S₀ i ⟶
      stageUnionSheafTerm R κ₀ hbase hκ₀ hℵ₀ S₀ j := by
  classical
  letI : Mono (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ j) :=
    stageUnionTermInclusion_mono R κ₀ hbase hκ₀ hℵ₀ S₀ j
  exact Classical.choose (factors_through_of_sectionwise R
    (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ i ≫ F.d i j)
    (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ j)
    (by
      intro U x
      refine ⟨⟨(F.d i j).val.app (Opposite.op U) x.val,
        stageUnionSubmodule_differential_mem R κ₀ hbase hκ₀ hℵ₀ S₀ i j
          (Opposite.op U) x.val x.property⟩,
        ?_⟩
      rfl))

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma stageUnionDifferential_factor
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) (i j : ℤ) :
    stageUnionDifferential R κ₀ hbase hκ₀ hℵ₀ S₀ i j ≫
      stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ j =
        stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ i ≫ F.d i j := by
  let : Mono (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ j) :=
    stageUnionTermInclusion_mono R κ₀ hbase hκ₀ hℵ₀ S₀ j
  exact Classical.choose_spec (factors_through_of_sectionwise R
    (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ i ≫ F.d i j)
    (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ j)
    (by
      intro U x
      refine ⟨⟨(F.d i j).val.app (Opposite.op U) x.val,
        stageUnionSubmodule_differential_mem R κ₀ hbase hκ₀ hℵ₀ S₀ i j
          (Opposite.op U) x.val x.property⟩,
        ?_⟩
      rfl))

private noncomputable def stageUnionComplex
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) :
    CochainComplex (SheafOfModules.{m} R) ℤ where
  X i := stageUnionSheafTerm R κ₀ hbase hκ₀ hℵ₀ S₀ i
  d i j := stageUnionDifferential R κ₀ hbase hκ₀ hℵ₀ S₀ i j
  shape i j hij := by
    let : Mono (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ j) :=
      stageUnionTermInclusion_mono R κ₀ hbase hκ₀ hℵ₀ S₀ j
    apply (cancel_mono (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ j)).mp
    rw [stageUnionDifferential_factor, F.shape i j hij]
    simp
  d_comp_d' i j k _ _ := by
    let : Mono (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ k) :=
      stageUnionTermInclusion_mono R κ₀ hbase hκ₀ hℵ₀ S₀ k
    apply (cancel_mono (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ k)).mp
    rw [Category.assoc, stageUnionDifferential_factor,
      reassoc_of% stageUnionDifferential_factor, F.d_comp_d]
    simp

private noncomputable def stageUnionComplexInclusion
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) :
    stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀ ⟶ F where
  f i := stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ i
  comm' i j _ := (stageUnionDifferential_factor R κ₀ hbase hκ₀ hℵ₀ S₀ i j).symm

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma stageUnionComplexInclusion_mono
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) :
    Mono (stageUnionComplexInclusion R κ₀ hbase hκ₀ hℵ₀ S₀) :=
  HomologicalComplex.mono_of_mono_f _ (stageUnionTermInclusion_mono R κ₀ hbase hκ₀ hℵ₀ S₀)

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma stageUnionComplex_size_le
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ) :
    complexSectionSize (stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀) ≤ Λ := by
  let A (n : ℕ) := Σ i : ℤ, Σ U : C,
    ((smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n).H.X i).val.obj (Opposite.op U)
  let B := Σ i : ℤ, Σ U : C,
    ((stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀).X i).val.obj (Opposite.op U)
  let e : (Σ n : ℕ, A n) → B := fun ⟨n, i, U, y⟩ =>
    ⟨i, U, ⟨((smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n).inc.f i).val.app
      (Opposite.op U) y, by
        apply Submodule.mem_iSup_of_mem n
        exact ⟨y, rfl⟩⟩⟩
  have he : Function.Surjective e := by
    rintro ⟨i, U, x⟩
    obtain ⟨n, y, hy⟩ := exists_mem_of_mem_iSup_obj
      (stageRangeSequence_monotone R κ₀ hbase hκ₀ hℵ₀ S₀ i) x.property
    exact ⟨⟨n, i, U, y⟩, Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Subtype.ext hy))))⟩
  let f : ℕ → Cardinal.{max u v m r} := fun n =>
    Cardinal.lift.{max v r} (Cardinal.mk (A n))
  have hA (n : ℕ) : f n ≤ Λ := by
    simpa [f, A, complexSectionSize] using
      (smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n).size_le
  have hsum : Cardinal.sum f ≤ Λ := by
    have hsup : (⨆ n : ℕ, f n : Cardinal.{max u v m r}) ≤ Λ := ciSup_le' hA
    calc
      _ ≤ Cardinal.lift.{max u v m r, 0} (Cardinal.mk ℕ) * (⨆ n, f n) :=
        Cardinal.sum_le_lift_mk_mul_iSup f
      _ = Cardinal.aleph0 * (⨆ n, f n) := by
        simp [Cardinal.lift_aleph0]
      _ ≤ Cardinal.aleph0 * Λ := mul_le_mul_right hsup Cardinal.aleph0
      _ ≤ Λ := Cardinal.mul_le_of_le hℵ₀ hℵ₀ le_rfl
  unfold complexSectionSize
  change Cardinal.lift.{max v r} (Cardinal.mk B) ≤ Λ
  calc
    _ ≤ Cardinal.lift.{max v r} (Cardinal.mk (Σ n : ℕ, A n)) :=
      Cardinal.lift_le.mpr (Cardinal.mk_le_of_surjective he)
    _ = Cardinal.sum f := by
      rw [Cardinal.mk_sigma, Cardinal.lift_sum]
    _ ≤ Λ := hsum

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma stageUnion_contains_initial
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ)
    (i : ℤ) (U : C) (x : (S₀.H.X i).val.obj (Opposite.op U)) :
    ∃ y : (stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀).X i |>.val.obj (Opposite.op U),
      (stageUnionTermInclusion R κ₀ hbase hκ₀ hℵ₀ S₀ i).val.app (Opposite.op U) y =
        (S₀.inc.f i).val.app (Opposite.op U) x := by
  refine ⟨⟨(S₀.inc.f i).val.app (Opposite.op U) x, ?_⟩, rfl⟩
  change (S₀.inc.f i).val.app (Opposite.op U) x ∈ ⨆ n,
    (stageRangeSequence R κ₀ hbase hκ₀ hℵ₀ S₀ i n).obj (Opposite.op U)
  exact Submodule.mem_iSup_of_mem 0 ⟨x, rfl⟩

private lemma exists_initial_smallStage
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F G : CochainComplex (SheafOfModules.{m} R) ℤ}
    (e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj G)
    (Λ : Cardinal.{max u v m r}) (hκ₀ : κ₀ ≤ Λ)
    (hδ : complexSectionSize G ≤ Λ) :
    ∃ (H : CochainComplex (SheafOfModules.{m} R) ℤ) (f : H ⟶ F),
      Mono f ∧ complexSectionSize H ≤ Λ ∧
      (∀ (i : ℤ) (U : C) (z : (G.cycles i).val.obj (Opposite.op U)),
        ∃ y : (H.X i).val.obj (Opposite.op U),
          (f.f i).val.app (Opposite.op U) y = cycleRepresentative R e i U z) := by
  let Ω : ∀ (i : ℤ) (U : C), Set ((F.X i).val.obj (Opposite.op U)) :=
    fun i U => Set.range (cycleRepresentative R e i U)
  have hΩ : sectionFamilySize Ω ≤ Λ :=
    (cycleRepresentativeFamily_size_le R e).trans hδ
  obtain ⟨H, f, hf, hcont, hsize⟩ :=
    exists_bounded_subcomplex_containing_family R κ₀ hbase F Ω hΩ
  exact ⟨H, f, hf, hsize.trans (max_le hκ₀ le_rfl), fun i U z => hcont i U _ ⟨z, rfl⟩⟩

omit [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma homologyCycle_zero_iff_boundary
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    (i : ℤ) (U : Cᵒᵖ) (z : (F.cycles i).val.obj U)
    (hz : (F.homologyπ i).val.app U z = 0) :
    ∃ y : (F.X (i - 1)).val.obj U,
      (F.toCycles (i - 1) i).val.app U y = z := by
  let E₁ : SheafOfModules.{m} R ⥤ PresheafOfModules.{m} R.obj :=
    SheafOfModules.forget R
  let E₂ : PresheafOfModules.{m} R.obj ⥤ ModuleCat.{m} ((R.obj).obj U) :=
    PresheafOfModules.evaluation R.obj U
  let T : ShortComplex (SheafOfModules.{m} R) :=
    ShortComplex.mk (F.toCycles (i - 1) i) (F.homologyπ i) (by simp)
  have hT : T.Exact := T.exact_of_g_is_cokernel (F.homologyIsCokernel (i - 1) i (by simp))
  let : E₁.IsEquivalence := (chaoticSheafPresheafEquivalence R).isEquivalence_functor
  let : E₁.IsLeftAdjoint := (chaoticSheafPresheafEquivalence R).isLeftAdjoint_functor
  have hpres₁ : Limits.PreservesColimit (Limits.parallelPair T.f 0) E₁ := by
    dsimp [E₁]
    infer_instance
  have hT₁ : (T.map E₁).Exact := hT.map_of_epi_of_preservesCokernel E₁ (by infer_instance) hpres₁
  have hEpi₁ : Epi (T.map E₁).g := by
    dsimp [E₁]
    infer_instance
  let := hEpi₁
  have hpres₂ : Limits.PreservesColimit
      (Limits.parallelPair (E₁.map T.f) 0) E₂ := by
    dsimp [E₂]
    infer_instance
  have hmap : ((T.map E₁).map E₂).Exact :=
    hT₁.map_of_epi_of_preservesCokernel E₂ (by infer_instance) hpres₂
  have hzero : (E₂.map (E₁.map (F.homologyπ i))).hom z = 0 := hz
  have hex : Function.Exact (((T.map E₁).map E₂).f).hom
      (((T.map E₁).map E₂).g).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hmap
  have hmem : z ∈ Set.range ⇑(((T.map E₁).map E₂).f) :=
    (hex z).mp (by simpa using hzero)
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy⟩

omit [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma exists_cycleOfTerm
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    (i : ℤ) (U : Cᵒᵖ) (x : (F.X i).val.obj U)
    (hx : (F.d i (i + 1)).val.app U x = 0) :
    ∃ z : (F.cycles i).val.obj U,
      (F.iCycles i).val.app U z = x := by
  let E₁ : SheafOfModules.{m} R ⥤ PresheafOfModules.{m} R.obj :=
    SheafOfModules.forget R
  let E₂ : PresheafOfModules.{m} R.obj ⥤ ModuleCat.{m} ((R.obj).obj U) :=
    PresheafOfModules.evaluation R.obj U
  let A : Type r := ↑((R.obj).obj U)
  let E₃ : ModuleCat.{m} A ⥤ ModuleCat.{max m r} A :=
    ModuleCat.uliftFunctor.{r, m} A
  let E := E₁ ⋙ E₂ ⋙ E₃
  let : E₁.IsEquivalence := (chaoticSheafPresheafEquivalence R).isEquivalence_functor
  let : E₁.IsLeftAdjoint := (chaoticSheafPresheafEquivalence R).isLeftAdjoint_functor
  let k : ModuleCat.of.{max m r, r} A (ULift.{m} A) ⟶ E.obj (F.X i) :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton A (E.obj (F.X i)) (ULift.up x)).comp
      (ULift.moduleEquiv.{r, r, m} (R := A) (M := A)).toLinearMap)
  have hk : k ≫ E.map (F.d i (i + 1)) = 0 := by
    ext a
    rcases a with ⟨a⟩
    change ULift.up ((F.d i (i + 1)).val.app U (a • x)) = 0
    rw [map_smul, hx, smul_zero]
    rfl
  let kcycle : CategoryTheory.Limits.KernelFork (F.d i (i + 1)) :=
    CategoryTheory.Limits.KernelFork.ofι (F.iCycles i) (F.iCycles_d i (i + 1))
  have hker : CategoryTheory.Limits.IsLimit kcycle :=
    F.cyclesIsKernel i (j := i + 1) (by simp)
  have hK : CategoryTheory.Limits.IsLimit (E.mapCone kcycle) :=
    CategoryTheory.Limits.isLimitOfPreserves E hker
  have hK' : CategoryTheory.Limits.IsLimit
      (CategoryTheory.Limits.KernelFork.ofι (E.map (F.iCycles i))
        (by
          change E.map (kcycle.ι) ≫ E.map (F.d i (i + 1)) = 0
          rw [← E.map_comp, kcycle.condition, E.map_zero])) :=
    (kcycle.isLimitMapConeEquiv E) hK
  obtain ⟨l, hl⟩ := CategoryTheory.Limits.KernelFork.IsLimit.lift' hK' k hk
  refine ⟨(l.hom 1).down, (congrArg (fun f => ULift.down (f.hom 1)) hl).trans ?_⟩
  change ULift.down ((LinearMap.toSpanSingleton A (E.obj (F.X i)) (ULift.up x)) (1 : A)) = x
  exact congrArg ULift.down
    (LinearMap.toSpanSingleton_apply_one A (E.obj (F.X i)) (ULift.up x))

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma stageUnion_boundaryTerm_preimage
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ)
    (i : ℤ) (V : C)
    (x : (((stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀).X (i + 1)).val.obj
      (Opposite.op V)))
    (y : (F.X i).val.obj (Opposite.op V))
    (hy : (F.d i (i + 1)).val.app (Opposite.op V) y = x.val) :
    ∃ z : ((stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀).X i).val.obj
        (Opposite.op V),
      ((stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀).d i (i + 1)).val.app
        (Opposite.op V) z = x := by
  classical
  let U := stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀
  let P : ℕ → (F.X (i + 1)).val.Submodule :=
    stageRangeSequence R κ₀ hbase hκ₀ hℵ₀ S₀ (i + 1)
  obtain ⟨n, a, ha⟩ := exists_mem_of_mem_iSup_obj
    (stageRangeSequence_monotone R κ₀ hbase hκ₀ hℵ₀ S₀ (i + 1)) x.property
  let S := smallStageSequence R κ₀ hbase hκ₀ hℵ₀ S₀ n
  let E := extendSmallStage R κ₀ hbase hκ₀ hℵ₀ S
  have hyS : (F.d i (i + 1)).val.app (Opposite.op V) y =
      (S.inc.f (i + 1)).val.app (Opposite.op V) a := by
    calc
      _ = x.val := hy
      _ = (S.inc.f (i + 1)).val.app (Opposite.op V) a := by
        simpa [S, P, stageRangeSequence, stageRangeSubmodule, rangePresheafSubmodule] using ha.symm
  obtain ⟨z, hz⟩ := E.boundary_preimage i V a y hyS
  let T := E.next
  let zU : (U.X i).val.obj (Opposite.op V) :=
    ⟨(T.inc.f i).val.app (Opposite.op V) z, by
      apply Submodule.mem_iSup_of_mem (n + 1)
      exact ⟨z, rfl⟩⟩
  have hchosen : (F.d i (i + 1)).val.app (Opposite.op V)
      (Classical.choose (⟨y, hyS⟩ : ∃ y' : (F.X i).val.obj (Opposite.op V),
        (F.d i (i + 1)).val.app (Opposite.op V) y' =
          (S.inc.f (i + 1)).val.app (Opposite.op V) a)) =
      (S.inc.f (i + 1)).val.app (Opposite.op V) a :=
    Classical.choose_spec (⟨y, hyS⟩ : ∃ y' : (F.X i).val.obj (Opposite.op V),
      (F.d i (i + 1)).val.app (Opposite.op V) y' =
        (S.inc.f (i + 1)).val.app (Opposite.op V) a)
  let q := stageUnionComplexInclusion R κ₀ hbase hκ₀ hℵ₀ S₀
  have hqz : (q.f i).val.app (Opposite.op V) zU =
      Classical.choose (⟨y, hyS⟩ : ∃ y' : (F.X i).val.obj (Opposite.op V),
        (F.d i (i + 1)).val.app (Opposite.op V) y' =
          (S.inc.f (i + 1)).val.app (Opposite.op V) a) := hz
  have hcomm := sectionMap_comp_eq (q.comm i (i + 1)) (Opposite.op V) zU
  have hval : (q.f (i + 1)).val.app (Opposite.op V)
      ((U.d i (i + 1)).val.app (Opposite.op V) zU) =
      (q.f (i + 1)).val.app (Opposite.op V) x := by
    calc
      _ = (F.d i (i + 1)).val.app (Opposite.op V)
          ((q.f i).val.app (Opposite.op V) zU) := hcomm.symm
      _ = (S.inc.f (i + 1)).val.app (Opposite.op V) a := by rw [hqz, hchosen]
      _ = x.val := by simpa [S, P, stageRangeSequence, stageRangeSubmodule,
        rangePresheafSubmodule] using ha
      _ = (q.f (i + 1)).val.app (Opposite.op V) x := by rfl
  let : Mono q := stageUnionComplexInclusion_mono R κ₀ hbase hκ₀ hℵ₀ S₀
  exact ⟨zU, sectionMap_injective_of_mono R (q.f (i + 1)) V hval⟩

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma stageUnion_boundaryTerm_preimage_at
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F : CochainComplex (SheafOfModules.{m} R) ℤ}
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ)
    (j k : ℤ) (hjk : k = j + 1) (V : C)
    (x : ((stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀).X k).val.obj (Opposite.op V))
    (y : (F.X j).val.obj (Opposite.op V))
    (hy : (F.d j k).val.app (Opposite.op V) y = x.val) :
    ∃ z : ((stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀).X j).val.obj (Opposite.op V),
      ((stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀).d j k).val.app
        (Opposite.op V) z = x := by
  subst k
  exact stageUnion_boundaryTerm_preimage R κ₀ hbase hκ₀ hℵ₀ S₀ j V x y hy

private lemma homologyMap_section_surjective_of_cycleCover
    {F G U : CochainComplex (SheafOfModules.{m} R) ℤ}
    (e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj G)
    (q : U ⟶ F) [Mono q]
    (hcover : ∀ (i : ℤ) (V : C) (z : (G.cycles i).val.obj (Opposite.op V)),
      ∃ y : (U.X i).val.obj (Opposite.op V),
        (q.f i).val.app (Opposite.op V) y = cycleRepresentative R e i V z)
    (i : ℤ) (V : C) :
    Function.Surjective ((HomologicalComplex.homologyMap q i).val.app (Opposite.op V)) := by
  classical
  let η := derivedIso_homologyIso R e i
  intro a
  let b := (η.hom.val.app (Opposite.op V)) a
  obtain ⟨z, hz⟩ := epi_sections_surjective R (G.homologyπ i) V b
  let zF := cycleRepresentativeCycle R e i V z
  obtain ⟨y, hy⟩ := hcover i V z
  have hcycleF : (F.d i (i + 1)).val.app (Opposite.op V)
      ((F.iCycles i).val.app (Opposite.op V) zF) = 0 :=
    congrArg (fun f : F.cycles i ⟶ F.X (i + 1) => (f.val.app (Opposite.op V)) zF)
      (F.iCycles_d i (i + 1))
  have hcomm := sectionMap_comp_eq (q.comm i (i + 1)) (Opposite.op V) y
  have hycycle : (U.d i (i + 1)).val.app (Opposite.op V) y = 0 := by
    apply sectionMap_injective_of_mono R (q.f (i + 1)) V
    calc
      (q.f (i + 1)).val.app (Opposite.op V)
          ((U.d i (i + 1)).val.app (Opposite.op V) y) =
        (F.d i (i + 1)).val.app (Opposite.op V) ((q.f i).val.app (Opposite.op V) y) :=
          hcomm.symm
      _ = 0 := by rw [hy]; exact hcycleF
      _ = (q.f (i + 1)).val.app (Opposite.op V) 0 := by simp
  obtain ⟨zU, hzU⟩ := exists_cycleOfTerm R i (Opposite.op V) y hycycle
  have hcycles : (HomologicalComplex.cyclesMap q i).val.app (Opposite.op V) zU = zF := by
    apply sectionMap_injective_of_mono R (F.iCycles i) V
    calc
      (F.iCycles i).val.app (Opposite.op V)
          ((HomologicalComplex.cyclesMap q i).val.app (Opposite.op V) zU) =
        (q.f i).val.app (Opposite.op V)
          ((U.iCycles i).val.app (Opposite.op V) zU) :=
            sectionMap_comp_eq (HomologicalComplex.cyclesMap_i q i) (Opposite.op V) zU
      _ = (q.f i).val.app (Opposite.op V) y := by rw [hzU]
      _ = cycleRepresentative R e i V z := hy
      _ = (F.iCycles i).val.app (Opposite.op V) zF := rfl
  refine ⟨(U.homologyπ i).val.app (Opposite.op V) zU, ?_⟩
  calc
    (HomologicalComplex.homologyMap q i).val.app (Opposite.op V)
        ((U.homologyπ i).val.app (Opposite.op V) zU) =
      (F.homologyπ i).val.app (Opposite.op V)
        ((HomologicalComplex.cyclesMap q i).val.app (Opposite.op V) zU) :=
          sectionMap_comp_eq (HomologicalComplex.homologyπ_naturality q i) (Opposite.op V) zU
    _ = (F.homologyπ i).val.app (Opposite.op V) zF := by rw [hcycles]
    _ = (η.inv.val.app (Opposite.op V)) ((G.homologyπ i).val.app (Opposite.op V) z) :=
      cycleRepresentativeCycle_homologyπ R e i V z
    _ = a := by
      rw [hz]
      exact congrArg (fun f => (f.val.app (Opposite.op V)) a) η.hom_inv_id

omit [HasDerivedCategory (SheafOfModules.{m} R)] in
private lemma homologyMap_section_injective_of_boundaryPreimage
    {F U : CochainComplex (SheafOfModules.{m} R) ℤ}
    (q : U ⟶ F) [Mono q]
    (hpre : ∀ (i : ℤ) (V : C) (x : (U.X i).val.obj (Opposite.op V))
      (y : (F.X (i - 1)).val.obj (Opposite.op V)),
      (F.d (i - 1) i).val.app (Opposite.op V) y =
        (q.f i).val.app (Opposite.op V) x →
      ∃ z : (U.X (i - 1)).val.obj (Opposite.op V),
        (U.d (i - 1) i).val.app (Opposite.op V) z = x)
    (i : ℤ) (V : C) :
    Function.Injective ((HomologicalComplex.homologyMap q i).val.app (Opposite.op V)) := by
  classical
  intro a b hab
  obtain ⟨z₁, hz₁⟩ := epi_sections_surjective R (U.homologyπ i) V a
  obtain ⟨z₂, hz₂⟩ := epi_sections_surjective R (U.homologyπ i) V b
  have hnat (z : (U.cycles i).val.obj (Opposite.op V)) :=
    sectionMap_comp_eq (HomologicalComplex.homologyπ_naturality q i) (Opposite.op V) z
  have hclass : (F.homologyπ i).val.app (Opposite.op V)
        ((HomologicalComplex.cyclesMap q i).val.app (Opposite.op V) z₁) =
      (F.homologyπ i).val.app (Opposite.op V)
        ((HomologicalComplex.cyclesMap q i).val.app (Opposite.op V) z₂) := by
    rw [← hnat, ← hnat, hz₁, hz₂, hab]
  let c := (HomologicalComplex.cyclesMap q i).val.app (Opposite.op V) z₁ -
    (HomologicalComplex.cyclesMap q i).val.app (Opposite.op V) z₂
  have hzero : (F.homologyπ i).val.app (Opposite.op V) c = 0 := by
    rw [map_sub, hclass, sub_self]
  obtain ⟨y, hy⟩ := homologyCycle_zero_iff_boundary R i (Opposite.op V) c hzero
  let x := (U.iCycles i).val.app (Opposite.op V) (z₁ - z₂)
  have hboundary : (F.d (i - 1) i).val.app (Opposite.op V) y =
      (q.f i).val.app (Opposite.op V) x := by
    have hq : (F.iCycles i).val.app (Opposite.op V) c =
        (q.f i).val.app (Opposite.op V) x := by
      have hmap := sectionMap_comp_eq (HomologicalComplex.cyclesMap_i q i) (Opposite.op V)
        (z₁ - z₂)
      simpa only [map_sub, c, x] using hmap
    calc
      (F.d (i - 1) i).val.app (Opposite.op V) y =
          (F.iCycles i).val.app (Opposite.op V)
            ((F.toCycles (i - 1) i).val.app (Opposite.op V) y) := by
              exact (sectionMap_comp_eq_apply (F.toCycles_i (i - 1) i) (Opposite.op V) y).symm
      _ = (F.iCycles i).val.app (Opposite.op V) c := by rw [hy]
      _ = (q.f i).val.app (Opposite.op V) x := hq
  obtain ⟨w, hw⟩ := hpre i V x y hboundary
  have hcycles : (U.iCycles i).val.app (Opposite.op V)
        ((U.toCycles (i - 1) i).val.app (Opposite.op V) w) =
      (U.iCycles i).val.app (Opposite.op V) (z₁ - z₂) := by
    calc
      _ = (U.d (i - 1) i).val.app (Opposite.op V) w := by
        exact sectionMap_comp_eq_apply (U.toCycles_i (i - 1) i) (Opposite.op V) w
      _ = (U.iCycles i).val.app (Opposite.op V) (z₁ - z₂) := hw
  have hdiff : (U.homologyπ i).val.app (Opposite.op V) (z₁ - z₂) = 0 := by
    rw [← sectionMap_injective_of_mono R (U.iCycles i) V hcycles]
    exact congrArg (fun f : U.X (i - 1) ⟶ U.homology i => (f.val.app (Opposite.op V)) w)
      (U.toCycles_comp_homologyπ (i - 1) i)
  have hpi : (U.homologyπ i).val.app (Opposite.op V) z₁ =
      (U.homologyπ i).val.app (Opposite.op V) z₂ :=
    sub_eq_zero.mp (by simpa only [map_sub] using hdiff)
  exact hz₁.symm.trans (hpi.trans hz₂)

private lemma stageUnion_cycleCover
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F G : CochainComplex (SheafOfModules.{m} R) ℤ}
    (e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj G)
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ)
    (hcover : ∀ (i : ℤ) (V : C) (z : (G.cycles i).val.obj (Opposite.op V)),
      ∃ y : (S₀.H.X i).val.obj (Opposite.op V),
        (S₀.inc.f i).val.app (Opposite.op V) y = cycleRepresentative R e i V z)
    (i : ℤ) (V : C) (z : (G.cycles i).val.obj (Opposite.op V)) :
    ∃ y : ((stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀).X i).val.obj (Opposite.op V),
      (((stageUnionComplexInclusion R κ₀ hbase hκ₀ hℵ₀ S₀).f i).val.app
        (Opposite.op V)) y = cycleRepresentative R e i V z := by
  obtain ⟨x, hx⟩ := hcover i V z
  obtain ⟨y, hy⟩ := stageUnion_contains_initial R κ₀ hbase hκ₀ hℵ₀ S₀ i V x
  exact ⟨y, hy.trans hx⟩

private lemma stageUnionComplexInclusion_quasiIso
    (κ₀ : Cardinal.{max u v m r})
    (hbase : BaseBound.{v, m, r, u} R κ₀)
    {F G : CochainComplex (SheafOfModules.{m} R) ℤ}
    (e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj G)
    {Λ : Cardinal.{max u v m r}} (hκ₀ : κ₀ ≤ Λ)
    (hℵ₀ : Cardinal.aleph0 ≤ Λ) (S₀ : SmallStage R F Λ)
    (hcover : ∀ (i : ℤ) (V : C) (z : (G.cycles i).val.obj (Opposite.op V)),
      ∃ y : (S₀.H.X i).val.obj (Opposite.op V),
        (S₀.inc.f i).val.app (Opposite.op V) y = cycleRepresentative R e i V z) :
    QuasiIso (stageUnionComplexInclusion R κ₀ hbase hκ₀ hℵ₀ S₀) := by
  let U := stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀
  let q := stageUnionComplexInclusion R κ₀ hbase hκ₀ hℵ₀ S₀
  let : Mono q := stageUnionComplexInclusion_mono R κ₀ hbase hκ₀ hℵ₀ S₀
  have hpre : ∀ (i : ℤ) (V : C) (x : (U.X i).val.obj (Opposite.op V))
      (y : (F.X (i - 1)).val.obj (Opposite.op V)),
      (F.d (i - 1) i).val.app (Opposite.op V) y =
        (q.f i).val.app (Opposite.op V) x →
      ∃ z : (U.X (i - 1)).val.obj (Opposite.op V),
        (U.d (i - 1) i).val.app (Opposite.op V) z = x := by
    intro i V x y hy
    have hq : (q.f i).val.app (Opposite.op V) x = x.val := rfl
    have hy' : (F.d (i - 1) i).val.app (Opposite.op V) y = x.val := hy.trans hq
    exact stageUnion_boundaryTerm_preimage_at R κ₀ hbase hκ₀ hℵ₀ S₀
      (i - 1) i (by omega) V x y hy'
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let h := HomologicalComplex.homologyMap q i
  have hsurj (V : C) : Function.Surjective (h.val.app (Opposite.op V)) :=
    homologyMap_section_surjective_of_cycleCover R e q
      (stageUnion_cycleCover R κ₀ hbase e hκ₀ hℵ₀ S₀ hcover) i V
  have hepiVal : Epi h.val := PresheafOfModules.epi_of_surjective fun V => hsurj V.unop
  let : (SheafOfModules.forget R).IsEquivalence :=
    (chaoticSheafPresheafEquivalence R).isEquivalence_functor
  have hepi : Epi h := (SheafOfModules.forget R).epi_of_epi_map hepiVal
  have hinj (V : C) : Function.Injective (h.val.app (Opposite.op V)) :=
    homologyMap_section_injective_of_boundaryPreimage R q hpre i V
  have hmonoVal : Mono h.val := PresheafOfModules.mono_of_injective fun V => hinj V.unop
  have hmono : Mono h := (SheafOfModules.forget R).mono_of_mono_map hmonoVal
  let : Epi h := hepi
  let : Mono h := hmono
  exact isIso_of_mono_of_epi h

/-- There is a cardinal, depending only on the category and its sheaf of rings, such that every
representative of a derived object contains a quasi-isomorphic subcomplex bounded by that cardinal
and the size of the derived object. -/
@[stacks 0GYY]
theorem exists_small_quasiIso_subcomplex :
    ∃ κ : Cardinal.{max u v m r},
      ∀ (F : CochainComplex (SheafOfModules.{m} R) ℤ)
        (K : DerivedCategory (SheafOfModules.{m} R)),
        Nonempty (DerivedCategory.Q.obj F ≅ K) →
          ∃ (H : CochainComplex (SheafOfModules.{m} R) ℤ) (f : H ⟶ F),
            Mono f ∧ QuasiIso f ∧
              complexSectionSize H ≤
                max κ (derivedObjectSize R K) := by
  obtain ⟨κ₀, hbase⟩ :=
    exists_subcomplex_containing_sections_of_size_le.{v, m, r, u} R
  let κ : Cardinal.{max u v m r} := max κ₀
    (Cardinal.lift.{max u v m r, 0} (Cardinal.mk ℕ))
  refine ⟨κ, ?_⟩
  intro F K hFK
  let eFK : DerivedCategory.Q.obj F ≅ K := Classical.choice hFK
  obtain ⟨G, hGK, hGsize⟩ := exists_representative_of_derivedObjectSize R K
    ⟨F, hFK⟩
  let e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj G :=
    eFK ≪≫ hGK.some.symm
  let Λ := max κ (derivedObjectSize R K)
  have hκ₀ : κ₀ ≤ Λ := (le_max_left κ₀ _).trans (le_max_left κ _)
  have hℵ₀ : Cardinal.aleph0 ≤ Λ :=
    (show Cardinal.aleph0 ≤ κ from by simp [κ, Cardinal.lift_aleph0]).trans
      (le_max_left κ _)
  have hG : complexSectionSize G ≤ Λ :=
    hGsize.le.trans (le_max_right _ _)
  obtain ⟨H, f, hf, hsize, hcover⟩ :=
    exists_initial_smallStage R κ₀ hbase e Λ hκ₀ hG
  let S₀ : SmallStage R F Λ := ⟨H, f, hf, hsize⟩
  let U := stageUnionComplex R κ₀ hbase hκ₀ hℵ₀ S₀
  let q := stageUnionComplexInclusion R κ₀ hbase hκ₀ hℵ₀ S₀
  exact ⟨U, q, stageUnionComplexInclusion_mono R κ₀ hbase hκ₀ hℵ₀ S₀,
    stageUnionComplexInclusion_quasiIso R κ₀ hbase e hκ₀ hℵ₀ S₀ hcover,
    stageUnionComplex_size_le R κ₀ hbase hκ₀ hℵ₀ S₀⟩

end Stacks.ModulesOnACategory
