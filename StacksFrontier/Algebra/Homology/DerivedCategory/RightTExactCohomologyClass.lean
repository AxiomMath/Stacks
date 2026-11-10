module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# Right t-exact functors carrying a cohomology class to another, by dévissage

Let `L : D(𝒜') ⥤ D(𝒜)` be a triangulated functor between unbounded derived categories of abelian
categories, let `𝒫'` be a class of objects of `𝒜'` and `𝒫` a weak Serre class of objects of `𝒜`.
This file proves that `L` carries `D_{𝒫'}(𝒜')` into `D_𝒫(𝒜)` as soon as

* `L` is *right t-exact*, `L(D^{≤ m}) ⊆ D^{≤ m}`,
* `L` commutes with countable direct sums,
* `𝒫` is closed under colimits of sequences, and
* `H^k(L(M[-n])) ∈ 𝒫` for every `M ∈ 𝒫'` and all `n, k`.

This is the argument the Stacks project gives for **Stacks 07B9** parts (1)(c) and (2)(c), where
`L = Lg_!`: a bounded complex is reached from its cohomology objects by the truncation triangles,
so two-out-of-three in the weak Serre class `D_𝒫(𝒜)` does the bounded case; right t-exactness
lets `H^k(L K)` be computed on `τ_{≥ k} K`; and an unbounded `K` is the derived colimit of its
truncations `τ_{< n} K`, which `L` preserves, so `H^k(L K)` is the colimit of the
`H^k(L τ_{< n} K)`.

## Main results

* `DerivedCategory.homologyFunctor_preservesCountableCoproducts`: cohomology on `D(𝒜)` commutes
  with countable direct sums when `𝒜` has exact countable direct sums.
* `DerivedCategory.isLE_obj_of_adjunction`: a left adjoint of the functor `G : D(𝒜) ⥤ D(𝒜')`
  induced by an exact functor of abelian categories is right t-exact.
* `DerivedCategory.isHomotopyColimit_truncLT`: every object of `D(𝒜)` is the derived colimit of
  the system of its truncations `τ_{< n} K`, `n ∈ ℕ`.
* `ObjectProperty.colimit_mem_of_isWeakSerre`: a weak Serre class closed under countable direct
  sums is closed under colimits of sequences.
* `DerivedCategory.derivedCategoryB_obj_of_isLE_obj`: the dévissage itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w w' v v' u u'

namespace DerivedCategory

open WeakSerre DerivedCategoryB

section Homology

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **Cohomology on the derived category commutes with countable direct sums**, for an abelian
category whose countable direct sums exist and are exact.  Direct sums in `D(𝒜)` are computed by
termwise direct sums of complexes (**Stacks 0A5L**), and cohomology of a termwise direct sum is
the direct sum of the cohomologies. -/
theorem homologyFunctor_preservesCountableCoproducts (hA : HasExactCountableDirectSums A)
    (n : ℤ) : PreservesColimitsOfShape (Discrete ℕ) (homologyFunctor A n) where
  preservesColimit {F} := by
    have : HasCoproductsOfShape ℕ A := hA.hasCoproducts.1 ℕ
    have hQ := derivedCategory_Q_preservesCoproductsOfShape A hA ℕ
    set C : Discrete ℕ ⥤ CochainComplex A ℤ :=
      Discrete.functor fun j => Q.objPreimage (F.obj ⟨j⟩)
    have hfac : PreservesColimit C (Q ⋙ homologyFunctor A n) :=
      have := homologicalComplex_homologyFunctor_preservesCoproducts A hA ℕ n
      preservesColimit_of_natIso _ (homologyFunctorFactors A n).symm
    have : PreservesColimit (C ⋙ Q) (homologyFunctor A n) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves Q (colimit.isColimit C))
        (isColimitOfPreserves (Q ⋙ homologyFunctor A n) (colimit.isColimit C))
    exact preservesColimit_of_iso_diagram _
      (Discrete.natIso (F := C ⋙ Q) (G := F) fun j => Q.objObjPreimageIso (F.obj j))

end Homology

section Adjunction

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]

/-- The functor induced on derived categories by an exact functor carries objects `≥ n` to
objects `≥ n`: its cohomology objects are the images of those of the source. -/
theorem isGE_mapDerivedCategory_obj (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (X : DerivedCategory A) (n : ℤ) [X.IsGE n] :
    (G.mapDerivedCategory.obj X).IsGE n := by
  rw [isGE_iff]
  intro i hi
  exact (G.map_isZero (isZero_of_isGE X n i hi)).of_iso
    ((G.mapDerivedCategoryHomologyIso i).app X)

/-- **A left adjoint of the functor induced by an exact functor is right t-exact.**  If
`L ⊣ G.mapDerivedCategory` with `G` exact, then `L` carries objects `≤ n` to objects `≤ n`.

The truncation map `L X ⟶ τ_{≥ n+1}(L X)` corresponds under the adjunction to a map from `X`,
which is `≤ n`, to `G(τ_{≥ n+1}(L X))`, which is `≥ n + 1`; such a map vanishes, so the truncation
map vanishes, and then `τ_{≥ n+1}(L X)` is zero. -/
theorem isLE_obj_of_adjunction (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] {L : DerivedCategory B ⥤ DerivedCategory A}
    (adj : L ⊣ G.mapDerivedCategory) (X : DerivedCategory B) (n : ℤ) [X.IsLE n] :
    (L.obj X).IsLE n := by
  change TStructure.t.IsLE (L.obj X) n
  rw [TStructure.t.isLE_iff_isZero_truncGE_obj n (n + 1) rfl]
  set Y := (TStructure.t.truncGE (n + 1)).obj (L.obj X)
  have hπ : (TStructure.t.truncGEπ (n + 1)).app (L.obj X) = 0 := by
    have : (G.mapDerivedCategory.obj Y).IsGE (n + 1) :=
      isGE_mapDerivedCategory_obj G Y (n + 1)
    have : L.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
    have : L.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint L
    rw [← (adj.homEquiv _ _).symm_apply_apply ((TStructure.t.truncGEπ (n + 1)).app (L.obj X)),
      TStructure.t.zero (adj.homEquiv _ _ _) n (n + 1) (by omega), Adjunction.homEquiv_counit,
      L.map_zero, zero_comp]
  rw [IsZero.iff_id_eq_zero]
  exact TStructure.t.from_truncGE_obj_ext (by simp [hπ])

end Adjunction

section HomotopyColimit

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The system `n ↦ τ_{< n} K`, `n ∈ ℕ`, of truncations of an object `K` of `D(𝒜)`, with the
canonical maps `τ_{< m} K ⟶ τ_{< n} K` for `m ≤ n`. -/
def truncLTSystem (K : DerivedCategory A) : ℕ ⥤ DerivedCategory A where
  obj n := (TStructure.t.truncLT (n : ℤ)).obj K
  map {m n} h := (TStructure.t.natTransTruncLTOfLE (m : ℤ) (n : ℤ)
    (by exact_mod_cast leOfHom h)).app K
  map_id n := TStructure.t.natTransTruncLTOfLE_refl_app _ K
  map_comp {l m n} f g := (TStructure.t.natTransTruncLTOfLE_trans_app _ _ _ _ _ K).symm

/-- The canonical maps `τ_{< n} K ⟶ K` form a cocone over the system of truncations. -/
theorem truncLTSystem_map_ι (K : DerivedCategory A) {m n : ℕ} (h : m ⟶ n) :
    (truncLTSystem K).map h ≫ (TStructure.t.truncLTι (n : ℤ)).app K =
      (TStructure.t.truncLTι (m : ℤ)).app K :=
  TStructure.t.natTransTruncLTOfLE_ι_app _ _ _ K

/-- **Every object of `D(𝒜)` is the derived colimit of its truncations** `τ_{< n} K`, `n ∈ ℕ`,
for an abelian category with exact countable direct sums and exact colimits of sequences.

A derived colimit `K'` of the system exists, being the third vertex of a distinguished triangle
on `1 - f`; the truncation maps `τ_{< n} K ⟶ K` define a map `K' ⟶ K`.  On `H^i` the source is
`colim_n H^i(τ_{< n} K)` (**Stacks 0CRK**), and this system is constant equal to `H^i(K)` from
`n = i + 1` on, so the map is an isomorphism in every degree. -/
theorem isHomotopyColimit_truncLT (hA : HasExactCountableDirectSums A)
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] (K : DerivedCategory A)
    [HasCoproduct (truncLTSystem K).obj] :
    Pretriangulated.IsHomotopyColimit (truncLTSystem K) K := by
  set F := truncLTSystem K
  obtain ⟨K', p, q, hT⟩ := distinguished_cocone_triangle
    (Stacks.CountableCoproducts.oneSubShift F)
  set c : ∀ n, F.obj n ⟶ K := fun n => (TStructure.t.truncLTι (n : ℤ)).app K
  have hc : Stacks.CountableCoproducts.oneSubShift F ≫ Sigma.desc c = 0 := by
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [reassoc_of% (Stacks.CountableCoproducts.ι_oneSubShift F n), comp_zero,
      Preadditive.sub_comp, Sigma.ι_comp_desc, Category.assoc, Sigma.ι_comp_desc]
    exact sub_eq_zero.2 (truncLTSystem_map_ι K (homOfLE (Nat.le_succ n))).symm
  obtain ⟨b, hb⟩ := Triangle.yoneda_exact₂ _ hT (Sigma.desc c) hc
  have hiso : IsIso b := by
    rw [isIso_iff]
    intro i
    have := homologyFunctor_preservesCountableCoproducts hA i
    obtain ⟨e, he⟩ := exists_iso_colimit_of_isHomotopyColimit F (homologyFunctor A i) p q hT
    -- the system `H^i(τ_{< n} K)` is constant from `n₀ = (i + 1).toNat` on, equal to `H^i K`
    set n₀ : ℕ := (i + 1).toNat
    let cc : Cocone (F ⋙ homologyFunctor A i) :=
      { pt := (homologyFunctor A i).obj K
        ι := { app := fun n => (homologyFunctor A i).map (c n)
               naturality := fun m n h => by
                 simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
                   Functor.const_obj_map, Category.comp_id, ← Functor.map_comp]
                 exact congrArg _ (truncLTSystem_map_ι K h) } }
    have hlt : ∀ n : ℕ, n₀ ≤ n → i < (n : ℤ) := fun n hn => by omega
    have : IsIso (cc.ι.app n₀) := isIso_homologyMap_truncLTι_app (n₀ : ℤ) i (hlt n₀ le_rfl) K
    have hev : (F ⋙ homologyFunctor A i).IsEventuallyConstantFrom n₀ := by
      intro n φ
      have : IsIso (cc.ι.app n) := isIso_homologyMap_truncLTι_app (n : ℤ) i (hlt n (leOfHom φ)) K
      exact IsIso.of_isIso_fac_right (cc.w φ)
    let hcc : IsColimit cc := hev.isColimitOfIsIso cc
    have hfac : e.hom ≫ (homologyFunctor A i).map b = colimit.desc _ cc := by
      refine colimit.hom_ext fun n => ?_
      rw [colimit.ι_desc, reassoc_of% (he n), ← Functor.map_comp, Category.assoc,
        show p ≫ b = Sigma.desc c from hb.symm, Sigma.ι_comp_desc]
    have h2 : IsIso (e.hom ≫ (homologyFunctor A i).map b) := by
      rw [hfac]
      exact ⟨hcc.desc (colimit.cocone _), colimit.hom_ext fun n => by simp,
        hcc.hom_ext fun n => by
          rw [IsColimit.fac_assoc, colimit.cocone_ι, colimit.ι_desc, Category.comp_id]⟩
    exact IsIso.of_isIso_comp_left e.hom _
  exact ⟨p ≫ b, inv b ≫ q, isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso b).symm
      (by simp only [Triangle.mk_obj₁, Triangle.mk_mor₁, Iso.refl_hom, Category.id_comp,
        Category.comp_id]; rfl) (by simp) (by simp))⟩

end HomotopyColimit

section ColimitClosure

open ZeroObject

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **A weak Serre class closed under countable direct sums is closed under colimits of
sequences.**  The colimit of `A₀ ⟶ A₁ ⟶ ⋯` is the cokernel of `1 - f : ⊕ Aₙ ⟶ ⊕ Aₙ`
(**Stacks 093W**), and a weak Serre class is closed under cokernels. -/
theorem colimit_mem_of_isWeakSerre (P : ObjectProperty A) (hP : IsWeakSerre P)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape (Discrete ℕ) A]
    (hexact : PreservesFiniteLimits (colim : (ℕ ⥤ A) ⥤ A))
    (hsum : ∀ f : ℕ → A, (∀ n, P (f n)) → P (∐ f))
    (F : ℕ ⥤ A) (hF : ∀ n, P (F.obj n)) : P (colimit F) := by
  obtain ⟨w, hSE⟩ := Stacks.CountableCoproducts.shortExact_oneSubShift_piMap hexact F
  have : Epi (Stacks.CountableCoproducts.piMap F) := hSE.epi_g
  have h0 : P (0 : A) := zero_mem_of_isWeakSerre P hP _ (isZero_zero A)
  exact hP.mem_of_exact5
    { obj₀ := ∐ F.obj, obj₁ := ∐ F.obj, obj₂ := colimit F, obj₃ := 0, obj₄ := 0
      f₀ := Stacks.CountableCoproducts.oneSubShift F
      f₁ := Stacks.CountableCoproducts.piMap F
      f₂ := 0, f₃ := 0
      zero₀ := w
      exact₁ := hSE.exact
      exact₂ := (ShortComplex.exact_iff_epi _ rfl).mpr this
      exact₃ := ShortComplex.exact_of_isZero_X₂ _ (isZero_zero A) }
    (hsum _ hF) (hsum _ hF) h0 h0

end ColimitClosure

section Devissage

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (L : DerivedCategory B ⥤ DerivedCategory A) [L.CommShift ℤ] [L.IsTriangulated]

/-- **Moving the degree of a single complex across a shift-commuting functor**, on unbounded
derived categories: `single q ⋙ L ⋙ H^r ≅ single 0 ⋙ L ⋙ H^p` when `p + q = r`, because
`single q` is `single 0` shifted by `-q`, the shift passes through `L`, and the shift sequence
of `H^0` turns `H^r` of an object shifted by `-q` into `H^p`. -/
def singleFunctorCompHomologyFunctorShiftIsoOfEq (p q r : ℤ) (hr : p + q = r) :
    singleFunctor B q ⋙ L ⋙ homologyFunctor A r ≅
      singleFunctor B 0 ⋙ L ⋙ homologyFunctor A p :=
  Functor.isoWhiskerRight ((singleFunctors B).shiftIso (-q) q 0 (by omega)).symm
      (L ⋙ homologyFunctor A r) ≪≫
    Functor.isoWhiskerLeft (singleFunctor B 0)
      (Functor.isoWhiskerRight (L.commShiftIso (-q)) (homologyFunctor A r)) ≪≫
      Functor.isoWhiskerLeft (singleFunctor B 0) (Functor.isoWhiskerLeft L
        ((homologyFunctor A 0).shiftIso (-q) r p (by omega)))

variable (P' : ObjectProperty B) [P'.IsClosedUnderIsomorphisms] (P : ObjectProperty A)

omit [L.IsTriangulated] [P'.IsClosedUnderIsomorphisms] in
/-- The hypothesis on single objects in every degree follows from the one in degree `0`. -/
theorem derivedCategoryB_obj_singleFunctor (hP : P.IsClosedUnderIsomorphisms)
    (h0 : ∀ M, P' M → derivedCategoryB P (L.obj ((singleFunctor B 0).obj M)))
    (M : B) (hM : P' M) (q : ℤ) : derivedCategoryB P (L.obj ((singleFunctor B q).obj M)) :=
  fun r => hP.of_iso ((singleFunctorCompHomologyFunctorShiftIsoOfEq L (r - q) q r
    (by omega)).app M).symm (h0 M hM (r - q))

/-- Truncating `X ≤ m` from below at any degree `k` gives an object `≤ m`. -/
private theorem isLE_truncGE_obj (X : DerivedCategory B) (k m : ℤ) [X.IsLE m] :
    ((TStructure.t.truncGE k).obj X).IsLE m := by
  rw [isLE_iff]
  intro i hi
  by_cases hki : k ≤ i
  · exact (isZero_of_isLE X m i hi).of_iso ((truncGECompHomologyFunctorIso k i hki).app X).symm
  · exact isZero_of_isGE ((TStructure.t.truncGE k).obj X) k i (by omega)

variable {P' P} in
/-- **The bounded case of the dévissage.**  If `L` carries every `M[-q]`, `M ∈ 𝒫'`, into
`D_𝒫(𝒜)`, then it carries every object `X` with `X ≥ a`, `X ≤ m` and `H^i(X) ∈ 𝒫'` for
`a ≤ i ≤ m` into `D_𝒫(𝒜)`.  By induction on `m - a`, through the truncation triangle
`τ_{< m} X ⟶ X ⟶ τ_{≥ m} X`, whose third vertex is `H^m(X)[-m]`, and two-out-of-three in
`D_𝒫(𝒜)`. -/
theorem derivedCategoryB_obj_of_isGE_of_isLE (hP : IsWeakSerre P)
    (h0 : ∀ M, P' M → ∀ q : ℤ, derivedCategoryB P (L.obj ((singleFunctor B q).obj M))) :
    ∀ (d : ℕ) (X : DerivedCategory B) (a m : ℤ), m < a + d → X.IsGE a → X.IsLE m →
      (∀ i, a ≤ i → i ≤ m → P' ((homologyFunctor B i).obj X)) →
        derivedCategoryB P (L.obj X) := by
  have hcl := derivedCategoryB_isClosedUnderIsomorphisms P hP
  intro d
  induction d with
  | zero =>
    intro X a m hma hXa hXm _ n
    have hX : IsZero X := TStructure.t.isZero X m a (by omega)
    exact zero_mem_of_isWeakSerre P hP _ ((homologyFunctor A n).map_isZero (L.map_isZero hX))
  | succ d ih =>
    intro X a m hma hXa hXm hX
    by_cases hlt : m < a + d
    · exact ih X a m hlt hXa hXm hX
    set T := (TStructure.t.triangleLTGE m).obj X
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished m X
    have h₁ : derivedCategoryB P (L.obj T.obj₁) := by
      have : T.obj₁.IsGE a := by
        rw [isGE_iff]
        intro i hi
        by_cases him : i < m
        · exact (isZero_of_isGE X a i hi).of_iso ((truncLTCompHomologyFunctorIso m i him).app X)
        · exact isZero_of_isLE T.obj₁ (m - 1) i (by omega)
      exact ih T.obj₁ a (m - 1) (by omega) this inferInstance fun i hai him =>
        P'.prop_of_iso ((truncLTCompHomologyFunctorIso m i (by omega)).app X).symm
          (hX i hai (by omega))
    have h₃ : derivedCategoryB P (L.obj T.obj₃) := by
      have : T.obj₃.IsLE m := isLE_truncGE_obj X m m
      obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ m
      have hY : P' Y := P'.prop_of_iso
        (((truncGECompHomologyFunctorIso m m le_rfl).app X) ≪≫
          (homologyFunctor B m).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso B m).app Y)
        (hX m (by omega) le_rfl)
      exact hcl.of_iso (L.mapIso e).symm (h0 Y hY m)
    exact derivedCategoryB_mem_obj₂_of_distinguished P hP (L.mapTriangle.obj T)
      (L.map_distinguished T hT) h₁ h₃

variable {P' P} in
/-- **Cohomology of `L X` in degree `k` only sees `τ_{≥ k} X`**, for a right t-exact `L`:
`H^k(L X) ≅ H^k(L τ_{≥ k} X)`, since `L τ_{< k} X ≤ k - 1`. -/
theorem isIso_homologyFunctor_map_truncGEπ_of_isLE_obj
    (hL : ∀ (X : DerivedCategory B) (n : ℤ), X.IsLE n → (L.obj X).IsLE n)
    (X : DerivedCategory B) (k : ℤ) :
    IsIso ((homologyFunctor A k).map (L.map ((TStructure.t.truncGEπ k).app X))) := by
  set T := (TStructure.t.triangleLTGE k).obj X
  have hT := L.map_distinguished T (TStructure.t.triangleLTGE_distinguished k X)
  have h₁ : (L.obj T.obj₁).IsLE (k - 1) := hL _ _ inferInstance
  have : Mono ((homologyFunctor A k).map (L.mapTriangle.obj T).mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff _ hT k]
    exact (isZero_of_isLE (L.obj T.obj₁) (k - 1) k (by omega)).eq_of_src _ _
  have : Epi ((homologyFunctor A k).map (L.mapTriangle.obj T).mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff _ hT k (k + 1) rfl]
    exact (isZero_of_isLE (L.obj T.obj₁) (k - 1) (k + 1) (by omega)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi ((homologyFunctor A k).map (L.mapTriangle.obj T).mor₂)

variable {P' P} in
/-- **The bounded above case of the dévissage**: for a right t-exact `L`, if `X ≤ m` and
`H^i(X) ∈ 𝒫'` for `i ≤ m`, then `L X ∈ D_𝒫(𝒜)`; for `H^k(L X) = H^k(L τ_{≥ k} X)` and
`τ_{≥ k} X` is bounded. -/
theorem derivedCategoryB_obj_of_isLE (hP : IsWeakSerre P)
    (hL : ∀ (X : DerivedCategory B) (n : ℤ), X.IsLE n → (L.obj X).IsLE n)
    (h0 : ∀ M, P' M → ∀ q : ℤ, derivedCategoryB P (L.obj ((singleFunctor B q).obj M)))
    (X : DerivedCategory B) (m : ℤ) [X.IsLE m]
    (hX : ∀ i, i ≤ m → P' ((homologyFunctor B i).obj X)) :
    derivedCategoryB P (L.obj X) := by
  intro k
  have := isIso_homologyFunctor_map_truncGEπ_of_isLE_obj L hL X k
  refine hP.isClosedUnderIsomorphisms.of_iso
    (asIso ((homologyFunctor A k).map (L.map ((TStructure.t.truncGEπ k).app X)))).symm ?_
  set Y := (TStructure.t.truncGE k).obj X
  have hYm : Y.IsLE m := isLE_truncGE_obj X k m
  exact derivedCategoryB_obj_of_isGE_of_isLE L hP h0 (m - k + 1).toNat Y k m (by omega)
    inferInstance hYm (fun i hki him => P'.prop_of_iso
      ((truncGECompHomologyFunctorIso k i hki).app X) (hX i him)) k

variable {P' P} in
/-- **The dévissage.**  Let `L : D(𝒜') ⥤ D(𝒜)` be triangulated, right t-exact and commuting with
countable direct sums, let `𝒜` and `𝒜'` have exact countable direct sums and exact colimits of
sequences, and let `𝒫` be a weak Serre class of objects of `𝒜` closed under colimits of
sequences.  If `L` carries every `M[-q]` with `M ∈ 𝒫'` into `D_𝒫(𝒜)`, then it carries
`D_{𝒫'}(𝒜')` into `D_𝒫(𝒜)`.

An object `X` is the derived colimit of its truncations `τ_{< n} X`, which `L` preserves, so
`H^k(L X)` is the colimit of the `H^k(L τ_{< n} X)` (**Stacks 0CRK**), each in `𝒫` by the bounded
above case. -/
theorem derivedCategoryB_obj_of_isLE_obj (hP : IsWeakSerre P)
    (hA : HasExactCountableDirectSums A) (hB : HasExactCountableDirectSums B)
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    [HasColimitsOfShape ℕ B] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape (Discrete ℕ) L]
    (hL : ∀ (X : DerivedCategory B) (n : ℤ), X.IsLE n → (L.obj X).IsLE n)
    (hcolim : ∀ F : ℕ ⥤ A, (∀ n, P (F.obj n)) → P (colimit F))
    (h0 : ∀ M, P' M → ∀ q : ℤ, derivedCategoryB P (L.obj ((singleFunctor B q).obj M)))
    (X : DerivedCategory B) (hX : derivedCategoryB P' X) :
    derivedCategoryB P (L.obj X) := by
  have := derivedCategory_hasCountableCoproducts A hA
  have := derivedCategory_hasCountableCoproducts B hB
  obtain ⟨p, q, hT⟩ := (isHomotopyColimit_truncLT hB X).map L
  intro k
  have := homologyFunctor_preservesCountableCoproducts hA k
  obtain ⟨e, -⟩ := exists_iso_colimit_of_isHomotopyColimit (truncLTSystem X ⋙ L)
    (homologyFunctor A k) p q hT
  refine hP.isClosedUnderIsomorphisms.of_iso e (hcolim _ fun n => ?_)
  have : ((truncLTSystem X).obj n).IsLE ((n : ℤ) - 1) :=
    inferInstanceAs (((TStructure.t.truncLT (n : ℤ)).obj X).IsLE ((n : ℤ) - 1))
  exact derivedCategoryB_obj_of_isLE L hP hL h0 ((truncLTSystem X).obj n) ((n : ℤ) - 1)
    (fun i hi => P'.prop_of_iso ((truncLTCompHomologyFunctorIso (n : ℤ) i (by omega)).app X).symm
      (hX i)) k

end Devissage

end DerivedCategory
