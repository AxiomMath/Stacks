module

public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentHocolim
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.ShiftedHomTransport

/-!
# Units out of a homotopy colimit, and their universality

Let `Φ : D' ⥤ D` be a functor between derived categories, `E = hocolim Eₙ` in `D` and
`L = hocolim Lₙ` in `D'`, and suppose given at every stage a map `uₙ : Eₙ ⟶ Φ(Lₙ)` compatible
with the transition maps. Then there is a map `u : E ⟶ Φ(L)` restricting to `uₙ` followed by
`Φ` of the coprojection on every stage. If moreover each `uₙ` is a *unit* — composing with it
identifies `Hom(Lₙ, N)` with `Hom(Eₙ, Φ N)` — and the coprojections of both systems are
isomorphisms on truncations `τ_{≥ k}` for `k` going to `-∞`, then `u` is a unit on the bounded
below objects, provided `Φ` carries objects in degrees `≥ m` to objects in degrees `≥ m + a`.

## Main results

* `CategoryTheory.Pretriangulated.IsHomotopyColimitWith.exists_desc`: a compatible family out of
  the system extends over the homotopy colimit (not uniquely).
* `Stacks.Cohomology.RelativeExtCanonical.exists_unit_of_isHomotopyColimitWith`: the unit `u`.
* `Stacks.Cohomology.RelativeExtCanonical.bijective_comp_of_isIso_truncGE_map`: a map inducing
  an isomorphism on `τ_{≥ a}` induces a bijection on maps into objects in degrees `≥ a`.
* `Stacks.Cohomology.RelativeExtCanonical.bijective_unit_comp_map`: the universality of `u`.
* `Stacks.Cohomology.RelativeExtCanonical.isIso_truncGE_map_of_isLE_preserving`: a right
  t-exact triangulated functor carries a map inducing an isomorphism on `τ_{≥ k}` to one inducing
  an isomorphism on `τ_{≥ k + 1}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

universe v u

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **The coprojections of a homotopy colimit are compatible with the transition maps**:
`fₙ ≫ cₙ₊₁ = cₙ`. -/
private theorem transition_comp_coprojection_of_isHomotopyColimitWith {F : ℕ ⥤ D}
    [HasCoproduct F.obj] {K : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitWith F K c) (n : ℕ) :
    F.map (homOfLE (Nat.le_succ n)) ≫ c (n + 1) = c n := by
  obtain ⟨p, q, hT, hc⟩ := h
  have h0 := comp_distTriang_mor_zero₁₂ _ hT
  have h1 := congrArg (fun g ↦ Limits.Sigma.ι F.obj n ≫ g) h0
  simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, comp_zero] at h1
  rw [← Category.assoc, Limits.Sigma.ι_comp_desc, Preadditive.sub_comp, Category.assoc, hc, hc,
    sub_eq_zero] at h1
  exact h1.symm

/-- **A compatible family out of the system extends over the homotopy colimit.** If
`xₙ : Kₙ ⟶ Y` satisfies `fₙ ≫ xₙ₊₁ = xₙ`, there is `x : K ⟶ Y` with `cₙ ≫ x = xₙ` for all `n`.
The extension is not unique. -/
theorem IsHomotopyColimitWith.exists_desc {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitWith F K c) {Y : D}
    (x : ∀ n, F.obj n ⟶ Y)
    (hx : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ x (n + 1) = x n) :
    ∃ y : K ⟶ Y, ∀ n, c n ≫ y = x n := by
  obtain ⟨p, q, hT, hc⟩ := h
  have hw : (Limits.Sigma.desc fun n ↦ Limits.Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Limits.Sigma.ι F.obj (n + 1)) ≫
        Limits.Sigma.desc x = 0 := by
    refine Limits.Sigma.hom_ext _ _ fun n ↦ ?_
    rw [← Category.assoc, Limits.Sigma.ι_comp_desc, Preadditive.sub_comp, Limits.Sigma.ι_comp_desc,
      Category.assoc, Limits.Sigma.ι_comp_desc, hx n, sub_self, comp_zero]
  obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ _ hT (Limits.Sigma.desc x) hw
  refine ⟨y, fun n ↦ ?_⟩
  have h1 := congrArg (fun g ↦ Limits.Sigma.ι F.obj n ≫ g) hy
  simp only [Triangle.mk_mor₂, Limits.Sigma.ι_comp_desc] at h1
  rw [h1, ← Category.assoc, hc]

/-- **Isomorphic systems have isomorphic homotopy colimits, compatibly with the coprojections.**
If `α : F ≅ F'` and `K = hocolim F`, `K' = hocolim F'` with coprojections `c`, `c'`, there is an
isomorphism `φ : K ≅ K'` with `cₙ ≫ φ = αₙ ≫ c'ₙ`. It is not unique. -/
theorem IsHomotopyColimitWith.exists_iso_of_iso {F F' : ℕ ⥤ D} [HasCoproduct F.obj]
    [HasCoproduct F'.obj] {K K' : D} {c : ∀ n, F.obj n ⟶ K} {c' : ∀ n, F'.obj n ⟶ K'}
    (h : IsHomotopyColimitWith F K c) (h' : IsHomotopyColimitWith F' K' c') (α : F ≅ F') :
    ∃ φ : K ≅ K', ∀ n, c n ≫ φ.hom = α.hom.app n ≫ c' n := by
  obtain ⟨p, q, hT, hc⟩ := h
  obtain ⟨p', q', hT', hc'⟩ := h'
  let a : ∐ F.obj ⟶ ∐ F'.obj := Limits.Sigma.map fun n ↦ α.hom.app n
  have ha : (Limits.Sigma.desc fun n ↦ Limits.Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Limits.Sigma.ι F.obj (n + 1)) ≫ a =
      a ≫ Limits.Sigma.desc fun n ↦ Limits.Sigma.ι F'.obj n -
        F'.map (homOfLE (Nat.le_succ n)) ≫ Limits.Sigma.ι F'.obj (n + 1) := by
    refine Limits.Sigma.hom_ext _ _ fun n ↦ ?_
    have hn := α.hom.naturality (homOfLE (Nat.le_succ n))
    simp only [a, Limits.Sigma.ι_comp_desc_assoc, Preadditive.sub_comp, Category.assoc,
      Limits.Sigma.ι_map, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_comp_desc,
      Preadditive.comp_sub]
    rw [← reassoc_of% hn]
  obtain ⟨φ, hφ₂, hφ₃⟩ := complete_distinguished_triangle_morphism _ _ hT hT' a a ha
  have hiso : IsIso φ := by
    have : IsIso a := by
      refine ⟨Limits.Sigma.map fun n ↦ α.inv.app n, ?_, ?_⟩ <;>
        refine Limits.Sigma.hom_ext _ _ fun n ↦ ?_ <;> simp [a, Limits.Sigma.ι_map_assoc]
    exact isIso₃_of_isIso₁₂ (Triangle.homMk _ _ a a φ ha hφ₂ hφ₃) hT hT'
      (by dsimp; exact this) (by dsimp; exact this)
  refine ⟨asIso φ, fun n ↦ ?_⟩
  have h1 := congrArg (fun g ↦ Limits.Sigma.ι F.obj n ≫ g) hφ₂
  simp only [Triangle.mk_mor₂, ← Category.assoc, hc, a, Limits.Sigma.ι_map] at h1
  simp only [asIso_hom, h1, Category.assoc, hc']

end CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.RelativeExtCanonical

universe v u v' u' w w'

section Unit

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {D' : Type u'} [Category.{v'} D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

/-- **A unit out of a homotopy colimit.** Let `E = hocolim Eₙ` (coprojections `cₙ`) in `D`,
`L = hocolim Lₙ` (coprojections `dₙ`) in `D'`, `Φ : D' ⥤ D` a functor, and `uₙ : Eₙ ⟶ Φ(Lₙ)`
maps compatible with the transition maps. Then there is `u : E ⟶ Φ(L)` with
`cₙ ≫ u = uₙ ≫ Φ(dₙ)` for all `n`. -/
theorem exists_unit_of_isHomotopyColimitWith (Φ : D' ⥤ D)
    {FE : ℕ ⥤ D} [HasCoproduct FE.obj] {E : D} {c : ∀ n, FE.obj n ⟶ E}
    (hE : IsHomotopyColimitWith FE E c)
    {FL : ℕ ⥤ D'} [HasCoproduct FL.obj] {L : D'} {d : ∀ n, FL.obj n ⟶ L}
    (hL : IsHomotopyColimitWith FL L d)
    (u : ∀ n, FE.obj n ⟶ Φ.obj (FL.obj n))
    (hu : ∀ n, FE.map (homOfLE (Nat.le_succ n)) ≫ u (n + 1) =
      u n ≫ Φ.map (FL.map (homOfLE (Nat.le_succ n)))) :
    ∃ η : E ⟶ Φ.obj L, ∀ n, c n ≫ η = u n ≫ Φ.map (d n) :=
  hE.exists_desc (fun n ↦ u n ≫ Φ.map (d n)) fun n ↦ by
    rw [← Category.assoc, hu n, Category.assoc, ← Φ.map_comp,
      transition_comp_coprojection_of_isHomotopyColimitWith hL n]

end Unit

section Bijective

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {C' : Type u'} [Category.{v'} C'] [Abelian C'] [HasDerivedCategory.{w'} C']

/-- **A map inducing an isomorphism on `τ_{≥ a}` induces a bijection on maps into objects in
degrees `≥ a`.** -/
theorem bijective_comp_of_isIso_truncGE_map {A' A : DerivedCategory C} (f : A' ⟶ A) (a : ℤ)
    (hf : IsIso ((DerivedCategory.TStructure.t.truncGE a).map f)) (N : DerivedCategory C)
    [N.IsGE a] : Function.Bijective (fun x : A ⟶ N ↦ f ≫ x) := by
  let t := DerivedCategory.TStructure.t (C := C)
  have hπ : f ≫ (t.truncGEπ a).app A = (t.truncGEπ a).app A' ≫ (t.truncGE a).map f := by simp
  constructor
  · intro x y hxy
    simp only at hxy
    rw [← t.π_descTruncGE x a, ← t.π_descTruncGE y a, ← Category.assoc, ← Category.assoc,
      hπ, Category.assoc, Category.assoc] at hxy
    rw [← t.π_descTruncGE x a, ← t.π_descTruncGE y a, (cancel_epi _).1 (t.from_truncGE_obj_ext hxy)]
  · intro z
    refine ⟨(t.truncGEπ a).app A ≫ inv ((t.truncGE a).map f) ≫ t.descTruncGE z a, ?_⟩
    simp only
    rw [← Category.assoc, hπ, Category.assoc, IsIso.hom_inv_id_assoc, t.π_descTruncGE]

/-- **Universality of the unit out of a homotopy colimit.** In the situation of
`exists_unit_of_isHomotopyColimitWith`, let `P` be a class of objects of `D(C')`, and suppose

* at every stage composing with `uₙ` identifies `Hom(Lₙ, N)` with `Hom(Eₙ, Φ N)` for `N ∈ P`;
* for every `k` there is a stage `n` at which both coprojections `Eₙ ⟶ E` and `Lₙ ⟶ L` are
  isomorphisms on `τ_{≥ k}`;
* `Φ` carries objects in degrees `≥ m` to objects in degrees `≥ m + a`.

Then for every `N ∈ P` in degrees `≥ m`, composing with `η` identifies `Hom(L, N)` with
`Hom(E, Φ N)`. -/
theorem bijective_unit_comp_map (Φ : DerivedCategory C' ⥤ DerivedCategory C) (a : ℤ)
    (hΦ : ∀ (N : DerivedCategory C') (m : ℤ), N.IsGE m → (Φ.obj N).IsGE (m + a))
    {FE : ℕ ⥤ DerivedCategory C} {E : DerivedCategory C} {c : ∀ n, FE.obj n ⟶ E}
    {FL : ℕ ⥤ DerivedCategory C'} {L : DerivedCategory C'} {d : ∀ n, FL.obj n ⟶ L}
    (u : ∀ n, FE.obj n ⟶ Φ.obj (FL.obj n)) (η : E ⟶ Φ.obj L)
    (hη : ∀ n, c n ≫ η = u n ≫ Φ.map (d n))
    (P : ObjectProperty (DerivedCategory C'))
    (hu : ∀ n (N : DerivedCategory C'), P N →
      Function.Bijective (fun ψ : FL.obj n ⟶ N ↦ u n ≫ Φ.map ψ))
    (hstage : ∀ k : ℤ, ∃ n, IsIso ((DerivedCategory.TStructure.t.truncGE k).map (c n)) ∧
      IsIso ((DerivedCategory.TStructure.t.truncGE k).map (d n)))
    (N : DerivedCategory C') (hN : P N) (m : ℤ) (hm : N.IsGE m) :
    Function.Bijective (fun ψ : L ⟶ N ↦ η ≫ Φ.map ψ) := by
  obtain ⟨n, hc, hd⟩ := hstage (min m (m + a))
  have : N.IsGE (min m (m + a)) :=
    DerivedCategory.TStructure.t.isGE_of_ge N _ _ (min_le_left _ _)
  have : (Φ.obj N).IsGE (m + a) := hΦ N m hm
  have : (Φ.obj N).IsGE (min m (m + a)) :=
    DerivedCategory.TStructure.t.isGE_of_ge (Φ.obj N) _ _ (min_le_right _ _)
  have h1 := bijective_comp_of_isIso_truncGE_map (d n) _ hd N
  have h2 := bijective_comp_of_isIso_truncGE_map (c n) _ hc (Φ.obj N)
  have hcomm : (fun x : E ⟶ Φ.obj N ↦ c n ≫ x) ∘ (fun ψ : L ⟶ N ↦ η ≫ Φ.map ψ) =
      (fun ψ : FL.obj n ⟶ N ↦ u n ≫ Φ.map ψ) ∘ (fun x : L ⟶ N ↦ d n ≫ x) := by
    funext ψ
    simp only [Function.comp_apply]
    rw [← Category.assoc, hη, Category.assoc, ← Φ.map_comp]
  exact (Function.Bijective.of_comp_iff' h2 _).1 (hcomm ▸ (hu n N hN).comp h1)

end Bijective


section RightExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {C' : Type u'} [Category.{v'} C'] [Abelian C'] [HasDerivedCategory.{w'} C']

/-- A map inducing an isomorphism on `τ_{≥ a}` induces isomorphisms on cohomology in the degrees
`≥ a`. -/
theorem isIso_homologyFunctor_map_of_isIso_truncGE_map {A B : DerivedCategory C} (φ : A ⟶ B)
    (a : ℤ) (h : IsIso ((DerivedCategory.TStructure.t.truncGE a).map φ)) (i : ℤ) (hi : a ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor C i).map φ) := by
  let t := DerivedCategory.TStructure.t (C := C)
  have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ (C := C) a i hi A
  have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ (C := C) a i hi B
  have : IsIso ((DerivedCategory.homologyFunctor C i).map (φ ≫ (t.truncGEπ a).app B)) := by
    rw [← Functor.id_map φ, (t.truncGEπ a).naturality, Functor.map_comp]
    infer_instance
  rw [Functor.map_comp] at this
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor C i).map
    ((t.truncGEπ a).app B))

/-- A map inducing isomorphisms on cohomology in the degrees `≥ a` induces an isomorphism on
`τ_{≥ a}`. -/
theorem isIso_truncGE_map_of_isIso_homologyFunctor_map {A B : DerivedCategory C} (φ : A ⟶ B)
    (a : ℤ) (h : ∀ i : ℤ, a ≤ i → IsIso ((DerivedCategory.homologyFunctor C i).map φ)) :
    IsIso ((DerivedCategory.TStructure.t.truncGE a).map φ) := by
  let t := DerivedCategory.TStructure.t (C := C)
  rw [DerivedCategory.isIso_iff]
  intro i
  by_cases hi : a ≤ i
  · have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ (C := C) a i hi A
    have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ (C := C) a i hi B
    have := h i hi
    have : IsIso ((DerivedCategory.homologyFunctor C i).map
        ((t.truncGEπ a).app A ≫ (t.truncGE a).map φ)) := by
      rw [← (t.truncGEπ a).naturality, Functor.map_comp, Functor.id_map]
      infer_instance
    rw [Functor.map_comp] at this
    exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctor C i).map
      ((t.truncGEπ a).app A)) _
  · exact (DerivedCategory.isZero_of_isGE ((t.truncGE a).obj A) a i (by omega)).isIso
      (DerivedCategory.isZero_of_isGE ((t.truncGE a).obj B) a i (by omega)) _

/-- If a map induces an isomorphism on `τ_{≥ k}`, its cone has no cohomology in degrees `≥ k`. -/
theorem isLE_obj₃_of_isIso_truncGE_map (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (k : ℤ)
    (h : IsIso ((DerivedCategory.TStructure.t.truncGE k).map T.mor₁)) : T.obj₃.IsLE (k - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hiso := isIso_homologyFunctor_map_of_isIso_truncGE_map T.mor₁ k h
  have hepi : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1),
      ← DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1)]
    have := hiso (i + 1) (by omega)
    infer_instance
  have hzero : (DerivedCategory.homologyFunctor C i).map T.mor₂ = 0 := by
    rw [← DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    have := hiso i (by omega)
    infer_instance
  exact IsZero.of_epi_eq_zero _ hzero

/-- **A right t-exact triangulated functor shifts truncation isomorphisms by one.** Let
`F : D(C) ⥤ D(C')` be triangulated and carry objects in degrees `≤ j` to objects in degrees
`≤ j`. If `φ` induces an isomorphism on `τ_{≥ k}`, then `F φ` induces one on `τ_{≥ k + 1}`. -/
theorem isIso_truncGE_map_of_isLE_preserving (F : DerivedCategory C ⥤ DerivedCategory C')
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ (X : DerivedCategory C) (j : ℤ), X.IsLE j → (F.obj X).IsLE j)
    {A B : DerivedCategory C} (φ : A ⟶ B) (k : ℤ)
    (h : IsIso ((DerivedCategory.TStructure.t.truncGE k).map φ)) :
    IsIso ((DerivedCategory.TStructure.t.truncGE (k + 1)).map (F.map φ)) := by
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle φ
  have hC := isLE_obj₃_of_isIso_truncGE_map _ hT k h
  have hFT := F.map_distinguished _ hT
  have hFC : (F.obj Z).IsLE (k - 1) := hF Z _ hC
  refine isIso_truncGE_map_of_isIso_homologyFunctor_map _ _ fun i hi ↦ ?_
  have hz : ∀ j : ℤ, k - 1 < j → IsZero ((DerivedCategory.homologyFunctor C' j).obj (F.obj Z)) :=
    fun j hj ↦ DerivedCategory.isZero_of_isLE (F.obj Z) (k - 1) j hj
  have hepi : Epi ((DerivedCategory.homologyFunctor C' i).map (F.map φ)) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff
      (F.mapTriangle.obj (Triangle.mk φ g δ)) hFT i).2 ((hz i (by omega)).eq_of_tgt _ _)
  have hmono : Mono ((DerivedCategory.homologyFunctor C' i).map (F.map φ)) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      (F.mapTriangle.obj (Triangle.mk φ g δ)) hFT (i - 1) i (by omega)).2
        ((hz (i - 1) (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

end RightExact

section Yoneda

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒟 : Type u'} [Category.{v'} 𝒟]

/-- **A natural identification on a class containing the source is composition with a unit.**
If `χ_N : Hom(A, N) ≃ Hom(B, Φ N)` is natural in `N ∈ P` and `A ∈ P`, then
`χ_N(x) = χ_A(𝟙 A) ≫ Φ x`. -/
theorem homEquiv_eq_unit_comp (Φ : 𝒞 ⥤ 𝒟) (P : ObjectProperty 𝒞) {A : 𝒞} {B : 𝒟}
    (χ : ∀ N : 𝒞, P N → ((A ⟶ N) ≃ (B ⟶ Φ.obj N)))
    (hχ : ∀ {N N' : 𝒞} (hN : P N) (hN' : P N') (g : N ⟶ N') (x : A ⟶ N),
      χ N' hN' (x ≫ g) = χ N hN x ≫ Φ.map g)
    (hA : P A) (N : 𝒞) (hN : P N) (x : A ⟶ N) :
    χ N hN x = χ A hA (𝟙 A) ≫ Φ.map x := by
  rw [← hχ hA hN, Category.id_comp]

/-- In the situation of `homEquiv_eq_unit_comp`, composing with the unit is bijective on
`Hom(A, N)` for every `N ∈ P`. -/
theorem bijective_unit_comp_of_homEquiv (Φ : 𝒞 ⥤ 𝒟) (P : ObjectProperty 𝒞) {A : 𝒞} {B : 𝒟}
    (χ : ∀ N : 𝒞, P N → ((A ⟶ N) ≃ (B ⟶ Φ.obj N)))
    (hχ : ∀ {N N' : 𝒞} (hN : P N) (hN' : P N') (g : N ⟶ N') (x : A ⟶ N),
      χ N' hN' (x ≫ g) = χ N hN x ≫ Φ.map g)
    (hA : P A) (N : 𝒞) (hN : P N) :
    Function.Bijective (fun x : A ⟶ N ↦ χ A hA (𝟙 A) ≫ Φ.map x) := by
  convert (χ N hN).bijective using 1
  exact funext fun x ↦ (homEquiv_eq_unit_comp Φ P χ hχ hA N hN x).symm

end Yoneda

section UnitEquiv

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒟 : Type u'} [Category.{v'} 𝒟]

/-- **A unit which is universal on a class gives a natural identification.** If composing with
`η : E ⟶ Φ(L)` identifies `Hom(L, N)` with `Hom(E, Φ N)` for every `N ∈ P`, these bijections are
natural in `N ∈ P`. -/
def naturalHomEquivOfUnit (Φ : 𝒞 ⥤ 𝒟) (P : ObjectProperty 𝒞) {L : 𝒞} {E : 𝒟}
    (η : E ⟶ Φ.obj L)
    (hη : ∀ N : 𝒞, P N → Function.Bijective (fun ψ : L ⟶ N ↦ η ≫ Φ.map ψ)) :
    ShiftedHom.NaturalHomEquiv (𝟭 𝒞) Φ L E P where
  equiv N hN := Equiv.ofBijective _ (hη N hN)
  naturality _ _ g x := by
    simp only [Equiv.ofBijective_apply, Functor.id_map, Functor.map_comp, Category.assoc]

/-- The identification `naturalHomEquivOfUnit Φ P η hη` sends `ψ : L ⟶ N` to `η ≫ Φ.map ψ`. -/
theorem naturalHomEquivOfUnit_apply (Φ : 𝒞 ⥤ 𝒟) (P : ObjectProperty 𝒞) {L : 𝒞} {E : 𝒟}
    (η : E ⟶ Φ.obj L)
    (hη : ∀ N : 𝒞, P N → Function.Bijective (fun ψ : L ⟶ N ↦ η ≫ Φ.map ψ))
    (N : 𝒞) (hN : P N) (ψ : L ⟶ N) :
    (naturalHomEquivOfUnit Φ P η hη).equiv N hN ψ = η ≫ Φ.map ψ :=
  rfl

/-- **A functor bijective on the relevant Hom-sets gives a natural identification.** If
`R : 𝒟 ⥤ 𝒟'` is bijective on `Hom(A, Φ N)` for `N ∈ P`, then `Hom(R A, R(Φ N)) ≃ Hom(A, Φ N)`
naturally in `N ∈ P`. -/
def naturalHomEquivOfBijectiveMap {𝒟' : Type*} [Category 𝒟'] (Φ : 𝒞 ⥤ 𝒟) (R : 𝒟 ⥤ 𝒟')
    (P : ObjectProperty 𝒞) (A : 𝒟)
    (hR : ∀ N : 𝒞, P N → Function.Bijective (fun x : A ⟶ Φ.obj N ↦ R.map x)) :
    ShiftedHom.NaturalHomEquiv (Φ ⋙ R) Φ (R.obj A) A P where
  equiv N hN := (Equiv.ofBijective _ (hR N hN)).symm
  naturality {N N'} hN hN' g y := by
    apply (hR N' hN').1
    have h1 := Equiv.ofBijective_apply_symm_apply (fun x : A ⟶ Φ.obj N' ↦ R.map x) (hR N' hN')
      (y ≫ (Φ ⋙ R).map g)
    have h2 := Equiv.ofBijective_apply_symm_apply (fun x : A ⟶ Φ.obj N ↦ R.map x) (hR N hN) y
    simp only at h1 h2 ⊢
    rw [h1, Functor.map_comp, h2]
    rfl

end UnitEquiv

end Stacks.Cohomology.RelativeExtCanonical

end
