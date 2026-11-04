module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Dévissage of a comparison transformation on bounded below derived categories

Let `A` be an abelian category with a derived category, let `F : D⁺(A) ⥤ D⁺(A)` be a
triangulated functor commuting with the shift, and let `α : 𝟭 ⟶ F` be a natural transformation
commuting with the shift. Fix `n : ℤ` and consider the property

`Q(K) : H^i(α_K) is invertible for every i ≤ n, and H^{n+1}(α_K) is a monomorphism.`

Then `Q` propagates from a class of single objects to every object of `D⁺(A)` with cohomology
in finitely many degrees, all of it in that class. Between bounded below derived categories, an
exact functor preserves invertibility on cohomology in a fixed degree, and a total right derived
functor carries a morphism invertible on cohomology in all degrees `≤ n` to one invertible on
cohomology in degree `n`.

## Main results

* `DerivedCategory.Plus.ofNonnegative`: an object of `D(A)` with no cohomology in negative
  degrees, as an object of `D⁺(A)`.
* `DerivedCategory.Plus.isIso_homology_comparison_of_triangle`: the inductive step — `Q` passes
  from the outer two vertices of a distinguished triangle to the middle one.
* `DerivedCategory.Plus.isIso_homology_comparison_of_bounded`: the dévissage — `Q` holds for
  every object with cohomology in a finite window lying in the given class, as soon as it holds
  for the single objects of that class.
* `DerivedCategory.Plus.isIso_homology_mapDerivedCategoryPlus_map`: an exact functor preserves
  invertibility of a morphism on cohomology in a fixed degree.
* `DerivedCategory.Plus.isIso_homology_rightDerivedFunctorPlus_map_truncLEι_app`: a total right
  derived functor carries `τ_{≤n}K ⟶ K` to a morphism invertible on cohomology in degrees `≤ n`.
* `DerivedCategory.Plus.isIso_homology_rightDerivedFunctorPlus_map_of_isIso_homology_le`: a total
  right derived functor carries a morphism invertible on cohomology in all degrees `≤ n` to one
  invertible on cohomology in degree `n`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace DerivedCategory.Plus

section Nonnegative

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- **An object of the unbounded derived category with no cohomology in negative degrees,
regarded as an object of the bounded below derived category.** -/
def ofNonnegative (L : DerivedCategory A)
    (hneg : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor A i).obj L)) :
    Plus A :=
  ⟨L, 0, (DerivedCategory.isGE_iff L 0).2 hneg⟩

/-- An object placed in the bounded below derived category by `ofNonnegative` is bounded below
by `0`. -/
lemma isGE_ofNonnegative (L : DerivedCategory A)
    (hneg : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor A i).obj L)) :
    (ofNonnegative L hneg).IsGE 0 :=
  (isGE_ι_obj_iff (ofNonnegative L hneg) 0).1 ((DerivedCategory.isGE_iff L 0).2 hneg)

end Nonnegative

section PropHomology

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- The cohomology of `τ_{≤a}K` lies in any isomorphism-closed class containing a zero object
and the cohomology of `K` in the degrees `≤ a`. -/
theorem prop_homology_truncLE_obj (K : Plus A) (a : ℤ)
    (hK : ∀ i : ℤ, i ≤ a → P ((homologyFunctor A i).obj K)) (i : ℤ) :
    P ((homologyFunctor A i).obj ((TStructure.t.truncLE a).obj K)) := by
  by_cases hi : i ≤ a
  · have := isIso_homologyMap_truncLEι_app K i a hi
    exact P.prop_of_iso
      (asIso ((homologyFunctor A i).map ((TStructure.t.truncLEι a).app K))).symm (hK i hi)
  · exact P.prop_of_isZero (isZero_homology_truncLE_obj K i a (by omega))

/-- The cohomology of `τ_{>a}K` lies in any isomorphism-closed class containing a zero object
and the cohomology of `K` in the degrees `> a`. -/
theorem prop_homology_truncGT_obj (K : Plus A) (a : ℤ)
    (hK : ∀ i : ℤ, a < i → P ((homologyFunctor A i).obj K)) (i : ℤ) :
    P ((homologyFunctor A i).obj ((TStructure.t.truncGT a).obj K)) := by
  by_cases hi : a < i
  · have := isIso_homologyMap_truncGTπ_app K i a hi
    exact P.prop_of_iso
      (asIso ((homologyFunctor A i).map ((TStructure.t.truncGTπ a).app K))) (hK i hi)
  · exact P.prop_of_isZero (isZero_homology_truncGT_obj K i a (by omega))

end PropHomology

section Devissage

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- **The inductive step of the dévissage.** Let `F` be a triangulated endofunctor of `D⁺(A)`
commuting with the shift and `α : 𝟭 ⟶ F` a natural transformation commuting with the shift. If,
for the outer two vertices of a distinguished triangle, `H^i(α)` is invertible in all degrees
`i ≤ n` and monomorphic in degree `n + 1`, then the same holds at the middle vertex. -/
theorem isIso_homology_comparison_of_triangle
    (F : Plus A ⥤ Plus A) [F.CommShift ℤ] [F.IsTriangulated]
    (α : 𝟭 (Plus A) ⟶ F) [NatTrans.CommShift α ℤ]
    (T : Triangle (Plus A)) (hT : T ∈ distTriang (Plus A)) (n : ℤ)
    (hfirst : (∀ i ≤ n, IsIso ((homologyFunctor A i).map (α.app T.obj₁))) ∧
      Mono ((homologyFunctor A (n + 1)).map (α.app T.obj₁)))
    (hthird : (∀ i ≤ n, IsIso ((homologyFunctor A i).map (α.app T.obj₃))) ∧
      Mono ((homologyFunctor A (n + 1)).map (α.app T.obj₃))) :
    (∀ i ≤ n, IsIso ((homologyFunctor A i).map (α.app T.obj₂))) ∧
      Mono ((homologyFunctor A (n + 1)).map (α.app T.obj₂)) := by
  let source := T
  let target := F.mapTriangle.obj T
  have hs : source ∈ distTriang (Plus A) := hT
  have ht := F.map_distinguished T hT
  let φ : source ⟶ target :=
    { hom₁ := α.app T.obj₁
      hom₂ := α.app T.obj₂
      hom₃ := α.app T.obj₃
      comm₁ := α.naturality T.mor₁
      comm₂ := α.naturality T.mor₂
      comm₃ := by
        have hnat : T.mor₃ ≫ α.app (T.obj₁⟦(1 : ℤ)⟧) = α.app T.obj₃ ≫ F.map T.mor₃ :=
          α.naturality T.mor₃
        have hcs := NatTrans.shift_app_comm α (1 : ℤ) T.obj₁
        show T.mor₃ ≫ (α.app T.obj₁)⟦(1 : ℤ)⟧' =
          α.app T.obj₃ ≫ F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁
        rw [← Category.assoc, ← hnat, Category.assoc, ← hcs]
        simp }
  let H := homologyFunctor A 0
  let row (U : Triangle (Plus A)) (i : ℤ) :=
    ComposableArrows.mk₄
      ((homologyFunctor A (i - 1)).map U.mor₂)
      (H.homologySequenceδ U (i - 1) i (by omega))
      ((homologyFunctor A i).map U.mor₁)
      ((homologyFunctor A i).map U.mor₂)
  have hexact (U : Triangle (Plus A)) (hU : U ∈ distTriang _) (i : ℤ) :
      (row U i).Exact :=
    (H.homologySequenceComposableArrows₅_exact U hU (i - 1) i (by omega)).δ₀
  have sq₁ (i : ℤ) : (homologyFunctor A i).map source.mor₁ ≫ (homologyFunctor A i).map φ.hom₂ =
      (homologyFunctor A i).map φ.hom₁ ≫ (homologyFunctor A i).map target.mor₁ := by
    simpa only [← Functor.map_comp] using congrArg ((homologyFunctor A i).map) φ.comm₁
  have sq₂ (i : ℤ) : (homologyFunctor A i).map source.mor₂ ≫ (homologyFunctor A i).map φ.hom₃ =
      (homologyFunctor A i).map φ.hom₂ ≫ (homologyFunctor A i).map target.mor₂ := by
    simpa only [← Functor.map_comp] using congrArg ((homologyFunctor A i).map) φ.comm₂
  have mono_of (X : Plus A)
      (h : (∀ i ≤ n, IsIso ((homologyFunctor A i).map (α.app X))) ∧
        Mono ((homologyFunctor A (n + 1)).map (α.app X))) (i : ℤ) (hi : i ≤ n + 1) :
      Mono ((homologyFunctor A i).map (α.app X)) := by
    by_cases hle : i ≤ n
    · have := h.1 i hle
      infer_instance
    · obtain rfl : i = n + 1 := by omega
      exact h.2
  have epi_of (i : ℤ) (hi : i ≤ n + 1) :
      Epi ((homologyFunctor A (i - 1)).map (α.app T.obj₃)) := by
    have := hthird.1 (i - 1) (by omega)
    infer_instance
  let diagram (i : ℤ) : row source i ⟶ row target i :=
    ComposableArrows.homMk₄
      ((homologyFunctor A (i - 1)).map φ.hom₂)
      ((homologyFunctor A (i - 1)).map φ.hom₃)
      ((homologyFunctor A i).map φ.hom₁)
      ((homologyFunctor A i).map φ.hom₂)
      ((homologyFunctor A i).map φ.hom₃)
      (sq₂ (i - 1))
      (H.homologySequenceδ_naturality φ (i - 1) i (by omega)).symm
      (sq₁ i)
      (sq₂ i)
  have hmono (i : ℤ) (hi : i ≤ n + 1) :
      Mono ((homologyFunctor A i).map (α.app T.obj₂)) := by
    exact Abelian.mono_of_epi_of_mono_of_mono
      (ComposableArrows.δ₀Functor.map (diagram i))
      (hexact source hs i).δ₀ (hexact target ht i).δ₀
      (epi_of i hi) (mono_of _ hfirst i hi) (mono_of _ hthird i hi)
  refine ⟨fun i hi ↦ ?_, hmono (n + 1) le_rfl⟩
  have hnext := mono_of _ hfirst (i + 1) (by omega)
  let longerRow (U : Triangle (Plus A)) :=
    ComposableArrows.mk₄ (H.homologySequenceδ U (i - 1) i (by omega))
      ((homologyFunctor A i).map U.mor₁)
      ((homologyFunctor A i).map U.mor₂)
      (H.homologySequenceδ U i (i + 1) rfl)
  have longerExact (U : Triangle (Plus A)) (hU : U ∈ distTriang _) :
      (longerRow U).Exact :=
    ComposableArrows.exact_of_δ₀
      (H.homologySequence_exact₁ U hU (i - 1) i (by omega)).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (H.homologySequence_exact₂ U hU i).exact_toComposableArrows
        (H.homologySequence_exact₃ U hU i (i + 1) rfl).exact_toComposableArrows)
  let ψ : longerRow source ⟶ longerRow target :=
    ComposableArrows.homMk₄
      ((homologyFunctor A (i - 1)).map φ.hom₃)
      ((homologyFunctor A i).map φ.hom₁)
      ((homologyFunctor A i).map φ.hom₂)
      ((homologyFunctor A i).map φ.hom₃)
      ((homologyFunctor A (i + 1)).map φ.hom₁)
      (H.homologySequenceδ_naturality φ (i - 1) i (by omega)).symm
      (sq₁ i)
      (sq₂ i)
      (H.homologySequenceδ_naturality φ i (i + 1) rfl).symm
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    (longerExact source hs) (longerExact target ht) ψ
    (epi_of i (by omega)) (hfirst.1 i hi) (hthird.1 i hi) hnext

/-- **The dévissage.** Let `F` be a triangulated endofunctor of `D⁺(A)` commuting with the shift
and `α : 𝟭 ⟶ F` a natural transformation commuting with the shift, and let `P` be an
isomorphism-closed class of objects of `A` containing a zero object. Suppose that for every `M`
in `P` and every `a ≥ 0` the comparison `H^i(α)` at `M` placed in degree `a` is invertible for
`i ≤ n` and monomorphic in degree `n + 1`. Then the same holds at every object of `D⁺(A)` whose
cohomology lies in `P` and is concentrated in a window `[a, a + width]` with `a ≥ 0`. -/
theorem isIso_homology_comparison_of_bounded
    (F : Plus A ⥤ Plus A) [F.CommShift ℤ] [F.IsTriangulated]
    (α : 𝟭 (Plus A) ⟶ F) [NatTrans.CommShift α ℤ]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms] (n : ℤ)
    (hsingle : ∀ M : A, P M → ∀ a : ℤ, 0 ≤ a →
      (∀ i ≤ n, IsIso ((homologyFunctor A i).map
        (α.app ((singleFunctor A a).obj M)))) ∧
      Mono ((homologyFunctor A (n + 1)).map (α.app ((singleFunctor A a).obj M))))
    (width : ℕ) (a : ℤ) (ha : 0 ≤ a) (K : Plus A)
    [K.IsGE a] [K.IsLE (a + width)]
    (hK : ∀ i : ℤ, P ((homologyFunctor A i).obj K)) :
    (∀ i ≤ n, IsIso ((homologyFunctor A i).map (α.app K))) ∧
      Mono ((homologyFunctor A (n + 1)).map (α.app K)) := by
  have hpure (N : Plus A) (b : ℤ) (hb : 0 ≤ b) [N.IsGE b] [N.IsLE b]
      (hN : P ((homologyFunctor A b).obj N)) :
      (∀ i ≤ n, IsIso ((homologyFunctor A i).map (α.app N))) ∧
        Mono ((homologyFunctor A (n + 1)).map (α.app N)) := by
    obtain ⟨M, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE N b
    have hM : P M := P.prop_of_iso
      ((homologyFunctor A b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso b).app M) hN
    have h := hsingle M hM b hb
    refine ⟨fun i hi ↦ (NatTrans.isIso_app_iff_of_iso
      (Functor.whiskerRight α (homologyFunctor A i)) e).2 (h.1 i hi), ?_⟩
    have hmono : Mono ((homologyFunctor A (n + 1)).map
      (α.app ((singleFunctor A b).obj M))) := h.2
    have eqn := congrArg ((homologyFunctor A (n + 1)).map) (α.naturality e.hom)
    simp only [Functor.map_comp, Functor.id_map] at eqn
    have hcomp : Mono ((homologyFunctor A (n + 1)).map e.hom ≫
        (homologyFunctor A (n + 1)).map
          (α.app ((singleFunctor A b).obj M))) := inferInstance
    rw [eqn] at hcomp
    exact mono_of_mono ((homologyFunctor A (n + 1)).map (α.app N))
      ((homologyFunctor A (n + 1)).map (F.map e.hom))
  induction width generalizing a K with
  | zero =>
    have hzero : K.IsLE (a + ((0 : ℕ) : ℤ)) := inferInstance
    have : K.IsLE a := by simpa using hzero
    exact hpure K a ha (hK a)
  | succ width ih =>
    have hsucc : K.IsLE (a + ((width + 1 : ℕ) : ℤ)) := inferInstance
    have hKLE : K.IsLE (a + 1 + (width : ℤ)) :=
      TStructure.t.isLE_of_le K (a + ((width + 1 : ℕ) : ℤ)) (a + 1 + (width : ℤ))
        (by push_cast; omega)
    refine isIso_homology_comparison_of_triangle F α ((TStructure.t.triangleLEGT a).obj K)
      (TStructure.t.triangleLEGT_distinguished a K) n ?_ ?_
    · exact hpure ((TStructure.t.truncLE a).obj K) a ha
        (prop_homology_truncLE_obj P K a (fun i _ ↦ hK i) a)
    · exact ih (a + 1) (by omega) ((TStructure.t.truncGT a).obj K)
        (prop_homology_truncGT_obj P K a fun i _ ↦ hK i)

end Devissage

section Functors

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory B]

/-- **An exact functor preserves invertibility on cohomology in a fixed degree**, for its action
`CategoryTheory.Functor.mapDerivedCategoryPlus` on bounded below derived categories. -/
theorem isIso_homology_mapDerivedCategoryPlus_map (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : Plus A} (f : K ⟶ L) (i : ℤ)
    (hf : IsIso ((homologyFunctor A i).map f)) :
    IsIso ((homologyFunctor B i).map (F.mapDerivedCategoryPlus.map f)) := by
  have hι : IsIso ((DerivedCategory.homologyFunctor A i).map (ι.map f)) := hf
  have hFι : IsIso (F.map ((DerivedCategory.homologyFunctor A i).map (ι.map f))) := by
    infer_instance
  exact (F.isIso_homologyFunctor_map_mapDerivedCategory_map_iff (ι.map f) i).2 hFι

/-- A functor sending `τ_{≤n}K ⟶ K` and `τ_{≤n}L ⟶ L` to isomorphisms sends `τ_{≤n}f` to an
isomorphism if and only if it sends `f` to one. -/
private theorem isIso_map_truncLE_map_iff_of_isIso_map_truncLEι {C : Type*} [Category C]
    (G : Plus A ⥤ C) {K L : Plus A} (f : K ⟶ L) {n : ℤ}
    (hK : IsIso (G.map ((TStructure.t.truncLEι n).app K)))
    (hL : IsIso (G.map ((TStructure.t.truncLEι n).app L))) :
    IsIso (G.map ((TStructure.t.truncLE n).map f)) ↔ IsIso (G.map f) := by
  have hsq : G.map ((TStructure.t.truncLE n).map f) ≫ G.map ((TStructure.t.truncLEι n).app L) =
      G.map ((TStructure.t.truncLEι n).app K) ≫ G.map f := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg G.map ((TStructure.t.truncLEι n).naturality f)
  constructor
  · intro h
    have : IsIso (G.map ((TStructure.t.truncLEι n).app K) ≫ G.map f) := by
      rw [← hsq]
      infer_instance
    exact IsIso.of_isIso_comp_left (G.map ((TStructure.t.truncLEι n).app K)) (G.map f)
  · intro h
    have : IsIso (G.map ((TStructure.t.truncLE n).map f) ≫
        G.map ((TStructure.t.truncLEι n).app L)) := by
      rw [hsq]
      infer_instance
    exact IsIso.of_isIso_comp_right (G.map ((TStructure.t.truncLE n).map f))
      (G.map ((TStructure.t.truncLEι n).app L))

variable [EnoughInjectives A]

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-- **A total right derived functor carries the truncation `τ_{≤n}K ⟶ K` to a morphism
invertible on cohomology in every degree `≤ n`.** -/
theorem isIso_homology_rightDerivedFunctorPlus_map_truncLEι_app
    (F : A ⥤ B) [F.Additive] (K : Plus A) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((homologyFunctor B i).map
      (F.rightDerivedFunctorPlus.map ((TStructure.t.truncLEι n).app K))) := by
  have hGE : (F.rightDerivedFunctorPlus.obj ((TStructure.t.truncGT n).obj K)).IsGE (n + 1) :=
    Functor.isGE_rightDerivedFunctorPlus_obj F _ (n + 1)
  exact isIso_homologyMap_mor₁_of_isGE₃
    (F.rightDerivedFunctorPlus.mapTriangle.obj ((TStructure.t.triangleLEGT n).obj K))
    (F.rightDerivedFunctorPlus.map_distinguished _
      (TStructure.t.triangleLEGT_distinguished n K)) i (n + 1) hGE (by omega)

/-- **A total right derived functor carries a morphism invertible on cohomology in all degrees
`≤ n` to one invertible on cohomology in degree `n`.** -/
theorem isIso_homology_rightDerivedFunctorPlus_map_of_isIso_homology_le
    (F : A ⥤ B) [F.Additive] {K L : Plus A} (f : K ⟶ L) (n : ℤ)
    (hf : ∀ i : ℤ, i ≤ n → IsIso ((homologyFunctor A i).map f)) :
    IsIso ((homologyFunctor B n).map (F.rightDerivedFunctorPlus.map f)) := by
  have hcut : IsIso ((TStructure.t.truncLE n).map f) := by
    refine (isIso_iff _).2 fun i ↦ ?_
    by_cases hi : i ≤ n
    · exact (isIso_map_truncLE_map_iff_of_isIso_map_truncLEι (homologyFunctor A i) f
        (isIso_homologyMap_truncLEι_app K i n hi) (isIso_homologyMap_truncLEι_app L i n hi)).2
        (hf i hi)
    · apply IsZero.isIso
      · exact isZero_homology_truncLE_obj K i n (by omega)
      · exact isZero_homology_truncLE_obj L i n (by omega)
  exact (isIso_map_truncLE_map_iff_of_isIso_map_truncLEι
    (F.rightDerivedFunctorPlus ⋙ homologyFunctor B n) f
    (isIso_homology_rightDerivedFunctorPlus_map_truncLEι_app F K n n le_rfl)
    (isIso_homology_rightDerivedFunctorPlus_map_truncLEι_app F L n n le_rfl)).1 inferInstance

end Functors

end DerivedCategory.Plus

end
