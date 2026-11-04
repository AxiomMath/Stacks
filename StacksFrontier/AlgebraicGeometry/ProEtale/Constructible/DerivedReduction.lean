module

public import StacksCore.Algebra.Category.ModuleCat.Localization
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.DerivedTensor
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Constant
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces
import StacksCore.Tactic.StacksAttribute

/-!
# Reductions modulo powers of an ideal of constructible pro-étale complexes

Let `X` be a scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. For `K` in `D(X_proét, Λ)` set
`Kₙ = K ⊗_Λ^L Λ/Iⁿ`, an object of `D(X_proét, Λ/Iⁿ)`. If `K₁` lies in
`D_c^-(X_proét, Λ/I)` — it is bounded above and its cohomology sheaves are constructible — then
`Kₙ` lies in `D_c^-(X_proét, Λ/Iⁿ)` for every `n` (Stacks 09BR).

## Main results

* `minus_and_isConstructibleModuleSheaf'_homology_restrictScalars_iff`: membership in `D_c^-` is
  detected after restriction of scalars along a surjective ring map.
* `minus_and_isConstructibleModuleSheaf'_homology_tensor_of_annihilated`: `M ⊗_Λ^L K` lies in
  `D_c^-(X_proét, Λ)` for every finitely generated `Λ`-module `M` killed by `I`.
* `minus_and_isConstructibleModuleSheaf'_homology_derivedExtendScalars`: if `K₁` lies in
  `D_c^-(X_proét, Λ/I)`, then `Kₙ` lies in `D_c^-(X_proét, Λ/Iⁿ)` for every `n`.

## Implementation notes

`Kₙ` is the derived extension of scalars `Stacks.ModuleSheaf.derivedExtendScalars` along
`Λ → Λ/Iⁿ`, which is the derived tensor product `K ⊗_Λ^L Λ/Iⁿ` regarded as an object over
`Λ/Iⁿ`: read over `Λ` it is `Λ/Iⁿ ⊗_Λ^L K`
(`Stacks.ModuleSheaf.nonempty_restrictScalars_derivedExtendScalars_iso`).

The proof is the source's. Read over `Λ`, the objects `Λ/Iⁿ ⊗_Λ^L K` sit in the distinguished
triangles obtained by tensoring the short exact sequences
`0 → Iⁿ/Iⁿ⁺¹ → Λ/Iⁿ⁺¹ → Λ/Iⁿ → 0` with `K`, the first one written here as the kernel of
`Λ/Iⁿ⁺¹ → Λ/Iⁿ`. Its first vertex is `M ⊗_Λ^L K` for a finitely generated `Λ/I`-module `M`, which
is `M ⊗_{Λ/I}^L K₁` read over `Λ` by the derived projection formula
(`Stacks.ModuleSheaf.nonempty_restrictScalars_tensor_derivedExtendScalars_iso`), so lies in
`D_c^-` by Tag 09BQ. Since constructible sheaves form a weak Serre subcategory (Tag 09B5),
`D_c^-(X_proét, Λ)` is closed under extensions, and the induction on `n` goes through over
`Λ`. Finally membership in `D_c^-` can be tested after restriction of scalars along the
surjection `Λ → Λ/Iⁿ`: restriction of scalars is exact and faithful, and constructibility is
detected by it (`AlgebraicGeometry.ProEtale.isConstructibleModuleSheaf'_restrictScalars_iff`).

All coefficient rings live in the universe `max (u + 1) w` of the module sections, as for Tag
09BQ.

## References

* [Stacks Project, Tag 09BR](https://stacks.math.columbia.edu/tag/09BR)
* [Stacks Project, Tag 09BQ](https://stacks.math.columbia.edu/tag/09BQ)
* [Stacks Project, Tag 09B5](https://stacks.math.columbia.edu/tag/09B5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Stacks.ModuleSheaf

universe t t' t'' w u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Sheaf.monoidalCategory derivedMonoidal

variable {X : Scheme.{u}}

/-! ### Change of rings -/

section ChangeOfRings

variable {Λ S : Type (max (u + 1) w)} [CommRing Λ] [CommRing S] [IsNoetherianRing Λ]
  [IsNoetherianRing S] {f : Λ →+* S}
  [HasDerivedCategory.{t} (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))]
  [HasDerivedCategory.{t'} (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} S))]

/-- **Membership in `D_c^-` is detected by restriction of scalars along a surjective ring
map**: an object of `D(X_proét, S)` is bounded above with constructible cohomology sheaves
exactly when it is so as an object of `D(X_proét, Λ)`. -/
theorem minus_and_isConstructibleModuleSheaf'_homology_restrictScalars_iff
    (hf : Function.Surjective f)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} S))) :
    (DerivedCategory.TStructure.t.minus
        ((restrictScalars (Scheme.ProEt.topology X) f).mapDerivedCategory.obj L) ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
        ((DerivedCategory.homologyFunctor _ i).obj
          ((restrictScalars (Scheme.ProEt.topology X) f).mapDerivedCategory.obj L))) ↔
      (DerivedCategory.TStructure.t.minus L ∧
        ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X S
          ((DerivedCategory.homologyFunctor _ i).obj L)) := by
  let R := restrictScalars (Scheme.ProEt.topology X) f
  have := isWeakSerreClass_isConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
  let e : ∀ i, (DerivedCategory.homologyFunctor _ i).obj (R.mapDerivedCategory.obj L) ≅
      R.obj ((DerivedCategory.homologyFunctor _ i).obj L) :=
    fun i => (R.mapDerivedCategoryHomologyIso i).app L
  have hz : ∀ F, IsZero (R.obj F) ↔ IsZero F := fun F => ⟨fun h => by
    rw [IsZero.iff_id_eq_zero] at h ⊢
    exact R.map_injective (by rw [R.map_id, h, R.map_zero]), R.map_isZero⟩
  have hle : ∀ n, (R.mapDerivedCategory.obj L).IsLE n ↔ L.IsLE n := fun n => by
    simp only [DerivedCategory.isLE_iff]
    exact forall₂_congr fun i _ => (Iso.isZero_iff (e i)).trans (hz _)
  refine and_congr ⟨fun ⟨n, h⟩ => ⟨n, (hle n).1 h⟩, fun ⟨n, h⟩ => ⟨n, (hle n).2 h⟩⟩
    (forall_congr' fun i => ?_)
  rw [ObjectProperty.prop_iff_of_iso (fun F => IsConstructibleModuleSheaf'.{u, max (u + 1) w, w}
    X Λ F) (e i)]
  exact isConstructibleModuleSheaf'_restrictScalars_iff hf _

end ChangeOfRings

/-! ### The reduction modulo powers of `I` -/

section Reduction

variable {Λ : Type (max (u + 1) w)} [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ)
  [HasDerivedCategory.{t} (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))]

/-- `D_c^-(X_proét, Λ)` is closed under extensions: in a distinguished triangle whose outer
vertices are bounded above with constructible cohomology sheaves, so is the middle vertex. -/
theorem minus_and_isConstructibleModuleSheaf'_homology_obj₂
    (T : Pretriangulated.Triangle
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))))
    (hT : T ∈ distTriang _)
    (h₁ : DerivedCategory.TStructure.t.minus T.obj₁ ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
        ((DerivedCategory.homologyFunctor _ i).obj T.obj₁))
    (h₃ : DerivedCategory.TStructure.t.minus T.obj₃ ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
        ((DerivedCategory.homologyFunctor _ i).obj T.obj₃)) :
    DerivedCategory.TStructure.t.minus T.obj₂ ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
        ((DerivedCategory.homologyFunctor _ i).obj T.obj₂) := by
  have := isWeakSerreClass_isConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
  exact ⟨DerivedCategory.TStructure.t.minus.ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1,
    DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _) T hT h₁.2 h₃.2⟩

/-- Membership in `D_c^-(X_proét, Λ)` is invariant under isomorphism. -/
private theorem minus_and_isConstructibleModuleSheaf'_homology_of_iso
    {A B : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))}
    (e : A ≅ B)
    (h : DerivedCategory.TStructure.t.minus A ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
        ((DerivedCategory.homologyFunctor _ i).obj A)) :
    DerivedCategory.TStructure.t.minus B ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
        ((DerivedCategory.homologyFunctor _ i).obj B) := by
  have := isWeakSerreClass_isConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
  exact ⟨DerivedCategory.TStructure.t.minus.prop_of_iso e h.1, fun i =>
    ObjectProperty.prop_of_iso _ ((DerivedCategory.homologyFunctor _ i).mapIso e) (h.2 i)⟩

variable [HasDerivedCategory.{t'}
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} (Λ ⧸ I)))]

/-- **The graded pieces.** If `K ⊗_Λ^L Λ/I` lies in `D_c^-(X_proét, Λ/I)`, then for every
finitely generated `Λ`-module `M` killed by `I`, the derived tensor product `M ⊗_Λ^L K` lies in
`D_c^-(X_proét, Λ)`: regarding `M` as a `Λ/I`-module, it is `M ⊗_{Λ/I}^L (K ⊗_Λ^L Λ/I)` read
over `Λ`, by the projection formula, and Tag 09BQ applies over `Λ/I`. -/
theorem minus_and_isConstructibleModuleSheaf'_homology_tensor_of_annihilated
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (hK : DerivedCategory.TStructure.t.minus
        ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K) ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X (Λ ⧸ I)
        ((DerivedCategory.homologyFunctor _ i).obj
          ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K)))
    (M : ModuleCat.{max (u + 1) w} Λ) (hM : ModuleCat.isFG Λ M)
    (hkill : Module.IsTorsionBySet Λ M I) :
    DerivedCategory.TStructure.t.minus
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology X) _).obj M) ⊗ K) ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
        ((DerivedCategory.homologyFunctor _ i).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf (Scheme.ProEt.topology X) _).obj M) ⊗ K)) := by
  let J := Scheme.ProEt.topology X
  let π := Ideal.Quotient.mk I
  let R := restrictScalars J π
  let : Module (Λ ⧸ I) M := hkill.module
  let M' : ModuleCat.{max (u + 1) w} (Λ ⧸ I) := ModuleCat.of (Λ ⧸ I) M
  let eM : (ModuleCat.restrictScalars π).obj M' ≅ M :=
    LinearEquiv.toModuleIso
      { toFun := fun x => x
        invFun := fun x => x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hM' : ModuleCat.isFG (Λ ⧸ I) M' := by
    rw [ModuleCat.isFG_iff] at hM ⊢
    exact Module.Finite.of_restrictScalars_finite Λ (Λ ⧸ I) M
  let L₁ : DerivedCategory (Sheaf J (ModuleCat.{max (u + 1) w} (Λ ⧸ I))) :=
    (DerivedCategory.singleFunctor _ 0).obj ((constantSheaf J _).obj M')
  have hL₁ : DerivedCategory.TStructure.t.minus L₁ ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X (Λ ⧸ I)
        ((DerivedCategory.homologyFunctor _ i).obj L₁) := by
    have := isWeakSerreClass_isConstructibleModuleSheaf'.{u, max (u + 1) w, w} X (Λ ⧸ I)
    exact ⟨⟨0, inferInstanceAs (L₁.IsLE 0)⟩,
      (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _
        (WeakSerre.isWeakSerre_of_isWeakSerreClass _) _
        (isConstructibleModuleSheaf'_constantSheaf M' hM')).2⟩
  obtain ⟨e⟩ := nonempty_restrictScalars_tensor_derivedExtendScalars_iso π L₁ K
  let e' : (DerivedCategory.singleFunctor _ 0).obj ((constantSheaf J _).obj M) ⊗ K ≅
      R.mapDerivedCategory.obj (L₁ ⊗ (derivedExtendScalars J π).obj K) :=
    ((DerivedCategory.singleFunctor _ 0).mapIso ((constantSheaf J _).mapIso eM.symm ≪≫
      ((restrictScalarsConstantSheafIso J π).app M').symm) ≪≫
      ((R.mapDerivedCategorySingleFunctor 0).app _).symm ⊗ᵢ Iso.refl K) ≪≫ e.symm
  have h := (minus_and_isConstructibleModuleSheaf'_homology_restrictScalars_iff
    (Ideal.Quotient.mk_surjective (I := I)) _).2
    (minus_tensor_and_isConstructibleModuleSheaf'_homology L₁ _ hL₁.1 hK.1 hL₁.2 hK.2)
  exact minus_and_isConstructibleModuleSheaf'_homology_of_iso e'.symm h

variable [∀ n : ℕ, HasDerivedCategory.{t''}
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ n)))]

omit [∀ n : ℕ, HasDerivedCategory.{t''}
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ n)))] in
/-- **The induction on `n`**: if `K ⊗_Λ^L Λ/I` lies in `D_c^-(X_proét, Λ/I)`, then
`Λ/Iⁿ ⊗_Λ^L K` lies in `D_c^-(X_proét, Λ)` for every `n`. -/
theorem minus_and_isConstructibleModuleSheaf'_homology_tensor_quotient_pow
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (hK : DerivedCategory.TStructure.t.minus
        ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K) ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X (Λ ⧸ I)
        ((DerivedCategory.homologyFunctor _ i).obj
          ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K)))
    (n : ℕ) :
    DerivedCategory.TStructure.t.minus
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology X) _).obj
            (ModuleCat.of Λ (Λ ⧸ I ^ n))) ⊗ K) ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
        ((DerivedCategory.homologyFunctor _ i).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf (Scheme.ProEt.topology X) _).obj
              (ModuleCat.of Λ (Λ ⧸ I ^ n))) ⊗ K)) := by
  obtain ⟨s, hs⟩ := exists_commShift_isTriangulated_tensorRight (Scheme.ProEt.topology X) Λ K
  let := s
  induction n with
  | zero =>
    have : Subsingleton (Λ ⧸ I ^ 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])
    have hz : IsZero ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Scheme.ProEt.topology X) _).obj
          (ModuleCat.of Λ (Λ ⧸ I ^ 0))) ⊗ K) :=
      (tensorRight K).map_isZero (Functor.map_isZero _ (Functor.map_isZero _
        (@ModuleCat.isZero_of_subsingleton _ _ _ this)))
    exact ⟨⟨0, DerivedCategory.TStructure.t.isLE_of_isZero hz 0⟩, fun i =>
      isConstructibleModuleSheaf'_of_isZero ((DerivedCategory.homologyFunctor _ i).map_isZero hz)⟩
  | succ n ih =>
    obtain ⟨a, b, c, hT⟩ := Stacks.ConstantSheaf.exists_distTriang_map_singleTriangle
      (tensorRight K) ((Stacks.ConstantSheaf.idealPowShortComplex Λ I n).map
        (constantSheaf (Scheme.ProEt.topology X) _))
      ((Stacks.ConstantSheaf.shortExact_idealPowShortComplex Λ I n).map_of_exact _)
    exact minus_and_isConstructibleModuleSheaf'_homology_obj₂ _ hT
      (minus_and_isConstructibleModuleSheaf'_homology_tensor_of_annihilated I K hK _
        (Stacks.ConstantSheaf.isFG_idealPowSuccQuot Λ I n)
        (fun x a => Stacks.ConstantSheaf.smul_eq_zero_idealPowSuccQuot Λ I n a a.2 x)) ih

/-- **Stacks 09BR.** Let `X` be a scheme, `Λ` a Noetherian ring, `I ⊆ Λ` an ideal and `K` an
object of `D(X_proét, Λ)`. Set `Kₙ = K ⊗_Λ^L Λ/Iⁿ`, the derived extension of scalars of `K` along
`Λ → Λ/Iⁿ`. If `K₁` lies in `D_c^-(X_proét, Λ/I)`, that is, it is bounded above and its
cohomology sheaves are constructible, then `Kₙ` lies in `D_c^-(X_proét, Λ/Iⁿ)` for all `n`. -/
@[stacks 09BR]
theorem minus_and_isConstructibleModuleSheaf'_homology_derivedExtendScalars
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (hK : DerivedCategory.TStructure.t.minus
        ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K) ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X (Λ ⧸ I)
        ((DerivedCategory.homologyFunctor _ i).obj
          ((derivedExtendScalars _ (Ideal.Quotient.mk I)).obj K)))
    (n : ℕ) :
    DerivedCategory.TStructure.t.minus
        ((derivedExtendScalars _ (Ideal.Quotient.mk (I ^ n))).obj K) ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X (Λ ⧸ I ^ n)
        ((DerivedCategory.homologyFunctor _ i).obj
          ((derivedExtendScalars _ (Ideal.Quotient.mk (I ^ n))).obj K)) := by
  obtain ⟨e⟩ := nonempty_restrictScalars_derivedExtendScalars_iso (Ideal.Quotient.mk (I ^ n)) K
  rw [← minus_and_isConstructibleModuleSheaf'_homology_restrictScalars_iff
    (Ideal.Quotient.mk_surjective (I := I ^ n))]
  have h := minus_and_isConstructibleModuleSheaf'_homology_tensor_quotient_pow I K hK n
  let e' := e ≪≫ ((DerivedCategory.singleFunctor _ 0).mapIso
    ((constantSheaf (Scheme.ProEt.topology X) _).mapIso
      (ModuleCat.restrictScalarsAlgebraMapIso (R := Λ) (ModuleCat.of (Λ ⧸ I ^ n) (Λ ⧸ I ^ n))))
    ⊗ᵢ Iso.refl K)
  exact minus_and_isConstructibleModuleSheaf'_homology_of_iso e'.symm h

end Reduction

end AlgebraicGeometry.ProEtale
