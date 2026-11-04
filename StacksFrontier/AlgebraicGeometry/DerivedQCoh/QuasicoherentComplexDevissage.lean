module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.QcohUniversalDeltaFunctor

/-!
# Dévissage on the derived category of quasi-coherent modules

Let `X` be a quasi-compact scheme with affine diagonal, and let `α : F ⟶ G` be a natural
transformation between two triangulated functors `D(QCoh(𝒪_X)) ⥤ D(𝓑)`. This file proves that
`α` is an isomorphism as soon as it is one at every complex `j_*𝒢^•`, where `j : U ⟶ X` is the
inclusion of an affine open and `𝒢^•` is a complex of quasi-coherent `𝒪_U`-modules.

This is the dévissage in the proof of [Stacks, Tag 0CRX]. Let `𝓕^•` be a complex of
quasi-coherent `𝒪_X`-modules, cover `X` by finitely many affine opens `U₁, …, Uₙ` and let
`c : 𝓕^• ⟶ j_*j^*𝓕^•` be the unit for `U = U₁`. The kernel and cokernel of `c` vanish on `U₁`,
and they vanish on every `Uᵢ` on which `𝓕^•` does; the two short exact sequences
`0 ⟶ Ker(c) ⟶ 𝓕^• ⟶ Im(c) ⟶ 0` and `0 ⟶ Im(c) ⟶ j_*j^*𝓕^• ⟶ Coker(c) ⟶ 0` give distinguished
triangles, and the property "`α` is invertible at every shift" has the two-out-of-three property
on distinguished triangles. An induction on the number of opens on which the complex does not yet
vanish ends at a complex vanishing on a cover, which is zero.

## Main results

* `Stacks.DerivedQCoh.isIso_natTrans_of_isIso_app_quasicoherentPushforward` — the dévissage.

## Implementation notes

The two-out-of-three step does not ask `α` to commute with translation: it is the five lemma
applied, cohomology sheaf by cohomology sheaf, to the long exact sequences of the images of a
distinguished triangle under `F` and `G`, and the price is that the property carried by the
induction is invertibility of `α` at *every* shift of a complex.

## References

* [Stacks Project, Tag 0CRX](https://stacks.math.columbia.edu/tag/0CRX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u

namespace Stacks.DerivedQCoh

/-! ### Vanishing of a module on the opens of a cover -/

section Vanishing

/-- A module on a scheme vanishes exactly when all of its modules of sections do. -/
theorem isZero_schemeModules_iff (X : Scheme.{u}) (M : X.Modules) :
    IsZero M ↔ ∀ V : X.Opens, IsZero Γ(M, V) := by
  constructor
  · intro h V
    let : ((Scheme.Modules.toPresheaf X) ⋙
        (evaluation _ _).obj (.op V)).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
    exact ((Scheme.Modules.toPresheaf X) ⋙ (evaluation _ _).obj (.op V)).map_isZero h
  · intro h
    apply (IsZero.iff_id_eq_zero M).2
    apply Scheme.Modules.hom_ext
    intro V
    exact (h V).eq_of_src _ _

/-- The restriction of a module to an open `U` vanishes exactly when its sections over every open
contained in `U` do. -/
theorem isZero_restrict_iff {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    IsZero (M.restrict U.ι) ↔ ∀ V : X.Opens, V ≤ U → IsZero Γ(M, V) := by
  rw [isZero_schemeModules_iff]
  constructor
  · intro h V hV
    have := (h (U.ι ⁻¹ᵁ V)).of_iso (M.restrictAppIso U.ι (U.ι ⁻¹ᵁ V)).symm
    simpa [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_of_le_right hV] using this
  · intro h V
    refine (h _ ?_).of_iso (M.restrictAppIso U.ι V)
    simpa using U.ι.image_le_opensRange V

/-- If a module vanishes on an open `V`, so does its direct image from any open `U` of its
restriction to `U`. -/
theorem isZero_restrict_pushforward_restrict {X : Scheme.{u}}
    (M : X.Modules) (U V : X.Opens) (h : IsZero (M.restrict V.ι)) :
    IsZero (((Scheme.Modules.pushforward U.ι).obj (M.restrict U.ι)).restrict V.ι) := by
  rw [isZero_restrict_iff] at h ⊢
  intro W hW
  rw [Scheme.Modules.pushforward_obj_obj]
  exact (h _ ((U.ι.image_preimage_le W).trans hW)).of_iso (M.restrictAppIso U.ι (U.ι ⁻¹ᵁ W))

/-- A module vanishing on every open of a cover vanishes. -/
theorem isZero_schemeModules_of_cover {X : Scheme.{u}} (M : X.Modules)
    {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, IsZero (M.restrict (U i).ι)) : IsZero M := by
  apply (isZero_schemeModules_iff X M).2
  intro V
  apply (IsZero.iff_id_eq_zero _).2
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply M.isSheaf.section_ext
  intro x hx
  have hxU : x ∈ iSup U := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
  refine ⟨V ⊓ U i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  simpa using ConcreteCategory.congr_hom
    (((isZero_restrict_iff M (U i)).1 (h i) (V ⊓ U i) inf_le_right).eq_of_src (𝟙 _) 0)
    (M.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op s)

/-- The unit `M ⟶ j_*j^*M` of restriction to an open becomes invertible after restriction. -/
theorem isIso_restrictFunctor_map_restrictAdjunction_unit {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) ≫
      (Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.restrictFunctor U.ι).obj M)) := by
    rw [(Scheme.Modules.restrictAdjunction U.ι).left_triangle_components M]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.restrictAdjunction U.ι).counit.app
      ((Scheme.Modules.restrictFunctor U.ι).obj M))

end Vanishing

/-! ### Restriction of complexes of quasi-coherent modules -/

section Restriction

variable {X : Scheme.{u}}

/-- The unit `𝓕 ⟶ j_*j^*𝓕` of restriction of quasi-coherent modules to an open `U`. -/
def quasicoherentRestrictUnit (U : X.Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι] :
    𝟭 (Scheme.QuasicoherentModules X) ⟶
      quasicoherentRestrict U ⋙ quasicoherentPushforward U.ι where
  app M := ObjectProperty.homMk ((Scheme.Modules.restrictAdjunction U.ι).unit.app M.obj)
  naturality M N g := by
    apply (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map_injective
    exact (Scheme.Modules.restrictAdjunction U.ι).unit.naturality g.hom

/-- A quasi-coherent module restricts to zero on `U` exactly when the underlying module does. -/
theorem isZero_quasicoherentRestrict_obj_iff (U : X.Opens) (M : Scheme.QuasicoherentModules X) :
    IsZero ((quasicoherentRestrict U).obj M) ↔ IsZero (Scheme.Modules.restrict M.obj U.ι) := by
  let J := (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι
  exact ⟨fun h => J.map_isZero h, fun h => IsZero.of_full_of_faithful_of_isZero J _ h⟩

/-- A cochain complex vanishes exactly when each of its terms does. -/
theorem isZero_cochainComplex_iff {A : Type*} [Category* A] [HasZeroMorphisms A]
    (K : CochainComplex A ℤ) : IsZero K ↔ ∀ n, IsZero (K.X n) := by
  constructor
  · intro h n
    exact (HomologicalComplex.eval A (.up ℤ) n).map_isZero h
  · intro h
    apply (IsZero.iff_id_eq_zero K).2
    ext n
    exact (h n).eq_of_src _ _

/-- A complex of quasi-coherent modules restricts to zero on `U` exactly when each of its terms
does. -/
theorem isZero_quasicoherentRestrict_complex_iff (U : X.Opens)
    (K : CochainComplex (Scheme.QuasicoherentModules X) ℤ) :
    IsZero (((quasicoherentRestrict U).mapHomologicalComplex (.up ℤ)).obj K) ↔
      ∀ n, IsZero (Scheme.Modules.restrict (K.X n).obj U.ι) := by
  rw [isZero_cochainComplex_iff]
  exact forall_congr' fun n => isZero_quasicoherentRestrict_obj_iff U (K.X n)

/-- A complex of quasi-coherent modules vanishing on every open of a cover vanishes. -/
private theorem isZero_of_isZero_quasicoherentRestrict_complex {ι : Type*} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (K : CochainComplex (Scheme.QuasicoherentModules X) ℤ)
    (h : ∀ i, IsZero (((quasicoherentRestrict (U i)).mapHomologicalComplex (.up ℤ)).obj K)) :
    IsZero K := by
  refine (isZero_cochainComplex_iff K).2 fun n => ?_
  apply IsZero.of_full_of_faithful_of_isZero (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
  exact isZero_schemeModules_of_cover (K.X n).obj U hU
    fun i => (isZero_quasicoherentRestrict_complex_iff (U i) K).1 (h i) n

/-- If a complex vanishes on `V`, so does `j_*j^*` of it, for `j` the inclusion of any open. -/
theorem isZero_quasicoherentRestrict_complex_pushforward (U V : X.Opens)
    [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (K : CochainComplex (Scheme.QuasicoherentModules X) ℤ)
    (h : IsZero (((quasicoherentRestrict V).mapHomologicalComplex (.up ℤ)).obj K)) :
    IsZero (((quasicoherentRestrict V).mapHomologicalComplex (.up ℤ)).obj
      (((quasicoherentRestrict U ⋙
        quasicoherentPushforward U.ι).mapHomologicalComplex (.up ℤ)).obj K)) := by
  rw [isZero_quasicoherentRestrict_complex_iff] at h ⊢
  intro n
  exact isZero_restrict_pushforward_restrict (K.X n).obj U V (h n)

/-- The unit `𝓕^• ⟶ j_*j^*𝓕^•` becomes invertible after restriction to `U`. -/
theorem isIso_quasicoherentRestrict_map_unit (U : X.Opens)
    [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (K : CochainComplex (Scheme.QuasicoherentModules X) ℤ) :
    IsIso (((quasicoherentRestrict U).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (quasicoherentRestrictUnit U) (.up ℤ)).app K)) := by
  let g := ((quasicoherentRestrict U).mapHomologicalComplex (.up ℤ)).map
    ((NatTrans.mapHomologicalComplex (quasicoherentRestrictUnit U) (.up ℤ)).app K)
  have (n : ℤ) : IsIso (g.f n) := by
    have : IsIso ((SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι.map (g.f n)) :=
      isIso_restrictFunctor_map_restrictAdjunction_unit (K.X n).obj U
    exact isIso_of_reflects_iso (g.f n) (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι
  exact HomologicalComplex.Hom.isIso_of_components g

end Restriction

/-! ### Two out of three, at every shift -/

section TwoOutOfThree

/-- **The induction along a finite family of units.** Let `P` be a property of objects, `Z i` a
family of vanishing conditions and `c i : 𝟭 ⟶ L i` a family of transformations such that `P` holds
on objects satisfying every `Z i`, holds on every `L i K`, and passes from the kernel, the
cokernel and the target of a morphism to its source. If the kernel and cokernel of `c i` satisfy
`Z i`, and satisfy `Z j` whenever their source does, then `P` holds everywhere. -/
theorem property_of_finite_family_of_kernel_cokernel
    {C ι : Type*} [Category* C] [HasZeroMorphisms C] [HasKernels C] [HasCokernels C]
    [Finite ι] (P : C → Prop) (Z : ι → C → Prop)
    (L : ι → C ⥤ C) (c : ∀ i, 𝟭 C ⟶ L i)
    (hzero : ∀ K, (∀ i, Z i K) → P K)
    (hvanish : ∀ i j K, j = i ∨ Z j K →
      Z j (kernel ((c i).app K)) ∧ Z j (cokernel ((c i).app K)))
    (hL : ∀ i K, P ((L i).obj K))
    (hstep : ∀ {K M : C} (f : K ⟶ M), P (kernel f) → P (cokernel f) → P M → P K)
    (K : C) : P K := by
  classical
  let := Fintype.ofFinite ι
  have h (s : Finset ι) : ∀ K, (∀ i, i ∉ s → Z i K) → P K := by
    induction s using Finset.induction_on with
    | empty => exact fun K hK => hzero K (fun i => hK i (Finset.notMem_empty i))
    | @insert i s hi ih =>
      intro K hK
      have hZ : ∀ j, j ∉ s → j = i ∨ Z j K := fun j hj =>
        (em (j = i)).imp_right fun hji => hK j (by simp [hji, hj])
      exact hstep ((c i).app K) (ih _ fun j hj => (hvanish i j K (hZ j hj)).1)
        (ih _ fun j hj => (hvanish i j K (hZ j hj)).2) (hL i K)
  exact h Finset.univ K (by simp)

/-- If a natural transformation `α` is invertible at every translate `X⟦n⟧` of `X`, and `X ≅ Y`,
then `α` is invertible at every translate `Y⟦n⟧` of `Y`. -/
lemma isIso_app_shift_of_iso
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ]
    {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y)
    (hX : ∀ n : ℤ, IsIso (α.app (X⟦n⟧))) (n : ℤ) : IsIso (α.app (Y⟦n⟧)) :=
  (α.isIso_app_iff_of_iso ((shiftFunctor C n).mapIso e)).1 (hX n)

/-- If a natural transformation `α` is invertible at every translate `X⟦n⟧` of `X`, then it is
invertible at every iterated translate `(X⟦a⟧)⟦n⟧`. -/
lemma isIso_app_shift_shift
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ]
    {F G : C ⥤ D} (α : F ⟶ G) {X : C}
    (hX : ∀ n : ℤ, IsIso (α.app (X⟦n⟧))) (a n : ℤ) : IsIso (α.app ((X⟦a⟧)⟦n⟧)) :=
  (α.isIso_app_iff_of_iso ((shiftFunctorAdd C a n).app X)).1 (hX (a + n))

variable {C B : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category* B] [Abelian B] [HasDerivedCategory B]
  {F G : C ⥤ DerivedCategory B} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]

/-- **The five lemma on the cohomology of a distinguished triangle.** A transformation of
triangulated functors into a derived category which is invertible at the first two vertices of a
distinguished triangle and at their translates is invertible at the third vertex. No
compatibility of the transformation with translation is needed. -/
lemma isIso_app₃_of_isIso_app₁₂_shift
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distTriang C)
    [IsIso (α.app T.obj₁)] [IsIso (α.app T.obj₂)]
    [IsIso (α.app (T.obj₁⟦(1 : ℤ)⟧))] [IsIso (α.app (T.obj₂⟦(1 : ℤ)⟧))] :
    IsIso (α.app T.obj₃) := by
  apply (DerivedCategory.isIso_iff B _).2
  intro n
  let H := DerivedCategory.homologyFunctor B n
  let S := ComposableArrows.mk₄ T.mor₁ T.mor₂ T.mor₃ T.rotate.rotate.mor₂
  have hex (L : C ⥤ B) [L.IsHomological] : ComposableArrows.Exact (S ⋙ L) :=
    ComposableArrows.exact_of_δ₀
      (L.map_distinguished_exact T hT).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (L.map_distinguished_exact T.rotate (rot_of_distTriang T hT)).exact_toComposableArrows
        (ComposableArrows.exact₂_mk _ _ (L.map_distinguished_exact T.rotate.rotate
          (rot_of_distTriang _ (rot_of_distTriang T hT)))))
  let φ : S ⋙ F ⋙ H ⟶ S ⋙ G ⋙ H := Functor.whiskerLeft S (Functor.whiskerRight α H)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    (hex (F ⋙ H)) (hex (G ⋙ H)) φ
    (inferInstanceAs (Epi (H.map (α.app T.obj₁))))
    (inferInstanceAs (IsIso (H.map (α.app T.obj₂))))
    (inferInstanceAs (IsIso (H.map (α.app (T.obj₁⟦(1 : ℤ)⟧)))))
    (inferInstanceAs (Mono (H.map (α.app (T.obj₂⟦(1 : ℤ)⟧)))))

/-- Invertibility at every shift passes from the first two vertices of a distinguished triangle
to the third. -/
lemma isIso_app_shift₃_of_isIso_app_shift₁₂
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧)))
    (h₂ : ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) (n : ℤ) :
    IsIso (α.app (T.obj₃⟦n⟧)) := by
  have : IsIso (α.app (T⟦n⟧).obj₁) := h₁ n
  have : IsIso (α.app (T⟦n⟧).obj₂) := h₂ n
  have : IsIso (α.app ((T⟦n⟧).obj₁⟦(1 : ℤ)⟧)) := isIso_app_shift_shift α h₁ n 1
  have : IsIso (α.app ((T⟦n⟧).obj₂⟦(1 : ℤ)⟧)) := isIso_app_shift_shift α h₂ n 1
  exact isIso_app₃_of_isIso_app₁₂_shift α (T⟦n⟧) (Triangle.shift_distinguished T hT n)

/-- Invertibility at every shift passes from the outer vertices of a distinguished triangle to
the middle one. -/
lemma isIso_app_shift₂_of_isIso_app_shift₁₃
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧)))
    (h₃ : ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) (n : ℤ) :
    IsIso (α.app (T.obj₂⟦n⟧)) :=
  isIso_app_shift₃_of_isIso_app_shift₁₂ α T.invRotate (inv_rot_of_distTriang T hT)
    (isIso_app_shift_shift α h₃ (-1)) h₁ n

/-- Invertibility at every shift passes from the last two vertices of a distinguished triangle to
the first. -/
lemma isIso_app_shift₁_of_isIso_app_shift₂₃
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₂ : ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧)))
    (h₃ : ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) (n : ℤ) :
    IsIso (α.app (T.obj₁⟦n⟧)) :=
  isIso_app_shift_of_iso α ((shiftEquiv C (1 : ℤ)).unitIso.symm.app T.obj₁)
    (isIso_app_shift_shift α
      (isIso_app_shift₃_of_isIso_app_shift₁₂ α T.rotate (rot_of_distTriang T hT) h₂ h₃) (-1)) n

end TwoOutOfThree

/-- **Two out of three along a morphism of complexes.** For `c : K ⟶ L` a morphism of cochain
complexes, invertibility of a transformation of triangulated functors at every shift of the
kernel, of the cokernel and of the target of `c` gives it at every shift of the source: the
image of `c` sits in two short exact sequences, whose distinguished triangles do the rest. -/
lemma isIso_app_shift_of_kernel_cokernel
    {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    [Category* B] [Abelian B] [HasDerivedCategory B]
    {F G : DerivedCategory A ⥤ DerivedCategory B}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (α : F ⟶ G) {K L : CochainComplex A ℤ} (c : K ⟶ L)
    (hker : ∀ n : ℤ, IsIso (α.app ((DerivedCategory.Q.obj (kernel c))⟦n⟧)))
    (hcoker : ∀ n : ℤ, IsIso (α.app ((DerivedCategory.Q.obj (cokernel c))⟦n⟧)))
    (hL : ∀ n : ℤ, IsIso (α.app ((DerivedCategory.Q.obj L)⟦n⟧))) (n : ℤ) :
    IsIso (α.app ((DerivedCategory.Q.obj K)⟦n⟧)) := by
  let S₁ := ShortComplex.mk (kernel.ι c) (Abelian.coimage.π c) (by simp)
  have h₁ : S₁.ShortExact :=
    { exact := (ShortComplex.exact_iff_exact_coimage_π _).1 (ShortComplex.exact_kernel c) }
  let S₂ := ShortComplex.mk (Abelian.image.ι c) (cokernel.π c) (by simp)
  have h₂ : S₂.ShortExact :=
    { exact := (ShortComplex.exact_iff_exact_image_ι _).1 (ShortComplex.exact_cokernel c) }
  have hImage := isIso_app_shift₁_of_isIso_app_shift₂₃ α (DerivedCategory.triangleOfSES h₂)
    (DerivedCategory.triangleOfSES_distinguished h₂) hL hcoker
  have hCoimage := isIso_app_shift_of_iso α
    (DerivedCategory.Q.mapIso (Abelian.coimageIsoImage c).symm) hImage
  exact isIso_app_shift₂_of_isIso_app_shift₁₃ α (DerivedCategory.triangleOfSES h₁)
    (DerivedCategory.triangleOfSES_distinguished h₁) hker hCoimage n

/-- An exact functor carrying a morphism to an isomorphism kills its kernel and its cokernel. -/
lemma isZero_map_kernel_cokernel_of_isIso
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : A} (c : K ⟶ L) [IsIso (F.map c)] :
    IsZero (F.obj (kernel c)) ∧ IsZero (F.obj (cokernel c)) :=
  ⟨(isZero_kernel_of_mono (F.map c)).of_iso (PreservesKernel.iso F c),
    (isZero_cokernel_of_epi (F.map c)).of_iso (PreservesCokernel.iso F c)⟩

/-! ### The dévissage -/

/-- **The dévissage of [Stacks, Tag 0CRX].** Let `X` be a quasi-compact scheme with affine
diagonal and let `α : F ⟶ G` be a natural transformation between triangulated functors
`D(QCoh(𝒪_X)) ⥤ D(𝓑)`. If `α` is invertible at `j_*𝒢^•` for every inclusion `j : U ⟶ X` of an
affine open and every complex `𝒢^•` of quasi-coherent `𝒪_U`-modules, then `α` is an
isomorphism.

The inclusion of an affine open is an affine morphism because the diagonal of `X` is affine,
which is what makes `j_*` defined on quasi-coherent modules. -/
theorem isIso_natTrans_of_isIso_app_quasicoherentPushforward
    {X : Scheme.{u}} [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    {F G : DerivedCategory (Scheme.QuasicoherentModules X) ⥤ DerivedCategory B}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (α : F ⟶ G)
    (hα : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      haveI := Stacks.Cohomology.QcohDelta.isAffineHom_ι_of_isAffineOpen X U hU
      ∀ K : CochainComplex (Scheme.QuasicoherentModules U.toScheme) ℤ,
        IsIso (α.app (DerivedCategory.Q.obj
          (((quasicoherentPushforward U.ι).mapHomologicalComplex (.up ℤ)).obj K)))) :
    IsIso α := by
  obtain ⟨ι, _, U, hU, hcover⟩ := exists_finite_affine_open_cover X
  have (i : ι) : IsAffineHom (U i).ι :=
    Stacks.Cohomology.QcohDelta.isAffineHom_ι_of_isAffineOpen X (U i) (hU i)
  let A := Scheme.QuasicoherentModules X
  let Q := DerivedCategory.Q (C := A)
  let P (K : CochainComplex A ℤ) := ∀ n : ℤ, IsIso (α.app ((Q.obj K)⟦n⟧))
  let R (i : ι) := (quasicoherentRestrict (U i)).mapHomologicalComplex (.up ℤ)
  let L (i : ι) :=
    (quasicoherentRestrict (U i) ⋙ quasicoherentPushforward (U i).ι).mapHomologicalComplex (.up ℤ)
  let c (i : ι) : 𝟭 (CochainComplex A ℤ) ⟶ L i :=
    NatTrans.mapHomologicalComplex (quasicoherentRestrictUnit (U i)) (.up ℤ)
  have hP (K : CochainComplex A ℤ) : P K := by
    apply property_of_finite_family_of_kernel_cokernel P (fun i K => IsZero ((R i).obj K)) L c
    · intro M hM n
      have hz := (shiftFunctor (DerivedCategory A) n).map_isZero
        (Q.map_isZero (isZero_of_isZero_quasicoherentRestrict_complex U hcover M hM))
      exact (F.map_isZero hz).isIso (G.map_isZero hz) _
    · intro i j M hij
      have : IsIso ((R j).map ((c i).app M)) := by
        rcases hij with rfl | hM
        · exact isIso_quasicoherentRestrict_map_unit (U j) M
        · exact hM.isIso (isZero_quasicoherentRestrict_complex_pushforward (U i) (U j) M hM) _
      exact isZero_map_kernel_cokernel_of_isIso (R j) ((c i).app M)
    · intro i M n
      let K := (R i).obj M
      let H := (quasicoherentPushforward (U i).ι).mapHomologicalComplex (.up ℤ) ⋙ Q
      exact (α.isIso_app_iff_of_iso ((H.commShiftIso n).app K)).1 (hα (U i) (hU i) (K⟦n⟧))
    · intro M N g
      exact isIso_app_shift_of_kernel_cokernel α g
  have (K : DerivedCategory A) : IsIso (α.app K) := by
    let M := Q.objPreimage K
    have h : IsIso (α.app (Q.obj M)) :=
      (α.isIso_app_iff_of_iso ((shiftFunctorZero (DerivedCategory A) ℤ).app (Q.obj M))).1
        (hP M 0)
    exact (α.isIso_app_iff_of_iso (Q.objObjPreimageIso K)).1 h
  exact NatIso.isIso_of_isIso_app α

end Stacks.DerivedQCoh

end
