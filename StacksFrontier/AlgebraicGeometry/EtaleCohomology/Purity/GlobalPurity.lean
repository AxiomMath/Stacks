module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurityFinset
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global cohomological purity for smooth pairs

Let `k` be algebraically closed, `ℓ` a prime invertible in `k`, `Y` smooth over `k` of relative
dimension `d + c` and `i : T ⟶ Y` a closed immersion with `T` quasi-compact and smooth over `k`
of relative dimension `d`. Then `i` has a purity class `γ ∈ Ext^{2c}_Y(i_* Λ_T, Λ_Y)` for
`Λ = ℤ/ℓ` (SGA 4 XVI 3.7; `Stacks.EtaleCohomology.Purity.exists_isPurityClass_of_smooth`).

The local purity classes of `Stacks.EtaleCohomology.Purity.localPurityFun` are read on `Y`
through extension by zero, restricted to irreducible opens of `T`
(`AlgebraicGeometry.exists_isOpen_isIrreducible_of_smooth`: a scheme smooth over a field is
locally irreducible), and glued over a finite cover of `T`. Two local classes glue across an
overlap which is either irreducible, by rescaling
(`Stacks.EtaleCohomology.Purity.IsLocalPurityClass.exists_glue`), or empty, where every class
agrees (`Stacks.EtaleCohomology.Purity.IsLocalPurityClass.exists_glue_of_isPreirreducible`).
A local purity class over all of `T` is a purity class
(`Stacks.EtaleCohomology.Purity.IsLocalPurityClass.exists_isPurityClass`).

This is part of the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.EtaleCohomology.ExtensionTorsor
open Stacks.EtaleCohomology.Purity.Gysin

universe u

namespace AlgebraicGeometry

/-- **A scheme smooth over a field is locally irreducible**: every point has an irreducible open
neighbourhood, namely an integral piece of the decomposition of a normal Noetherian affine open
neighbourhood into integral schemes (Tag 033M). -/
theorem exists_isOpen_isIrreducible_of_smooth {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [Smooth g] (z : Y) :
    ∃ U : Set Y, IsOpen U ∧ z ∈ U ∧ IsIrreducible U := by
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨V, hzV⟩ : ∃ V : Y.affineOpens, z ∈ V.1 := by
    rw [← TopologicalSpace.Opens.mem_iSup, iSup_affineOpens_eq_top]
    trivial
  have : IsAffine V.1.toScheme := V.2
  have : IsNoetherian V.1.toScheme := ⟨⟩
  have : IsNormal V.1.toScheme := isNormal_of_smooth (V.1.ι ≫ g)
  obtain ⟨ι, _, W, _, hint, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_finite_coproduct_integral_normal V.1.toScheme).mp inferInstance
  obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk W).surjective (e.hom ⟨z, hzV⟩)
  rw [sigmaMk_mk] at hw
  let j : W i ⟶ Y := Sigma.ι W i ≫ e.inv ≫ V.1.ι
  have := hint i
  refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, ⟨w, ?_⟩, ?_⟩
  · change V.1.ι (e.inv (Sigma.ι W i w)) = z
    rw [hw]
    change (e.hom ≫ e.inv ≫ V.1.ι) ⟨z, hzV⟩ = z
    rw [e.hom_inv_id_assoc]
    rfl
  · rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (W i)).image j j.continuous.continuousOn

end AlgebraicGeometry

namespace Stacks.EtaleCohomology.Purity

attribute [local instance] moduleCat_hasLimitsOfSize

/-! ### Classes at zero objects -/

/-- Every `Ext` class out of a zero object vanishes. -/
private theorem ext_eq_zero_of_isZero {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y : C}
    {n : ℕ} (hX : IsZero X) (z : Ext X Y n) : z = 0 := by
  rw [← Ext.mk₀_id_comp z, hX.eq_of_src (𝟙 _) 0, Ext.mk₀_zero, Ext.zero_comp]

namespace Gysin

variable {C : Type*} [Category C] [Abelian C] [HasExt C] {D : Type*} [Category D] [Abelian D]
  [HasExt D] (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- **Every class is good at a zero object**: all the `Ext` groups involved vanish. -/
theorem isGoodAt_of_isZero {M : C} {A : D} {c : ℕ} (γ : Ext (P.obj M) A c) {X : C}
    (hX : IsZero X) : IsGoodAt P γ X := by
  have hPX : IsZero (P.obj X) := P.map_isZero hX
  have hsC : ∀ q, Subsingleton (Ext X M q) := fun q =>
    subsingleton_of_forall_eq 0 (ext_eq_zero_of_isZero hX)
  have hsD : ∀ q, Subsingleton (Ext (P.obj X) A q) := fun q =>
    subsingleton_of_forall_eq 0 (ext_eq_zero_of_isZero hPX)
  exact ⟨fun q q' h => ⟨fun a b _ => (hsC q).elim a b, fun b => ⟨0, (hsD q').elim _ _⟩⟩,
    fun q _ => hsD q⟩

end Gysin

variable {N : ℕ}

/-! ### Extension by zero from an empty open -/

/-- **Extension by zero from an open with no points vanishes.** -/
theorem isZero_extensionByZero_of_forall_notMem {T : Scheme.{u}} (O : T.Opens)
    (hO : ∀ x : T, x ∉ O) (H : EtaleModules.{u, 0} (ZMod N) O) :
    IsZero ((etaleModuleExtensionByZero.{u, 0} (ZMod N) O.ι).obj H) := by
  have hH : IsZero H := isZero_etaleModule_of_forall_isZero_sections (ZMod N) H fun V =>
    isZero_etaleModule_sections_of_isEmpty (ZMod N) H V ⟨fun v => hO _ (V.hom.base v).2⟩
  exact Functor.map_isZero _ hH

/-- **The counit of extension by zero from an open containing every point is invertible.** -/
theorem isIso_counit_extensionByZeroAdj_of_forall_mem {T : Scheme.{u}} (O : T.Opens)
    (hO : ∀ x : T, x ∈ O) (F : EtaleModules.{u, 0} (ZMod N) T) :
    IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) O.ι).counit.app F) := by
  refine isIso_of_isIso_etaleModuleInverseImage_family (ZMod N) (ι := PUnit.{u + 1})
    (fun _ => O.ι) ?_ _ fun _ =>
      isIso_etaleModuleInverseImage_map_counit_of_factors (ZMod N) O.ι O.ι (𝟙 _)
        (Category.id_comp _) F
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨PUnit.unit, ?_⟩
  rw [Scheme.Opens.range_ι]
  exact hO x

/-! ### Gluing local purity classes -/

section Gluing

variable {T Y : Scheme.{u}} (i : T ⟶ Y) [IsClosedImmersion i]

/-- **Every class is a local purity class over an open with no points.** -/
theorem isLocalPurityClass_of_forall_notMem (O : T.Opens) (hO : ∀ x : T, x ∉ O) {c : ℕ}
    (a : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) O))
      (unitSheaf (X := Y) N) c) : IsLocalPurityClass i O a := fun H =>
  isGoodAt_of_isZero _ a (isZero_extensionByZero_of_forall_notMem O hO H)

variable [NeZero N] in
/-- **Two local purity classes glue when one of the two opens is irreducible**: their overlap is
then either irreducible, where the classes agree after rescaling one of them by a unit
(`Stacks.EtaleCohomology.Purity.IsLocalPurityClass.exists_glue`), or empty, where all classes
agree. -/
theorem IsLocalPurityClass.exists_glue_of_isPreirreducible {O₁ O₂ : T.Opens}
    (hO₂ : IsPreirreducible (O₂ : Set T)) {c : ℕ}
    {a₁ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) O₁))
      (unitSheaf (X := Y) N) c}
    {a₂ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) O₂))
      (unitSheaf (X := Y) N) c}
    (h₁ : IsLocalPurityClass i O₁ a₁) (h₂ : IsLocalPurityClass i O₂ a₂) :
    ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) (O₁ ⊔ O₂)))
      (unitSheaf (X := Y) N) c, IsLocalPurityClass i (O₁ ⊔ O₂) γ := by
  by_cases hne : ((O₁ ⊓ O₂ : T.Opens) : Set T).Nonempty
  · have : IrreducibleSpace (O₁ ⊓ O₂ : T.Opens) :=
      Subtype.irreducibleSpace ⟨hne, hO₂.open_subset (O₁ ⊓ O₂).isOpen fun _ hx => hx.2⟩
    exact IsLocalPurityClass.exists_glue i h₁ h₂
  · refine IsLocalPurityClass.glue i h₁ h₂ ?_
    have hz : IsZero ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj
        (localUnit (N := N) (O₁ ⊓ O₂))) :=
      Functor.map_isZero _ (isZero_extensionByZero_of_forall_notMem _
        (fun x hx => hne ⟨x, hx⟩) _)
    rw [ext_eq_zero_of_isZero hz ((Ext.mk₀ _).comp a₁ (zero_add c)),
      ext_eq_zero_of_isZero hz ((Ext.mk₀ _).comp a₂ (zero_add c))]

variable [NeZero N] in
/-- **Local purity classes on irreducible opens glue over finite unions.** -/
theorem exists_isLocalPurityClass_finset_sup {ι : Type*} (O : ι → T.Opens)
    (hO : ∀ x, IsPreirreducible (O x : Set T)) {c : ℕ}
    (ha : ∀ x, ∃ a : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj
      (localUnit (N := N) (O x))) (unitSheaf (X := Y) N) c, IsLocalPurityClass i (O x) a)
    (s : Finset ι) :
    ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) (s.sup O)))
      (unitSheaf (X := Y) N) c, IsLocalPurityClass i (s.sup O) γ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, isLocalPurityClass_of_forall_notMem i _ (fun x hx => by simp at hx) 0⟩
  | insert x s _ ih =>
    obtain ⟨γ, hγ⟩ := ih
    obtain ⟨a, ha⟩ := ha x
    rw [Finset.sup_insert, sup_comm]
    exact IsLocalPurityClass.exists_glue_of_isPreirreducible i (hO x) hγ ha

variable [Fact N.Prime] in
/-- **A local purity class over all of `T` gives a purity class**: `Λ_T^! ≅ Λ_T` and every
sheaf on `T` is an extension by zero from the open `T`. -/
theorem IsLocalPurityClass.exists_isPurityClass {O : T.Opens} (hO : ∀ x : T, x ∈ O) {c : ℕ}
    {a : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) O))
      (unitSheaf (X := Y) N) c} (ha : IsLocalPurityClass i O a) :
    ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (unitSheaf (X := T) N))
      (unitSheaf (X := Y) N) c, IsPurityClass i _ γ := by
  let P := etaleModuleDirectImage.{u, 0} (ZMod N) i
  have := isIso_counit_extensionByZeroAdj_of_forall_mem (N := N) O hO (unitSheaf (X := T) N)
  let ε : localUnit (N := N) O ≅ unitSheaf (X := T) N :=
    asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) O.ι).counit.app (unitSheaf (X := T) N))
  let γ := (Ext.mk₀ (P.map ε.inv)).comp a (zero_add c)
  have hgood : ∀ G, IsGoodAt P γ G := fun G => by
    have := isIso_counit_extensionByZeroAdj_of_forall_mem (N := N) O hO G
    refine (isGoodAt_comp_mk₀_iff P a ε.inv G (fun q =>
      Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := _) _ q)).2 ?_
    exact (ha ((etaleModuleRestriction.{u, 0} (ZMod N) O.ι).obj G)).of_iso _ _
      (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) O.ι).counit.app G))
  exact ⟨γ, fun G q => (hgood G).1 q (q + c) rfl, fun G q hq => (hgood G).2 q hq⟩

end Gluing

/-! ### Global purity -/

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Cohomological purity for smooth pairs** (SGA 4 XVI 3.7). Let `k` be algebraically closed,
`ℓ` a prime invertible in `k`, `Y` smooth over `k` of relative dimension `d + c` and
`i : T ⟶ Y` a closed immersion with `T` quasi-compact and smooth over `k` of relative dimension
`d`. Then `i` has a purity class `γ ∈ Ext^{2c}_Y(i_* Λ_T, Λ_Y)`, `Λ = ℤ/ℓ`: the map
`y ↦ i_* y ∘ γ`, `Ext^q_T(G, Λ_T) → Ext^{q + 2c}_Y(i_* G, Λ_Y)`, is bijective for every `G` and
`q`, and `Ext^q_Y(i_* G, Λ_Y) = 0` for `q < 2c`. -/
@[sga "5 I 5.1" "Purity clause of I 5.1"]
theorem exists_isPurityClass_of_smooth (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k))
    (Y T : Scheme.{u}) (p : Y ⟶ Spec (.of k)) (i : T ⟶ Y) [IsClosedImmersion i] (d c : ℕ)
    [SmoothOfRelativeDimension (d + c) p] [SmoothOfRelativeDimension d (i ≫ p)]
    [CompactSpace T] :
    ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
        (unitSheaf (X := Y) ℓ) (2 * c),
      IsPurityClass i _ γ := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : Smooth (i ≫ p) := SmoothOfRelativeDimension.smooth d (i ≫ p)
  have hx : ∀ x : T, ∃ O : T.Opens, x ∈ O ∧ IsPreirreducible (O : Set T) ∧
      ∃ a : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (localUnit (N := ℓ) O))
        (unitSheaf (X := Y) ℓ) (2 * c), IsLocalPurityClass i O a := by
    intro x
    obtain ⟨U, hxU, γ, hγ⟩ := localPurityFun k ℓ hℓ Y T p i d c x
    obtain ⟨a, ha⟩ := exists_isLocalPurityClass_of_isPurityClassFun i U γ hγ
    obtain ⟨V, hV, hxV, hVirr⟩ := exists_isOpen_isIrreducible_of_smooth (i ≫ p) x
    exact ⟨i ⁻¹ᵁ U ⊓ ⟨V, hV⟩, ⟨hxU, hxV⟩,
      hVirr.2.open_subset (i ⁻¹ᵁ U ⊓ ⟨V, hV⟩).isOpen fun _ hy => hy.2, _,
      ha.restrict i inf_le_left⟩
  choose O hxO hO ha using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (O x : Set T))
    (fun x => (O x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxO x⟩)
  obtain ⟨γ, hγ⟩ := exists_isLocalPurityClass_finset_sup i O hO ha t
  refine IsLocalPurityClass.exists_isPurityClass i (fun x => ?_) hγ
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact (Finset.le_sup hy : O y ≤ t.sup O) hxy

end Stacks.EtaleCohomology.Purity

end
