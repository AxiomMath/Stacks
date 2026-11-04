module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurityGluing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.FiniteComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero

/-!
# Purity on a neighbourhood of finitely many points

Let `k` be algebraically closed, `N` an integer invertible in `k`, `Y` smooth over `k` of relative
dimension `d + c` and `i : T ⟶ Y` a closed immersion with `T` irreducible and smooth over `k` of
relative dimension `d`. For every finite set `s` of points of `T` there is an open `U ⊆ Y`
containing `i(s)` over which `T ∩ U ⟶ U` has a purity class in degree `2c` for `Λ = ℤ/N`
(`Stacks.EtaleCohomology.Purity.localPurityFun_finset`).

The local purity classes of `Stacks.EtaleCohomology.Purity.localPurityFun` are read on `Y` through
extension by zero (`Stacks.EtaleCohomology.Purity.exists_isLocalPurityClass_of_isPurityClassFun`,
using Stacks 0GJ1, `j_! ∘ (i|_U)_* ≅ i_* ∘ j_!`), glued one point at a time over the union of
their neighbourhoods (`Stacks.EtaleCohomology.Purity.IsLocalPurityClass.exists_glue`; the traces on
`T` of two nonempty opens meet in an irreducible open, since `T` is irreducible), and read back on
the union (`Stacks.EtaleCohomology.Purity.exists_isPurityClassFun_of_isLocalPurityClass`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.EtaleCohomology.ExtensionTorsor
open Stacks.EtaleCohomology.Purity.Gysin

universe u

namespace Stacks.EtaleCohomology.Purity

attribute [local instance] moduleCat_hasLimitsOfSize

variable {N : ℕ}

/-! ### Extension by zero along an open immersion has a purity class of degree zero -/

section ExtensionByZero

variable {Y : Scheme.{u}} (U : Y.Opens)

/-- The class `j_{U!} Λ_U ≅ j_{U!} j⁻¹ Λ_Y ⟶ Λ_Y` of degree zero. -/
def extensionByZeroUnitClass :
    Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod N) U.ι).obj (unitSheaf (X := U.toScheme) N))
      (unitSheaf (X := Y) N) 0 :=
  Ext.mk₀ ((etaleModuleExtensionByZero.{u, 0} (ZMod N) U.ι).map
      (unitSheafRestrictionIso (N := N) U).inv ≫
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) U.ι).counit.app (unitSheaf N))

/-- **Extension by zero along an open immersion has a purity class of degree zero**: its Gysin
map is the adjunction isomorphism `Ext_U(G, Λ_U) ≅ Ext_Y(j_! G, Λ_Y)`. -/
theorem isPurityClassFun_extensionByZeroUnitClass :
    IsPurityClassFun N (etaleModuleExtensionByZero.{u, 0} (ZMod N) U.ι) (unitSheaf (X := Y) N)
      (extensionByZeroUnitClass (N := N) U) := by
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) U.ι
  refine isPurityClassFun_of_rfl _ _ _ (fun G q => ?_) (fun G q hq => absurd hq (Nat.not_lt_zero q))
  have e : (fun y : Ext G (unitSheaf (X := U.toScheme) N) q =>
      (y.mapExactFunctor (etaleModuleExtensionByZero.{u, 0} (ZMod N) U.ι)).comp
        (extensionByZeroUnitClass (N := N) U) (show q + 0 = q + 0 from rfl)) =
      Stacks.ExtAdjunction.extMap adj G (unitSheaf (X := Y) N) q ∘
        (Ext.mk₀ (unitSheafRestrictionIso (N := N) U).inv).postcomp G (add_zero q) := by
    funext y
    simp only [Function.comp_apply, Stacks.ExtAdjunction.extMap_apply,
      Stacks.ExtAdjunction.postcomp_apply, extensionByZeroUnitClass, Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_mk₀]
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rw [e]
  exact (Stacks.ExtAdjunction.extMap_bijective adj G _ q).comp
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := G) _ q)

/-- **Cancelling an extension by zero**: a purity class for `Q ⋙ j_{U!}` comes from a purity class
for `Q`, by the adjunction isomorphism `Ext_U(-, j⁻¹ Λ_Y) ≅ Ext_Y(j_!(-), Λ_Y)`. -/
theorem exists_isPurityClassFun_of_comp_extensionByZero {T : Scheme.{u}}
    (Q : EtaleModules.{u, 0} (ZMod N) T ⥤ EtaleModules.{u, 0} (ZMod N) U) [Q.Additive]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q] {c : ℕ}
    (β : Ext ((Q ⋙ etaleModuleExtensionByZero.{u, 0} (ZMod N) U.ι).obj (unitSheaf (X := T) N))
      (unitSheaf (X := Y) N) c)
    (hβ : IsPurityClassFun N (Q ⋙ etaleModuleExtensionByZero.{u, 0} (ZMod N) U.ι)
      (unitSheaf (X := Y) N) β) :
    ∃ γ : Ext (Q.obj (unitSheaf (X := T) N)) (unitSheaf (X := U.toScheme) N) c,
      IsPurityClassFun N Q (unitSheaf (X := U.toScheme) N) γ := by
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) U.ι
  let e := unitSheafRestrictionIso (N := N) U
  obtain ⟨γ₁, hγ₁⟩ := (Stacks.ExtAdjunction.extMap_bijective adj (Q.obj (unitSheaf (X := T) N))
    (unitSheaf (X := Y) N) c).2 β
  refine ⟨γ₁.comp (Ext.mk₀ e.hom) (add_zero c), isPurityClassFun_of_rfl _ _ _
    (fun G q => ?_) (fun G q hq => ?_)⟩
  · have hkey : Stacks.ExtAdjunction.extMap adj (Q.obj G) (unitSheaf (X := Y) N) (q + c) ∘
        (fun y : Ext G (unitSheaf (X := T) N) q => (y.mapExactFunctor Q).comp γ₁ rfl) =
        fun y => (y.mapExactFunctor (Q ⋙ etaleModuleExtensionByZero.{u, 0} (ZMod N) U.ι)).comp
          β rfl := by
      funext y
      simp only [Function.comp_apply, Stacks.ExtAdjunction.extMap_apply, Ext.mapExactFunctor_comp]
      rw [Ext.comp_assoc_of_third_deg_zero,
        Stacks.ExtFunctorial.mapExactFunctor_comp_functor Q
          (etaleModuleExtensionByZero.{u, 0} (ZMod N) U.ι), ← hγ₁,
        Stacks.ExtAdjunction.extMap_apply]
    have h₁ : Function.Bijective
        (fun y : Ext G (unitSheaf (X := T) N) q => (y.mapExactFunctor Q).comp γ₁ rfl) := by
      have := hβ.1 G q (q + c) rfl
      rw [← hkey] at this
      exact (Function.Bijective.of_comp_iff' (Stacks.ExtAdjunction.extMap_bijective adj _ _ _) _).1
        this
    have hfac : (fun y : Ext G (unitSheaf (X := T) N) q =>
        (y.mapExactFunctor Q).comp (γ₁.comp (Ext.mk₀ e.hom) (add_zero c))
          (show q + c = q + c from rfl)) =
        (Ext.mk₀ e.hom).postcomp (Q.obj G) (add_zero (q + c)) ∘
          (fun y : Ext G (unitSheaf (X := T) N) q => (y.mapExactFunctor Q).comp γ₁ rfl) := by
      funext y
      simp only [Function.comp_apply, Stacks.ExtAdjunction.postcomp_apply]
      exact (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm
    rw [hfac]
    exact (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := Q.obj G) e.hom _).comp h₁
  · have : Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod N) U.ι).obj (Q.obj G))
        (unitSheaf (X := Y) N) q) := hβ.2 G q hq
    have : Subsingleton (Ext (Q.obj G) ((etaleModuleRestriction.{u, 0} (ZMod N) U.ι).obj
        (unitSheaf (X := Y) N)) q) :=
      (Stacks.ExtAdjunction.extMap_bijective adj (Q.obj G) (unitSheaf (X := Y) N) q).1.subsingleton
    exact (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := Q.obj G) e.hom
      q).2.subsingleton

end ExtensionByZero

/-! ### From purity classes on opens to local purity classes and back -/

section Conversion

variable {T Y : Scheme.{u}} (i : T ⟶ Y) [IsClosedImmersion i]

/-- Goodness at `j_{O!} H` for all `H` is purity of `j_{O!} ⋙ i_*`. -/
theorem isGoodAt_extensionByZero_iff (O : T.Opens) {c : ℕ}
    (β : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) O.ι).obj (unitSheaf (X := O.toScheme) N)))
      (unitSheaf (X := Y) N) c) :
    (∀ H, IsGoodAt (etaleModuleDirectImage.{u, 0} (ZMod N) i) β
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) O.ι).obj H)) ↔
    IsPurityClassFun N (etaleModuleExtensionByZero.{u, 0} (ZMod N) O.ι ⋙
      etaleModuleDirectImage.{u, 0} (ZMod N) i) (unitSheaf (X := Y) N) β := by
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) O.ι
  have hmap : ∀ (H : EtaleModules.{u, 0} (ZMod N) O) q, Function.Bijective
      (fun y : Ext H (unitSheaf (X := O.toScheme) N) q =>
        y.mapExactFunctor (etaleModuleExtensionByZero.{u, 0} (ZMod N) O.ι)) := fun H q =>
    Stacks.ExtAdjunction.mapExtAddHom_bijective adj H _ q
  have e : ∀ (H : EtaleModules.{u, 0} (ZMod N) O) q q' (h : q + c = q'),
      (fun y : Ext H (unitSheaf (X := O.toScheme) N) q =>
        (y.mapExactFunctor (etaleModuleExtensionByZero.{u, 0} (ZMod N) O.ι ⋙
          etaleModuleDirectImage.{u, 0} (ZMod N) i)).comp β h) =
      gysin (etaleModuleDirectImage.{u, 0} (ZMod N) i) β _ q q' h ∘
        (fun y => y.mapExactFunctor (etaleModuleExtensionByZero.{u, 0} (ZMod N) O.ι)) := by
    intro H q q' h
    funext y
    simp only [Function.comp_apply, gysin_apply]
    rw [Stacks.ExtFunctorial.mapExactFunctor_comp_functor]
  constructor
  · intro hgood
    refine ⟨fun H q q' h => ?_, fun H q hq => (hgood H).2 q hq⟩
    rw [e]
    exact ((hgood H).1 q q' h).comp (hmap H q)
  · intro hβ H
    refine ⟨fun q q' h => ?_, fun q hq => hβ.2 H q hq⟩
    have := hβ.1 H q q' h
    rw [e] at this
    exact (Function.Bijective.of_comp_iff _ (hmap H q)).1 this

variable [IsIntegralHom i]

/-- **A purity class on an open `U ⊆ Y` gives a local purity class over `i⁻¹(U)`**: compose with
the degree zero purity class of `j_{U!}` and identify `j_{U!} ∘ (i|_U)_*` with `i_* ∘ j_!`
(Stacks 0GJ1). -/
theorem exists_isLocalPurityClass_of_isPurityClassFun (U : Y.Opens) {c : ℕ}
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) (i ∣_ U)).obj
      (unitSheaf (X := (i ⁻¹ᵁ U).toScheme) N)) (unitSheaf (X := U.toScheme) N) c)
    (hγ : IsPurityClassFun N (etaleModuleDirectImage.{u, 0} (ZMod N) (i ∣_ U))
      (unitSheaf (X := U.toScheme) N) γ) :
    ∃ a : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) (i ⁻¹ᵁ U)))
      (unitSheaf (X := Y) N) c, IsLocalPurityClass i (i ⁻¹ᵁ U) a := by
  let e₀ := etaleModuleExtensionByZeroDirectImageIsoOfIsIntegralHom (ZMod N) U.ι (i ⁻¹ᵁ U).ι
    (i ∣_ U) i (isPullback_morphismRestrict i U)
  have h₂ := (hγ.comp (isPurityClassFun_extensionByZeroUnitClass (N := N) U)).ofIso e₀
  rw [← isGoodAt_extensionByZero_iff] at h₂
  exact ⟨(Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod N) i).map
    ((etaleModuleExtensionByZero.{u, 0} (ZMod N) (i ⁻¹ᵁ U).ι).map
      (unitSheafRestrictionIso (N := N) (i ⁻¹ᵁ U)).hom))).comp _ (zero_add c), fun H =>
    (isGoodAt_comp_mk₀_iff _ _ _ _ (fun q =>
      Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := _) _ q)).2 (h₂ H)⟩

/-- **A local purity class over `i⁻¹(U)` gives a purity class on `U`.** -/
theorem exists_isPurityClassFun_of_isLocalPurityClass (U : Y.Opens) {c : ℕ}
    (a : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) (i ⁻¹ᵁ U)))
      (unitSheaf (X := Y) N) c) (ha : IsLocalPurityClass i (i ⁻¹ᵁ U) a) :
    ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) (i ∣_ U)).obj
      (unitSheaf (X := (i ⁻¹ᵁ U).toScheme) N)) (unitSheaf (X := U.toScheme) N) c,
      IsPurityClassFun N (etaleModuleDirectImage.{u, 0} (ZMod N) (i ∣_ U))
        (unitSheaf (X := U.toScheme) N) γ := by
  let e₀ := etaleModuleExtensionByZeroDirectImageIsoOfIsIntegralHom (ZMod N) U.ι (i ⁻¹ᵁ U).ι
    (i ∣_ U) i (isPullback_morphismRestrict i U)
  let β := (Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod N) i).map
    ((etaleModuleExtensionByZero.{u, 0} (ZMod N) (i ⁻¹ᵁ U).ι).map
      (unitSheafRestrictionIso (N := N) (i ⁻¹ᵁ U)).inv))).comp a (zero_add c)
  have hβ : ∀ H, IsGoodAt (etaleModuleDirectImage.{u, 0} (ZMod N) i) β
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) (i ⁻¹ᵁ U).ι).obj H) := fun H =>
    (isGoodAt_comp_mk₀_iff _ _ _ _ (fun q =>
      Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := _) _ q)).2 (ha H)
  rw [isGoodAt_extensionByZero_iff] at hβ
  exact exists_isPurityClassFun_of_comp_extensionByZero U _ _ (hβ.ofIso e₀.symm)

end Conversion

/-! ### Purity near finitely many points -/

/-- Two nonempty opens of an irreducible scheme meet in an irreducible open. -/
theorem irreducibleSpace_inf_of_nonempty {T : Scheme.{u}} [IrreducibleSpace T] (O₁ O₂ : T.Opens)
    (h₁ : (O₁ : Set T).Nonempty) (h₂ : (O₂ : Set T).Nonempty) :
    IrreducibleSpace (O₁ ⊓ O₂ : T.Opens) := by
  have hirr : IsPreirreducible (Set.univ : Set T) := (IrreducibleSpace.isIrreducible_univ T).2
  have hne : ((O₁ ⊓ O₂ : T.Opens) : Set T).Nonempty := by
    obtain ⟨x, -, hx⟩ := hirr O₁ O₂ O₁.isOpen O₂.isOpen (by simpa using h₁) (by simpa using h₂)
    exact ⟨x, hx⟩
  exact Subtype.irreducibleSpace ⟨hne, hirr.open_subset (O₁ ⊓ O₂).isOpen (Set.subset_univ _)⟩

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Cohomological purity on a neighbourhood of finitely many points** (SGA 4 XVI 3.7). Let `k`
be algebraically closed, `N` an integer invertible in `k`, `Y` smooth over `k` of relative
dimension `d + c` and `i : T ⟶ Y` a closed immersion with `T` irreducible and smooth over `k` of
relative dimension `d`. For every finite set `s` of points of `T` there is an open `U ⊆ Y`
containing `i(s)` over which `T ∩ U ⟶ U` has a purity class in degree `2c` for `Λ = ℤ/N`. -/
theorem localPurityFun_finset (N : ℕ) (hN : IsUnit (N : k)) (Y T : Scheme.{u})
    (p : Y ⟶ Spec (.of k)) (i : T ⟶ Y) [IsClosedImmersion i] (d c : ℕ)
    [SmoothOfRelativeDimension (d + c) p] [SmoothOfRelativeDimension d (i ≫ p)]
    [IrreducibleSpace T] (s : Finset T) :
    ∃ U : Y.Opens, (∀ x ∈ s, i.base x ∈ U) ∧
      ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) (i ∣_ U)).obj
          (unitSheaf (X := (i ⁻¹ᵁ U).toScheme) N)) (unitSheaf (X := U.toScheme) N) (2 * c),
        IsPurityClassFun N (etaleModuleDirectImage.{u, 0} (ZMod N) (i ∣_ U))
          (unitSheaf (X := U.toScheme) N) γ := by
  classical
  have : NeZero N := ⟨by rintro rfl; simp at hN⟩
  suffices hA : ∃ U : Y.Opens, (∀ x ∈ s, i.base x ∈ U) ∧ ((i ⁻¹ᵁ U : T.Opens) : Set T).Nonempty ∧
      ∃ a : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) (i ⁻¹ᵁ U)))
        (unitSheaf (X := Y) N) (2 * c), IsLocalPurityClass i (i ⁻¹ᵁ U) a by
    obtain ⟨U, hU, -, a, ha⟩ := hA
    exact ⟨U, hU, exists_isPurityClassFun_of_isLocalPurityClass i U a ha⟩
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨x₀⟩ := (inferInstance : IrreducibleSpace T).toNonempty
    obtain ⟨U, hxU, γ, hγ⟩ := localPurityFun k N hN Y T p i d c x₀
    exact ⟨U, by simp, ⟨x₀, hxU⟩, exists_isLocalPurityClass_of_isPurityClassFun i U γ hγ⟩
  | insert x s hxs ih =>
    obtain ⟨U', hU', hne', a', ha'⟩ := ih
    obtain ⟨Ux, hxUx, γx, hγx⟩ := localPurityFun k N hN Y T p i d c x
    obtain ⟨ax, hax⟩ := exists_isLocalPurityClass_of_isPurityClassFun i Ux γx hγx
    have := irreducibleSpace_inf_of_nonempty (i ⁻¹ᵁ U') (i ⁻¹ᵁ Ux) hne' ⟨x, hxUx⟩
    obtain ⟨γ, hγ⟩ := IsLocalPurityClass.exists_glue i ha' hax
    refine ⟨U' ⊔ Ux, fun y hy => ?_, ?_, ?_⟩
    · rcases Finset.mem_insert.1 hy with rfl | hy
      exacts [Or.inr hxUx, Or.inl (hU' y hy)]
    · obtain ⟨y, hy⟩ := hne'
      exact ⟨y, Or.inl hy⟩
    · rw [Scheme.Hom.preimage_sup]
      exact ⟨γ, hγ⟩

end Stacks.EtaleCohomology.Purity

end
