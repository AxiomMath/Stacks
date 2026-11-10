module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModulePullbackMap
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleDegreeZero

/-!
# The map of Čech complexes induced by a morphism of schemes and a refinement

Let `g : X' ⟶ X` be a morphism of schemes, `F` an `𝒪_X`-module, `U : I → X.Opens` and
`W : I' → X'.Opens` families of opens, and `π : I' → I` a function with `W k ≤ g⁻¹ U (π k)` for
every `k`. Pulling sections back along `g` on each finite intersection, and restricting along the
inclusions the condition provides, carries Čech cochains of `F` for `U` to Čech cochains of `g^*F`
for `W`. This file builds that map, shows that it commutes with the Čech differential, preserves
alternating cochains and is linear over the base ring, and assembles it into a morphism of the
alternating Čech complexes of `A`-modules.

When `π` is a bijection and `W k = g⁻¹ U (π k)`, the map is the base-change comparison
`Stacks.Cech.cochainBaseChange` (for `π` the identity, the morphism of complexes is
`Stacks.Cech.alternatingCechModuleComplexPullbackMap`); here `π` is arbitrary and the families are
only related by an inclusion, which is what a morphism `X' ⟶ X` that is not a base change
requires: the preimages of affine opens of `X` need not be affine, and an affine refinement of
them is indexed by a different type.

## Main definitions

* `Stacks.Cech.cochainPullback`, `Stacks.Cech.alternatingCochainRefinementPullbackₗ` and
  `Stacks.Cech.alternatingCechModuleRefinementPullbackMap`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.Cech

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {I I' : Type u} (U : I → X.Opens)
  (W : I' → X'.Opens) (π : I' → I) (hW : ∀ k, W k ≤ g ⁻¹ᵁ U (π k)) (F : X.Modules)

include hW in
/-- The intersection over a tuple of members of `W` lies in the preimage of the intersection over
the image tuple. -/
theorem inter_le_preimage_inter {p : ℕ} (k : Fin p → I') :
    CechCochains.inter W k ≤ g ⁻¹ᵁ CechCochains.inter U (π ∘ k) := by
  intro x hx
  simp only [CechCochains.inter, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf,
    Set.mem_iInter, Scheme.Hom.coe_preimage, Set.mem_preimage] at hx ⊢
  intro j
  exact hW (k j) (hx j)

/-- **The comparison on Čech cochains induced by `g` and `π`.** -/
def cochainPullback (p : ℕ) (s : CechCochains.Cochain U F.presheaf p) :
    CechCochains.Cochain W ((Scheme.Modules.pullback g).obj F).presheaf p := fun k ↦
  CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
    (inter_le_preimage_inter g U W π hW k)
    ((pullbackSections g F (CechCochains.inter U (π ∘ k))) (s (π ∘ k)))

/-- The comparison on Čech cochains is additive. -/
theorem cochainPullback_add (p : ℕ) (s t : CechCochains.Cochain U F.presheaf p) :
    cochainPullback g U W π hW F p (s + t) =
      cochainPullback g U W π hW F p s + cochainPullback g U W π hW F p t := by
  funext i
  simp only [cochainPullback, CechCochains.Cochain.add_apply, map_add]

/-- **The comparison on Čech cochains is a morphism of complexes.** -/
theorem cochainPullback_cechD (p : ℕ) (s : CechCochains.Cochain U F.presheaf p) :
    CechCochains.cechD W ((Scheme.Modules.pullback g).obj F).presheaf p
        (cochainPullback g U W π hW F p s) =
      cochainPullback g U W π hW F (p + 1) (CechCochains.cechD U F.presheaf p s) := by
  have cechD_apply' : ∀ {Y : TopCat.{u}} {J : Type u} (V : J → Opens Y)
      (ℱ : TopCat.Presheaf Ab Y) (p : ℕ) (s : CechCochains.Cochain V ℱ p) (i : Fin (p + 2) → J),
      CechCochains.cechD V ℱ p s i =
        ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          CechCochains.restr ℱ (CechCochains.inter_le_omit V i j) (s (i ∘ j.succAbove)) :=
    fun _ _ _ _ _ => rfl
  funext i
  rw [cechD_apply']
  have hR : cochainPullback g U W π hW F (p + 1) (CechCochains.cechD U F.presheaf p s) i =
      CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
        (inter_le_preimage_inter g U W π hW i)
        ((pullbackSections g F (CechCochains.inter U (π ∘ i)))
          (CechCochains.cechD U F.presheaf p s (π ∘ i))) := rfl
  rw [hR, cechD_apply', map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hL : cochainPullback g U W π hW F p s (i ∘ j.succAbove) =
      CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
        (inter_le_preimage_inter g U W π hW (i ∘ j.succAbove))
        ((pullbackSections g F (CechCochains.inter U (π ∘ (i ∘ j.succAbove))))
          (s (π ∘ (i ∘ j.succAbove)))) := rfl
  rw [hL, CechCochains.restr_restr, map_zsmul, map_zsmul]
  congr 1
  exact (pullbackSections_restr g F (CechCochains.inter_le_omit U (π ∘ i) j) _ _
    (s (π ∘ (i ∘ j.succAbove)))).symm

/-- **The comparison on Čech cochains carries alternating cochains to alternating cochains.** -/
theorem cochainPullback_isAlternating (p : ℕ) (s : CechCochains.Cochain U F.presheaf p)
    (hs : CechCochains.IsAlternating U F.presheaf s) :
    CechCochains.IsAlternating W ((Scheme.Modules.pullback g).obj F).presheaf
      (cochainPullback g U W π hW F p s) := by
  have permIso_eq_restr' : ∀ {Y : TopCat.{u}} {J : Type u} (V : J → Opens Y)
      (ℱ : TopCat.Presheaf Ab Y) {p : ℕ} (i : Fin (p + 1) → J) (σ : Equiv.Perm (Fin (p + 1)))
      (x : (ℱ.obj (op (CechCochains.inter V i)) : Type _)),
      CechCochains.permIso V ℱ i σ x =
        CechCochains.restr ℱ (CechCochains.inter_comp_perm V i σ).le x := by
    intro Y J V ℱ p i σ x
    unfold CechCochains.permIso CechCochains.restr
    rw [Subsingleton.elim (eqToHom (by rw [CechCochains.inter_comp_perm V i σ]))
      (homOfLE (CechCochains.inter_comp_perm V i σ).le)]
  refine ⟨fun i hi ↦ ?_, fun i a b hab ↦ ?_⟩
  · have : ¬ Function.Injective (π ∘ i) := fun hinj ↦ hi hinj.of_comp
    simp only [cochainPullback, hs.1 _ this, map_zero]
  · have hswap : cochainPullback g U W π hW F p s (i ∘ Equiv.swap a b) =
        CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
          (inter_le_preimage_inter g U W π hW (i ∘ Equiv.swap a b))
          ((pullbackSections g F (CechCochains.inter U (π ∘ (i ∘ Equiv.swap a b))))
            (s (π ∘ (i ∘ Equiv.swap a b)))) := rfl
    have hid : cochainPullback g U W π hW F p s i =
        CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
          (inter_le_preimage_inter g U W π hW i)
          ((pullbackSections g F (CechCochains.inter U (π ∘ i))) (s (π ∘ i))) := rfl
    have key : s (π ∘ i ∘ Equiv.swap a b) = -CechCochains.restr F.presheaf
        (CechCochains.inter_comp_perm U (π ∘ i) (Equiv.swap a b)).le (s (π ∘ i)) :=
      (hs.2 (π ∘ i) a b hab).trans (by rw [permIso_eq_restr'])
    rw [hswap, hid, permIso_eq_restr', CechCochains.restr_restr, key, map_neg, map_neg]
    congr 1
    exact pullbackSections_restr g F (CechCochains.inter_comp_perm U (π ∘ i)
      (Equiv.swap a b)).le _ _ (s (π ∘ i))

variable {A : Type u} [CommRing A] (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A))
  (hgf : g ≫ f = f')

include hgf in
/-- **The comparison on Čech cochains is linear over the base ring.** -/
theorem cochainPullback_smul (p : ℕ) (a : A) (s : CechCochains.Cochain U F.presheaf p) :
    letI := cochainModule f U F p
    letI := cochainModule f' W ((Scheme.Modules.pullback g).obj F) p
    cochainPullback g U W π hW F p (a • s) = a • cochainPullback g U W π hW F p s := by
  let _ := cochainModule f U F p
  let _ := cochainModule f' W ((Scheme.Modules.pullback g).obj F) p
  funext i
  rw [cochain_smul_apply]
  have hL : cochainPullback g U W π hW F p (a • s) i =
      CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
        (inter_le_preimage_inter g U W π hW i)
        ((pullbackSections g F (CechCochains.inter U (π ∘ i))) ((a • s) (π ∘ i))) := rfl
  have hR : cochainPullback g U W π hW F p s i =
      CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
        (inter_le_preimage_inter g U W π hW i)
        ((pullbackSections g F (CechCochains.inter U (π ∘ i))) (s (π ∘ i))) := rfl
  rw [hL, hR, cochain_smul_apply, pullbackSections_smul]
  have hb := congr($(baseRingHom_comp_app_of_comp f f' g hgf
    (CechCochains.inter U (π ∘ i))).hom a)
  rw [CommRingCat.hom_comp] at hb
  change ((Scheme.Modules.pullback g).obj F).presheaf.map
      (homOfLE (inter_le_preimage_inter g U W π hW i)).op (_ • _) = _
  rw [show (g.app (CechCochains.inter U (π ∘ i))).hom
      ((baseRingHom f (CechCochains.inter U (π ∘ i))).hom a) =
      (baseRingHom f' (g ⁻¹ᵁ CechCochains.inter U (π ∘ i))).hom a from hb,
    Scheme.Modules.map_smul, map_baseRingHom_apply]
  rfl

/-- The comparison on alternating Čech cochains, as a map linear over the base ring. -/
def alternatingCochainRefinementPullbackₗ (p : ℕ) :
    letI := cochainModule f U F p
    letI := cochainModule f' W ((Scheme.Modules.pullback g).obj F) p
    alternatingSubmodule f U F p →ₗ[A]
      alternatingSubmodule f' W ((Scheme.Modules.pullback g).obj F) p :=
  letI := cochainModule f U F p
  letI := cochainModule f' W ((Scheme.Modules.pullback g).obj F) p
  { toFun := fun s ↦ ⟨cochainPullback g U W π hW F p s.1,
      cochainPullback_isAlternating g U W π hW F p s.1 s.2⟩
    map_add' := fun s t ↦ Subtype.ext (cochainPullback_add g U W π hW F p s.1 t.1)
    map_smul' := fun a s ↦ Subtype.ext (cochainPullback_smul g U W π hW F f f' hgf p a s.1) }

/-- **The morphism of alternating Čech complexes of `A`-modules induced by `g` and `π`.** -/
def alternatingCechModuleRefinementPullbackMap :
    alternatingCechModuleComplex f U F ⟶
      alternatingCechModuleComplex f' W ((Scheme.Modules.pullback g).obj F) where
  f p := ModuleCat.ofHom (alternatingCochainRefinementPullbackₗ g U W π hW F f f' hgf p)
  comm' := by
    rintro p q (rfl : p + 1 = q)
    rw [alternatingCechModuleComplex_d, alternatingCechModuleComplex_d]
    ext s
    exact Subtype.ext (cochainPullback_cechD g U W π hW F p s.1)

/-- **Restricting a section and then pulling it back is pulling it back and then
restricting.** -/
theorem alternatingCochainRefinementPullbackₗ_sectionsToAlternatingₗ {V : X.Opens}
    (hUV : ∀ i, U i ≤ V) (hWV : ∀ k, W k ≤ g ⁻¹ᵁ V) (s : Γ(F, V)) :
    alternatingCochainRefinementPullbackₗ g U W π hW F f f' hgf 0
        (sectionsToAlternatingₗ f U F hUV s) =
      sectionsToAlternatingₗ f' W ((Scheme.Modules.pullback g).obj F) hWV
        (pullbackSections g F V s) := by
  refine Subtype.ext (funext fun i => ?_)
  exact pullbackSections_restr g F (inter_le_of_le U hUV (π ∘ i))
    (inter_le_of_le W hWV i) (inter_le_preimage_inter g U W π hW i) s

end Stacks.Cech

end

end
