module

public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Stalk

/-!
# `X_{st} = X_s ∩ X_t`: multiplicativity of the nonvanishing loci

Let `X` be a scheme, `L` an invertible `𝒪_X`-module, and `s`, `t` global sections of the tensor
powers `L ^⊗ n` and `L ^⊗ m`. The nonvanishing locus of their product in the graded ring of
sections of Stacks Tag 01CV is the intersection of their nonvanishing loci, `X_{st} = X_s ∩ X_t`.
The product of the graded ring is also computed on homogeneous sections, on the carrier
`⨁_{n ≥ 0} Γ(X, L ^⊗ n)`.

## Main definitions

* `Stacks.SectionProduct.globalSection`: the global section attached to a morphism out of the
  monoidal unit, through the carrier comparison of
  `Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv`.

## Main results

* `Stacks.SectionProduct.mem_nonvanishingLocus_iff_generates`: a global section of an invertible
  module does not vanish at `x` exactly when its germ generates the stalk.
* `Stacks.SectionProduct.globalSection_mul`, `Stacks.SectionProduct.Γgerm_globalSection_mul`: the
  sectionwise product formula, on global sections and on germs.
* `Stacks.SectionProduct.nonvanishingLocus_mul`: `X_{st} = X_s ∩ X_t`, and
  `Stacks.SectionProduct.nonvanishingOpen_mul` is the same as an equality of open subsets.
* `Stacks.SectionProduct.gradedGlobalSections_of_mul`: the graded product of Stacks Tag 01CV on
  the carrier `⨁_{n ≥ 0} Γ(X, L ^⊗ n)`, computed on homogeneous sections.
* `Stacks.SectionProduct.isInvertibleModule_natTensorPow`: the nonnegative tensor powers of an
  invertible module are invertible.

## Implementation notes

`Stacks.SectionRingGeometric.gradedGlobalSectionsCommRing` is transported along an additive
equivalence by `Equiv.commRing`, so its `Add` is only propositionally equal to the direct sum's own
instance, and with that ring structure in scope a term mentioning the additive equivalence fails to
elaborate. `equiv_symm_mul_of` is therefore stated outside that scope, in terms of the underlying
`Equiv` alone.

`Stacks.SectionRingGeometric.schemePreadditive` and
`Stacks.SectionRingGeometric.schemeTensorRightAdditive` are local instances where they are
declared, and are reintroduced as local instances in the section that needs them.

Rewriting with `eq_triv_smul_res_basis` loops, since `u` also occurs inside the trivializing
function on its right-hand side.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory Category AlgebraicGeometry Opposite MonoidalCategory
  Stacks.SheafOfModules.TensorSheafification
open TopologicalSpace
open Stacks.ModuleStalk Stacks.Ample

universe u

namespace Stacks.SectionProduct

variable {X : Scheme.{u}}

/-! ### A trivialization through every point -/

/-- An invertible `𝒪_X`-module is sectionwise trivial on some open through any given point: this
is clause 2 of Stacks Tag 0B8M, localized at a point. -/
theorem exists_trivialization_at (M : X.Modules) [IsInvertibleModule X M] (x : X) :
    ∃ (V : X.Opens) (_ : x ∈ V),
      Nonempty (Stacks.SheafDescent.Trivialization X.presheaf M.val V) := by
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 M
  obtain ⟨z, hz⟩ : ∃ z : X, x ∈ V z := Opens.mem_iSup.mp (hV ▸ Opens.mem_top x)
  exact ⟨V z, hz, htriv z⟩

/-- The stalk of an invertible module is not killed by the maximal ideal: the basis section of a
trivialization through the point has germ outside `𝔪_x · M_x`. -/
theorem exists_notMem_maximalSmul (M : X.Modules) [IsInvertibleModule X M] (x : X) :
    ∃ z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x, z ∉ maximalSmul M x := by
  obtain ⟨V, hxV, ⟨t⟩⟩ := exists_trivialization_at M x
  exact ⟨_, Stacks.NonvanishingOpen.notMem_maximalSmul_germ_basis t hxV⟩

/-! ### Germs of sections of an invertible module -/

variable {M : X.Modules} {V : X.Opens}
  (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V)

/-- Every section of `M` over an open inside the trivializing open is its trivializing function
times the restricted basis section. This is `Stacks.NonvanishingOpen.eq_triv_smul_basis` over a
smaller open. -/
theorem eq_triv_smul_res_basis {W : X.Opens} (h : W ⟶ V) (u : Γ(M, W)) :
    u = Stacks.NonvanishingOpen.triv t h u •
      M.presheaf.map h.op (Stacks.NonvanishingOpen.basis t) := by
  refine (t.θ W h).injective ?_
  change Stacks.NonvanishingOpen.triv t h u = Stacks.NonvanishingOpen.triv t h _
  rw [Stacks.NonvanishingOpen.triv_smul, Stacks.NonvanishingOpen.triv_res_basis, mul_one]

/-- **The germ of the basis section generates the stalk.** -/
theorem exists_smul_germ_basis {x : X} (hx : x ∈ V)
    (z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    ∃ r : X.presheaf.stalk x,
      z = r • (M.presheaf.germ V x hx).hom (Stacks.NonvanishingOpen.basis t) := by
  obtain ⟨W, hWV, hxW, u, hu⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf z hx
  refine ⟨(X.presheaf.germ W x hxW).hom
    (Stacks.NonvanishingOpen.triv t (homOfLE hWV) u), ?_⟩
  have h1 : z = (M.presheaf.germ W x hxW).hom
      (Stacks.NonvanishingOpen.triv t (homOfLE hWV) u •
        M.presheaf.map (homOfLE hWV).op (Stacks.NonvanishingOpen.basis t)) := by
    rw [← eq_triv_smul_res_basis t (homOfLE hWV) u]
    exact hu.symm
  rw [h1, germ_smul, TopCat.Presheaf.germ_res_apply]

/-- The germ of a global section is its trivializing function times the germ of the basis
section. -/
theorem Γgerm_eq_smul_germ_basis (s : Γ(M, ⊤)) {x : X} (hx : x ∈ V) :
    (M.presheaf.Γgerm x).hom s =
      (X.presheaf.germ V x hx).hom (Stacks.NonvanishingOpen.trivTop t s) •
        (M.presheaf.germ V x hx).hom (Stacks.NonvanishingOpen.basis t) := by
  have hsV : M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s =
      Stacks.NonvanishingOpen.trivTop t s • Stacks.NonvanishingOpen.basis t :=
    Stacks.NonvanishingOpen.eq_triv_smul_basis t _
  rw [← TopCat.Presheaf.Γgerm_res_apply (i := homOfLE (le_top : V ≤ ⊤)) M.presheaf x hx s,
    hsV, germ_smul]

/-! ### Nonvanishing is generation of the stalk -/

/-- **The germ at `x` of a global section that does not vanish at `x` generates the stalk.** -/
theorem exists_smul_Γgerm (M : X.Modules) [IsInvertibleModule X M] (s : Γ(M, ⊤)) {x : X}
    (hx : x ∈ nonvanishingLocus M s)
    (z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    ∃ r : X.presheaf.stalk x, z = r • (M.presheaf.Γgerm x).hom s := by
  obtain ⟨V, hxV, ⟨t⟩⟩ := exists_trivialization_at M x
  obtain ⟨a, ha⟩ := (Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit t s hxV).mp hx
  obtain ⟨r, hr⟩ := exists_smul_germ_basis t hxV z
  refine ⟨r * ↑a⁻¹, ?_⟩
  rw [Γgerm_eq_smul_germ_basis t s hxV, ← ha, smul_smul, mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, mul_one]
  exact hr

/-- A stalk element that generates the stalk of an invertible module avoids `𝔪_x · M_x`. -/
theorem notMem_maximalSmul_of_generates (M : X.Modules) [IsInvertibleModule X M] (x : X)
    {z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x}
    (hz : ∀ w, ∃ r : X.presheaf.stalk x, w = r • z) : z ∉ maximalSmul M x := by
  intro hmem
  obtain ⟨w, hw⟩ := exists_notMem_maximalSmul M x
  obtain ⟨r, hr⟩ := hz w
  exact hw (hr ▸ Submodule.smul_mem _ r hmem)

/-- **A global section of an invertible module does not vanish at `x` exactly when its germ
generates the stalk there.** -/
theorem mem_nonvanishingLocus_iff_generates (M : X.Modules) [IsInvertibleModule X M]
    (s : Γ(M, ⊤)) (x : X) :
    x ∈ nonvanishingLocus M s ↔
      ∀ w : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x,
        ∃ r : X.presheaf.stalk x, w = r • (M.presheaf.Γgerm x).hom s :=
  ⟨fun hx => exists_smul_Γgerm M s hx, notMem_maximalSmul_of_generates M x⟩

/-- The stalk map of a morphism of modules carries `𝔪_x · M_x` into `𝔪_x · N_x`. -/
theorem mapFun_mem_maximalSmul {M N : X.Modules} (φ : M ⟶ N) (x : X)
    {z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x} (hz : z ∈ maximalSmul M x) :
    mapFun φ x z ∈ maximalSmul N x := by
  have hle : Submodule.map (Stacks.ModuleStalk.map φ x) (maximalSmul M x) ≤ maximalSmul N x := by
    rw [maximalSmul, maximalSmul, Submodule.map_smul'']
    exact smul_mono_right _ le_top
  exact hle (Submodule.mem_map_of_mem hz)

/-! ### Global sections of a morphism out of the monoidal unit -/

section Unit

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- The global section attached to a morphism out of the monoidal unit, through the carrier
comparison of `Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv`. -/
noncomputable def globalSection (X : Scheme.{u}) (F : X.Modules) (f : 𝟙_ X.Modules ⟶ F) :
    Γ(F, ⊤) :=
  Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X F f

/-- **The carrier comparison is compatible with composition.** -/
theorem globalSection_comp (F G : X.Modules) (f : 𝟙_ X.Modules ⟶ F) (g : F ⟶ G) :
    globalSection X G (f ≫ g) = g.app ⊤ (globalSection X F f) := rfl

/-- The germ at `x` of the global section of `f ≫ g` is the image under the stalk map of `g` of the
germ of the global section of `f`. -/
theorem Γgerm_globalSection_comp (F G : X.Modules) (f : 𝟙_ X.Modules ⟶ F) (g : F ⟶ G) (x : X) :
    (G.presheaf.Γgerm x).hom (globalSection X G (f ≫ g)) =
      mapFun g x ((F.presheaf.Γgerm x).hom (globalSection X F f)) := by
  rw [globalSection_comp, mapFun_Γgerm]

/-- **A morphism out of the monoidal unit is surjective on the stalk at `x` as soon as its global
section does not vanish at `x`.** -/
theorem surjStalk_of_mem_nonvanishingLocus (F : X.Modules) [IsInvertibleModule X F]
    (f : 𝟙_ X.Modules ⟶ F) (x : X)
    (hx : x ∈ nonvanishingLocus F (globalSection X F f)) : SurjStalk f x := by
  have key : mapFun f x (((𝟙_ X.Modules).presheaf.Γgerm x).hom
        (globalSection X (𝟙_ X.Modules) (𝟙 (𝟙_ X.Modules)))) =
      (F.presheaf.Γgerm x).hom (globalSection X F f) := by
    rw [← Γgerm_globalSection_comp, Category.id_comp]
  intro z
  obtain ⟨r, hr⟩ := exists_smul_Γgerm F (globalSection X F f) hx z
  exact ⟨r • _, by rw [mapFun_smul, key, hr]⟩

/-! ### Multiplicativity of the nonvanishing loci -/

section Mul

/-- **The sectionwise product formula, at the germ.** The germ of the global section of a product
is the image of the germ of the second factor under multiplication by the first. -/
theorem Γgerm_globalSection_mul (L : X.Modules) (n m : ℕ)
    (s : Stacks.GradedSections.powSections L n)
    (t : Stacks.GradedSections.powSections L m) (x : X) :
    ((Stacks.TensorPowers.natTensorPow L (n + m)).presheaf.Γgerm x).hom
        (globalSection X _ (Stacks.GradedSections.mul s t)) =
      mapFun (Stacks.GradedSections.mulMap s m) x
        (((Stacks.TensorPowers.natTensorPow L m).presheaf.Γgerm x).hom (globalSection X _ t)) :=
  Γgerm_globalSection_comp (Stacks.TensorPowers.natTensorPow L m)
    (Stacks.TensorPowers.natTensorPow L (n + m)) t (Stacks.GradedSections.mulMap s m) x

/-- **The sectionwise product formula.** The global section attached to a product of two
homogeneous elements of the graded ring of sections is the global section of the second factor
pushed through multiplication by the first. -/
theorem globalSection_mul (L : X.Modules) (n m : ℕ) (s : Stacks.GradedSections.powSections L n)
    (t : Stacks.GradedSections.powSections L m) :
    globalSection X _ (Stacks.GradedSections.mul s t) =
      (Stacks.GradedSections.mulMap s m).app ⊤ (globalSection X _ t) := rfl

/-- A product vanishes wherever its second factor does. -/
theorem nonvanishingLocus_mul_subset_right (L : X.Modules) (n m : ℕ)
    (s : Stacks.GradedSections.powSections L n)
    (t : Stacks.GradedSections.powSections L m) :
    nonvanishingLocus (Stacks.TensorPowers.natTensorPow L (n + m))
        (globalSection X _ (Stacks.GradedSections.mul s t)) ⊆
      nonvanishingLocus (Stacks.TensorPowers.natTensorPow L m) (globalSection X _ t) := by
  intro x hx
  rw [mem_nonvanishingLocus_iff] at hx ⊢
  intro hc
  exact hx ((Γgerm_globalSection_mul L n m s t x).symm ▸
    mapFun_mem_maximalSmul (Stacks.GradedSections.mulMap s m) x hc)

variable (L : X.Modules) [IsInvertibleModule X L]

/-- Every nonnegative tensor power of an invertible module is invertible. -/
instance isInvertibleModule_natTensorPow (n : ℕ) :
    IsInvertibleModule X (Stacks.TensorPowers.natTensorPow L n) :=
  isInvertibleModule_tensorPowModule X L (n : ℤ)

/-- The nonvanishing locus of a product does not depend on the order of the factors. -/
theorem nonvanishingLocus_mul_comm (n m : ℕ) (s : Stacks.GradedSections.powSections L n)
    (t : Stacks.GradedSections.powSections L m) :
    nonvanishingLocus (Stacks.TensorPowers.natTensorPow L (m + n))
        (globalSection X _ (Stacks.GradedSections.mul t s)) =
      nonvanishingLocus (Stacks.TensorPowers.natTensorPow L (n + m))
        (globalSection X _ (Stacks.GradedSections.mul s t)) := by
  have he : Stacks.GradedSections.mul t s =
      Stacks.GradedSections.mul s t ≫
        Stacks.GradedSections.powCongr L (Nat.add_comm n m) :=
    (Stacks.GradedSections.mul_comm' s t).symm
  rw [he, globalSection_comp]
  exact nonvanishingLocus_congr
    (eqToIso (congrArg (Stacks.TensorPowers.natTensorPow L) (Nat.add_comm n m))) _

/-- **`X_{st} = X_s ∩ X_t`.** The nonvanishing locus of a product of two global sections of
tensor powers of an invertible module is the intersection of the nonvanishing loci of the
factors. -/
theorem nonvanishingLocus_mul (n m : ℕ) (s : Stacks.GradedSections.powSections L n)
    (t : Stacks.GradedSections.powSections L m) :
    nonvanishingLocus (Stacks.TensorPowers.natTensorPow L (n + m))
        (globalSection X _ (Stacks.GradedSections.mul s t)) =
      nonvanishingLocus (Stacks.TensorPowers.natTensorPow L n) (globalSection X _ s) ∩
        nonvanishingLocus (Stacks.TensorPowers.natTensorPow L m) (globalSection X _ t) := by
  refine Set.Subset.antisymm (Set.subset_inter ?_ (nonvanishingLocus_mul_subset_right L n m s t))
    ?_
  · rw [← nonvanishingLocus_mul_comm L n m s t]
    exact nonvanishingLocus_mul_subset_right L m n t s
  · rintro x ⟨hs, ht⟩
    rw [mem_nonvanishingLocus_iff]
    refine notMem_maximalSmul_of_generates _ x fun w => ?_
    obtain ⟨v, hv⟩ := surjStalk_mulMap L n s x
      (surjStalk_of_mem_nonvanishingLocus _ s x hs) m w
    obtain ⟨r, hrv⟩ := exists_smul_Γgerm (Stacks.TensorPowers.natTensorPow L m)
      (globalSection X _ t) ht v
    exact ⟨r, by rw [← hv, hrv, mapFun_smul, Γgerm_globalSection_mul]⟩

/-- **`X_{st} = X_s ∩ X_t`, in the bundled shape**: an equality of open subsets. -/
theorem nonvanishingOpen_mul (n m : ℕ) (s : Stacks.GradedSections.powSections L n)
    (t : Stacks.GradedSections.powSections L m) :
    Stacks.NonvanishingOpen.nonvanishingOpen X (Stacks.TensorPowers.natTensorPow L (n + m))
        (globalSection X _ (Stacks.GradedSections.mul s t)) =
      Stacks.NonvanishingOpen.nonvanishingOpen X (Stacks.TensorPowers.natTensorPow L n)
          (globalSection X _ s) ⊓
        Stacks.NonvanishingOpen.nonvanishingOpen X (Stacks.TensorPowers.natTensorPow L m)
          (globalSection X _ t) :=
  Opens.ext (nonvanishingLocus_mul L n m s t)

end Mul

/-! ### The product on the carrier of Tag 01CV -/

section Carrier

variable (L : X.Modules)

attribute [local instance] Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.SectionRingGeometric.schemeSectionCommRing

/-- The graded product of Stacks Tag 01CV on homogeneous elements. -/
theorem of_mul_of (n m : ℕ) (s : Stacks.GradedSections.powSections L n)
    (t : Stacks.GradedSections.powSections L m) :
    DirectSum.of (Stacks.GradedSections.powSections L) n s *
        DirectSum.of (Stacks.GradedSections.powSections L) m t =
      DirectSum.of (Stacks.GradedSections.powSections L) (n + m)
        (Stacks.GradedSections.mul s t) :=
  DirectSum.of_mul_of s t

/-- The equivalence `Stacks.SectionRingGeometric.gradedGlobalSectionsAddEquiv` sends a homogeneous
element to the corresponding homogeneous global section. -/
theorem gradedGlobalSectionsEquiv_of (k : ℕ) (a : Stacks.GradedSections.powSections L k) :
    (Stacks.SectionRingGeometric.gradedGlobalSectionsAddEquiv X L).toEquiv
        (DirectSum.of (Stacks.GradedSections.powSections L) k a) =
      DirectSum.of (fun i : ℕ => Γ(Stacks.TensorPowers.natTensorPow L i, ⊤)) k
        (globalSection X _ a) :=
  DirectSum.map_of _ k a

/-- The product of two homogeneous global sections, computed through the inverse of
`Stacks.SectionRingGeometric.gradedGlobalSectionsAddEquiv`, is the global section of
`Stacks.GradedSections.mul s t`. -/
theorem equiv_symm_mul_of (n m : ℕ) (s : Stacks.GradedSections.powSections L n)
    (t : Stacks.GradedSections.powSections L m) :
    ((Stacks.SectionRingGeometric.gradedGlobalSectionsAddEquiv X L).toEquiv.symm).symm
        (((Stacks.SectionRingGeometric.gradedGlobalSectionsAddEquiv X L).toEquiv.symm)
            (DirectSum.of (fun i : ℕ => Γ(Stacks.TensorPowers.natTensorPow L i, ⊤)) n
              (globalSection X _ s)) *
          ((Stacks.SectionRingGeometric.gradedGlobalSectionsAddEquiv X L).toEquiv.symm)
            (DirectSum.of (fun i : ℕ => Γ(Stacks.TensorPowers.natTensorPow L i, ⊤)) m
              (globalSection X _ t))) =
      DirectSum.of (fun i : ℕ => Γ(Stacks.TensorPowers.natTensorPow L i, ⊤)) (n + m)
        (globalSection X _ (Stacks.GradedSections.mul s t)) := by
  rw [← gradedGlobalSectionsEquiv_of L n s, ← gradedGlobalSectionsEquiv_of L m t,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, of_mul_of, Equiv.symm_symm]
  exact gradedGlobalSectionsEquiv_of L (n + m) (Stacks.GradedSections.mul s t)

/-- **The graded product of Stacks Tag 01CV on the carrier `⨁_{n ≥ 0} Γ(X, L ^⊗ n)`**, on
homogeneous sections: the product of the global sections of `s` and `t` in degrees `n` and `m` is
the global section of `Stacks.GradedSections.mul s t` in degree `n + m`. -/
theorem gradedGlobalSections_of_mul [IsInvertibleModule X L] (n m : ℕ)
    (s : Stacks.GradedSections.powSections L n)
    (t : Stacks.GradedSections.powSections L m) :
    letI := Stacks.SectionRingGeometric.gradedGlobalSectionsCommRing X L
    DirectSum.of (fun i : ℕ => Γ(Stacks.TensorPowers.natTensorPow L i, ⊤)) n
          (globalSection X _ s) *
        DirectSum.of (fun i : ℕ => Γ(Stacks.TensorPowers.natTensorPow L i, ⊤)) m
          (globalSection X _ t) =
      DirectSum.of (fun i : ℕ => Γ(Stacks.TensorPowers.natTensorPow L i, ⊤)) (n + m)
        (globalSection X _ (Stacks.GradedSections.mul s t)) :=
  (Equiv.mul_def (Stacks.SectionRingGeometric.gradedGlobalSectionsAddEquiv X L).toEquiv.symm _
    _).trans (equiv_symm_mul_of L n m s t)

end Carrier

end Unit

end Stacks.SectionProduct

end
