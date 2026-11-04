module

public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution

/-!
# Dimension shifting for `Tor` when only one second variable is acyclic

`Tor_iso_Tor'.lesShift00M3` shifts the degree of `Tor` along a short exact sequence `S` of first
variables whose middle term is *flat*, so that `Tor_j(S.X₂, -)` vanishes for every second
variable at once. The shift is already available at a single second variable `M`, on the sole
hypothesis that `Tor_k(S.X₂, M)` and `Tor_{k+1}(S.X₂, M)` vanish: flatness of `S.X₂` is used for
nothing else. This file records that weakening for the connecting map `torDelta`, together with
the naturality square of `torDelta` in the *second* variable, which
`StacksFrontier.RingTheory.Tor.AlmostFlatResolution` does not provide — it needs only naturality in
the first variable.

The point of the weakening is that a module which is not flat can still have `Tor_j(-, M) = 0`
for the particular `M` of interest: for a flat ring map `A → R` and an `R`-module `M` which is
flat over `A`, every `R ⊗_A V` has `Tor_j^R(R ⊗_A V, M) = 0` in positive degrees, whatever `V`
is. Such modules are what occur as the terms of a resolution by scalar extensions, and those
resolutions are not by projectives, so the flat form of the shift does not apply to them.

## Main results

* `torDelta_naturality`: the connecting map `Tor_{k+1}(S.X₃, -) ⟶ Tor_k(S.X₁, -)` is natural in
  the second variable.
* `mono_torDelta`, `isIso_torDelta`: it is a monomorphism as soon as `Tor_{k+1}(S.X₂, M)`
  vanishes, and an isomorphism as soon as `Tor_k(S.X₂, M)` vanishes too.
* `torDelta_comp_tor_map_f_eq_zero`, `torShortComplexExact₁`: the composite with the map induced
  by `S.f` on `Tor_k` is zero, and that two term sequence is exact.
* `tor_map_eq_zero_of_shift`: the vanishing of the map induced by `g` on `Tor_k(S.X₁, -)`
  transfers to `Tor_{k+1}(S.X₃, -)`, when the shift is an isomorphism at the target of `g`.
* `tor_succ_map_eq_zero_of_delta`: `Tor_{k+1}(S.X₃, g) = 0` as soon as `Tor_k(S.X₁, g)` kills the
  kernel of `Tor_k(S.f, -)` and `Tor_{k+1}(S.X₂, -)` vanishes at the target of `g`. This is the
  form used at the bottom of the sequence, where the shift is not an isomorphism.

## Implementation notes

Everything is read off `lesShift.ses A S hS M`, the degreewise tensor product of `S` with the
chosen projective resolution of `M`, which is short exact on `hS` alone: the flatness used there
is that of the terms of the resolution of `M`. Transport between its homology and `Tor` is
`torIsoHomology`, and the naturality proof in the second variable is that of
`lesShift.comp_naturality` with the flatness instance removed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

universe u

variable {A : Type u} [CommRing A]

section

variable (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact) (k : ℕ)

private lemma downRel : (ComplexShape.down ℕ).Rel (k + 1) k := by simp [ComplexShape.down_Rel]

/-- `torDelta` unfolded: it is the connecting map of `lesShift.ses`, transported along
`torIsoHomology`. -/
private lemma torDelta_eq (M : ModuleCat.{u} A) :
    torDelta S hS M k = (torIsoHomology S.X₃ M (k + 1)).hom ≫
      (lesShift.ses A S hS M).δ (k + 1) k (downRel k) ≫ (torIsoHomology S.X₁ M k).inv := rfl

/-- Naturality of the connecting map `torDelta` in the **second** variable. -/
theorem torDelta_naturality {M M' : ModuleCat.{u} A} (g : M ⟶ M') :
    ((Tor (ModuleCat.{u} A) (k + 1)).obj S.X₃).map g ≫ torDelta S hS M' k
      = torDelta S hS M k ≫ ((Tor (ModuleCat.{u} A) k).obj S.X₁).map g := by
  let φ := ProjectiveResolution.lift g (projectiveResolution M) (projectiveResolution M')
  have hφ : φ.f 0 ≫ (projectiveResolution M').π.f 0 = (projectiveResolution M).π.f 0 ≫ g :=
    ProjectiveResolution.lift_commutes_zero g _ _
  let ψ : (S.map (lesShift.phi A (projectiveResolution M).complex)) ⟶
      (S.map (lesShift.phi A (projectiveResolution M').complex)) :=
    S.mapNatTrans ((lesShift.phiBi A).flip.map φ)
  have hA : ((Tor (ModuleCat.{u} A) (k + 1)).obj S.X₃).map g ≫
        (torIsoHomology S.X₃ M' (k + 1)).hom
      = (torIsoHomology S.X₃ M (k + 1)).hom ≫
        HomologicalComplex.homologyMap ψ.τ₃ (k + 1) :=
    ProjectiveResolution.isoLeftDerivedObj_hom_naturality g
      (projectiveResolution M) (projectiveResolution M') φ hφ (tensorLeft S.X₃) (k + 1)
  have hC : ((Tor (ModuleCat.{u} A) k).obj S.X₁).map g ≫ (torIsoHomology S.X₁ M' k).hom
      = (torIsoHomology S.X₁ M k).hom ≫ HomologicalComplex.homologyMap ψ.τ₁ k :=
    ProjectiveResolution.isoLeftDerivedObj_hom_naturality g
      (projectiveResolution M) (projectiveResolution M') φ hφ (tensorLeft S.X₁) k
  have hB := lesShift.δ_naturality A (lesShift.ses A S hS M) (lesShift.ses A S hS M')
    ψ (k + 1) k (downRel k)
  have hC' : HomologicalComplex.homologyMap ψ.τ₁ k ≫ (torIsoHomology S.X₁ M' k).inv
      = (torIsoHomology S.X₁ M k).inv ≫ ((Tor (ModuleCat.{u} A) k).obj S.X₁).map g :=
    lesShift.comp_inv_eq_inv_comp_of_comm _ _ _ _ hC
  rw [torDelta_eq, torDelta_eq]
  simp only [Category.assoc]
  rw [← Category.assoc, hA, Category.assoc,
    ← Category.assoc (HomologicalComplex.homologyMap ψ.τ₃ (k + 1)), ← hB, Category.assoc, hC']

variable (M : ModuleCat.{u} A)

/-- The connecting map is a monomorphism as soon as `Tor_{k+1}(S.X₂, M)` vanishes. -/
theorem mono_torDelta (h : IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj S.X₂).obj M)) :
    Mono (torDelta S hS M k) :=
  (torShortComplexExact₃ S hS M k).mono_g (h.eq_of_src _ _)

/-- The composite of the connecting map with the map induced by `S.f` on `Tor_k` is zero. -/
theorem torDelta_comp_tor_map_f_eq_zero :
    torDelta S hS M k ≫ ((Tor (ModuleCat.{u} A) k).map S.f).app M = 0 := by
  have hδ : (lesShift.ses A S hS M).δ (k + 1) k (downRel k) ≫
      HomologicalComplex.homologyMap
        ((lesShift.phi A (projectiveResolution M).complex).map S.f) k = 0 :=
    (lesShift.ses A S hS M).δ_comp (k + 1) k (downRel k)
  rw [torDelta_eq, Category.assoc, Category.assoc, ← torIsoHomology_inv_naturality S.f M k,
    ← Category.assoc ((lesShift.ses A S hS M).δ (k + 1) k (downRel k)), hδ, zero_comp, comp_zero]

/-- The segment `Tor_{k+1}(S.X₃, M) → Tor_k(S.X₁, M) → Tor_k(S.X₂, M)` of the long exact
sequence of a short exact sequence of first variables. -/
noncomputable def torShortComplexDelta₁ : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (torDelta S hS M k) (((Tor (ModuleCat.{u} A) k).map S.f).app M)
    (torDelta_comp_tor_map_f_eq_zero S hS k M)

/-- Exactness of `Tor_{k+1}(S.X₃, M) → Tor_k(S.X₁, M) → Tor_k(S.X₂, M)`. -/
theorem torShortComplexExact₁ : (torShortComplexDelta₁ S hS k M).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((lesShift.ses A S hS M).homology_exact₁ (k + 1) k (downRel k))
  refine ShortComplex.isoMk (torIsoHomology S.X₃ M (k + 1)).symm
    (torIsoHomology S.X₁ M k).symm (torIsoHomology S.X₂ M k).symm ?_
    (torIsoHomology_inv_naturality S.f M k).symm
  show (torIsoHomology S.X₃ M (k + 1)).inv ≫ torDelta S hS M k
    = (lesShift.ses A S hS M).δ (k + 1) k (downRel k) ≫ (torIsoHomology S.X₁ M k).inv
  rw [torDelta_eq, Iso.inv_hom_id_assoc]

/-- The connecting map is an isomorphism as soon as both flanking `Tor` groups of the middle
term vanish at `M`. -/
theorem isIso_torDelta (h : IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj S.X₂).obj M))
    (h' : IsZero (((Tor (ModuleCat.{u} A) k).obj S.X₂).obj M)) :
    IsIso (torDelta S hS M k) :=
  have := mono_torDelta S hS k M h
  have : Epi (torDelta S hS M k) :=
    (torShortComplexExact₁ S hS k M).epi_f (h'.eq_of_tgt _ _)
  isIso_of_mono_of_epi _

end

section

variable (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact) (k : ℕ)
  {M M' : ModuleCat.{u} A} (g : M ⟶ M')

include hS in
/-- Transfer of vanishing across the dimension shift: if `g` induces the zero map on
`Tor_k(S.X₁, -)` and the connecting map is an isomorphism at `M'`, then `g` induces the zero map
on `Tor_{k+1}(S.X₃, -)`. -/
theorem tor_map_eq_zero_of_shift
    (h : IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj S.X₂).obj M'))
    (h' : IsZero (((Tor (ModuleCat.{u} A) k).obj S.X₂).obj M'))
    (hzero : ((Tor (ModuleCat.{u} A) k).obj S.X₁).map g = 0) :
    ((Tor (ModuleCat.{u} A) (k + 1)).obj S.X₃).map g = 0 := by
  have := isIso_torDelta S hS k M' h h'
  have hnat := torDelta_naturality S hS k g
  rw [hzero, comp_zero] at hnat
  exact (cancel_mono (torDelta S hS M' k)).mp (by simpa using hnat)

include hS in
/-- The form of the transfer used at the bottom of the long exact sequence, where the connecting
map need not be an isomorphism: it is enough that `Tor_k(S.X₁, g)` kills the kernel of
`Tor_k(S.f, M)`, together with the vanishing which makes the connecting map at `M'` a
monomorphism. -/
theorem tor_succ_map_eq_zero_of_delta
    (h : IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj S.X₂).obj M'))
    (hker : ∀ z : ((Tor (ModuleCat.{u} A) k).obj S.X₁).obj M,
      ((Tor (ModuleCat.{u} A) k).map S.f).app M z = 0 →
        (((Tor (ModuleCat.{u} A) k).obj S.X₁).map g) z = 0) :
    ((Tor (ModuleCat.{u} A) (k + 1)).obj S.X₃).map g = 0 := by
  have := mono_torDelta S hS k M' h
  have key : torDelta S hS M k ≫ ((Tor (ModuleCat.{u} A) k).obj S.X₁).map g = 0 := by
    apply ModuleCat.hom_ext
    ext x
    have hx := ConcreteCategory.congr_hom (torDelta_comp_tor_map_f_eq_zero S hS k M) x
    refine (hker (torDelta S hS M k x) ?_).trans ?_
    · simpa [ConcreteCategory.comp_apply] using hx
    · rfl
  refine (cancel_mono (torDelta S hS M' k)).mp ?_
  rw [torDelta_naturality S hS k g, key, zero_comp]

end

end
