module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksCore.Algebra.Homology.ShortComplex.SnakeLemma
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SupportedWeightOperator
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Irreducible
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Vanishing
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Functoriality
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Graded
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.TopIdeals.Basic
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroupImageKernel

/-!
# Dévissage for coherent modules with supports along a closed immersion

Let `i : X ⟶ Y` be a closed immersion into a Noetherian scheme `Y`, let `ℐ ⊆ 𝒪_Y` be its ideal
sheaf and let `Z ⊆ X` be a closed subset, with image `i(Z) ⊆ Y`. Direct image is an exact,
fully faithful functor `Coh_Z(X) ⥤ Coh_{i(Z)}(Y)` from the coherent `𝒪_X`-modules supported in
`Z` to the coherent `𝒪_Y`-modules supported in `i(Z)`. Its essential image consists of the
modules killed by `ℐ`, and every object `ℱ` of `Coh_{i(Z)}(Y)` is killed by a power of `ℐ`,
so the filtration `ℱ ⊇ ℐℱ ⊇ ℐ²ℱ ⊇ ⋯` is finite with graded pieces in the essential image. The
induced homomorphism

  `K₀(Coh_Z(X)) ⟶ K₀(Coh_{i(Z)}(Y))`

is therefore an isomorphism, with inverse `[ℱ] ↦ ∑ₚ [ℐᵖℱ / ℐᵖ⁺¹ℱ]`. This is [Stacks, Tag 0FDT]
in the form with supports. The isomorphisms are compatible with the inclusions `Z' ⊆ Z`, so after
tensoring with `𝐐` they form a natural isomorphism of functors on the closed subsets of `X`.
Finally, the length of the stalk of `i_*ℱ` at `i(ξ)` is the length of `ℱ_ξ`, so direct image
preserves the multiplicities `Stacks.Chow.sheafMultiplicity`.

The dévissage itself is proved for an arbitrary fully faithful functor `Φ : 𝒜 ⥤ 𝒞` of abelian
categories equipped with a *nilpotent radical*: a subfunctor `M ↦ ℛM` of the identity of `𝒞`,
preserving epimorphisms, vanishing on the essential image of `Φ`, whose quotients `M / ℛM` lie
in that essential image, and such that every object is killed by an iterate. Then every
homomorphism `K₀(𝒜) ⟶ K₀(𝒞)` with `[A] ↦ [Φ A]`, which exists as soon as `Φ` is exact, is
bijective.

## Main definitions

* `CategoryTheory.KZero.Devissage` — a nilpotent radical for `Φ : 𝒜 ⥤ 𝒞`, the input of the
  abstract dévissage.
* `CategoryTheory.KZero.Devissage.inv` — the inverse `K₀(𝒞) ⟶ K₀(𝒜)`,
  `[M] ↦ ∑ₚ [ℛᵖM / ℛᵖ⁺¹M]`.
* `AlgebraicGeometry.Scheme.Hom.closedImageFunctor` — the functor `Z ↦ f(Z)` on closed subsets,
  for `f` universally closed.
* `Stacks.Chow.supportedCoherentPushforward` — direct image `Coh_Z(X) ⥤ Coh_{i(Z)}(Y)`.
* `Stacks.Chow.supportedCoherentKZeroPushforward` — the induced homomorphism
  `K₀(Coh_Z(X)) ⟶ K₀(Coh_{i(Z)}(Y))`.
* `Stacks.Chow.supportedCoherentIdealSmul` — multiplication `M ↦ ℐM` by an ideal sheaf, as an
  endofunctor of `Coh_W(Y)`, with its inclusion `Stacks.Chow.supportedCoherentIdealSmulι`.
* `Stacks.Chow.supportedCoherentKZeroPushforwardEquiv` — the isomorphism of K-groups.
* `Stacks.Chow.supportedCoherentKZeroRatPushforwardIso` — the natural isomorphism
  `𝐐 ⊗ K₀(Coh_Z(X)) ≅ 𝐐 ⊗ K₀(Coh_{i(Z)}(Y))` of functors on the closed subsets of `X`.

## Main results

* `CategoryTheory.ShortComplex.shortExact_cokernelShortComplex_of_mono` — the cokernels of a
  monomorphism of short exact sequences form a short exact sequence.
* `CategoryTheory.KZero.Devissage.bijective` — the abstract dévissage.
* `Stacks.Chow.supportedCoherentKZeroPushforward_mk` — the homomorphism on classes.
* `Stacks.Chow.bijective_supportedCoherentKZeroPushforward` — [Stacks, Tag 0FDT] with supports.
* `Stacks.Chow.supportedCoherentKZeroPushforward_comp_map` — compatibility with the maps induced
  by inclusions of closed subsets.
* `Stacks.Chow.sheafMultiplicity_pushforward_of_isClosedImmersion` — direct image along a closed
  immersion preserves multiplicities.

## Implementation notes

The inverse is not built from the source's double filtration `ℐᵖℱ ∩ ℐ^q𝒢`. It is defined by the
recursion `c(M) = [M/ℛM] + c(ℛM)`, which terminates because `ℛ` is nilpotent, and two facts are
proved by induction on the nilpotency index. First, for a subobject `ℛN ⊆ K ⊆ N` one has
`c(N) = [N/K] + c(K)`: the induction alternates between the pairs `(N, K)` and `(K, ℛN)`.
Second, for a short exact sequence `0 → F → G → H → 0` one has `c(G) = c(F) + c(H)`: the
radical maps `ℛG` onto `ℛH` with kernel `K`, and the snake lemma, applied to the monomorphism of
short exact sequences `(K → ℛG → ℛH) ⟶ (F → G → H)`, gives the short exact sequence
`0 → F/K → G/ℛG → H/ℛH → 0`, while `ℛF ⊆ K ⊆ F` brings the first fact to bear.

For the closed immersion the radical is multiplication by `ℐ = ker i`,
`Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul`, whose sections over an affine open `U`
are `ℐ(U) · Γ(M, U)`. That `M/ℐM` is a direct image is [Stacks, Tag 087T] together with
`Stacks.AlgebraicGeometry.IrreducibleDevissage.smul_top_cokernel_idealPowStep`, and the
nilpotency is [Stacks, Tag 01Y9] applied to the vanishing ideal of `i(Z)`, which contains `ℐ`;
both use that `Y` is Noetherian, i.e. locally Noetherian and quasi-compact.

The image `i(Z)` is `AlgebraicGeometry.Scheme.Hom.closedImage`, the image of a closed subset
under a universally closed morphism.

Local Noetherianity of `X` follows from that of `Y` by
`AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion`; it is nevertheless taken as an
instance argument wherever `K₀(Coh_Z(X))` appears, since the abelian structure of `Coh_Z(X)` is
found by instance search.

## References

* [Stacks Project, Tag 0FDT](https://stacks.math.columbia.edu/tag/0FDT)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

/-! ### Cokernels of a monomorphism of short exact sequences -/

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category C] [Abelian C]

/-- **The cokernels of a monomorphism of short exact sequences are short exact.** For a morphism
`φ : S₁ ⟶ S₂` of short exact sequences whose three components are monomorphisms, the induced
sequence `0 → coker φ.τ₁ → coker φ.τ₂ → coker φ.τ₃ → 0` is short exact. This is the snake lemma:
the kernel row vanishes, so the connecting map out of `ker φ.τ₃ = 0` is zero. -/
theorem shortExact_cokernelShortComplex_of_mono {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [Mono φ.τ₁] [Mono φ.τ₂] [Mono φ.τ₃] :
    (S₂.cokernelShortComplex φ.comm₁₂ φ.comm₂₃).ShortExact := by
  let SI : SnakeInput C :=
    { L₀ := ShortComplex.mk (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) (by simp)
      L₁ := S₁
      L₂ := S₂
      L₃ := S₂.cokernelShortComplex φ.comm₁₂ φ.comm₂₃
      v₀₁ := 0
      v₁₂ := φ
      v₂₃ :=
        { τ₁ := cokernel.π φ.τ₁
          τ₂ := cokernel.π φ.τ₂
          τ₃ := cokernel.π φ.τ₃
          comm₁₂ := by simp
          comm₂₃ := by simp }
      w₀₂ := zero_comp
      w₁₃ := by ext <;> simp
      h₀ := by
        refine ShortComplex.isLimitOfIsLimitπ _ ?_ ?_ ?_
        · exact (KernelFork.isLimitMapConeEquiv _ _).symm <| KernelFork.IsLimit.ofMonoOfIsZero _
            (inferInstanceAs (Mono φ.τ₁)) (Limits.isZero_zero C)
        · exact (KernelFork.isLimitMapConeEquiv _ _).symm <| KernelFork.IsLimit.ofMonoOfIsZero _
            (inferInstanceAs (Mono φ.τ₂)) (Limits.isZero_zero C)
        · exact (KernelFork.isLimitMapConeEquiv _ _).symm <| KernelFork.IsLimit.ofMonoOfIsZero _
            (inferInstanceAs (Mono φ.τ₃)) (Limits.isZero_zero C)
      h₃ := by
        apply ShortComplex.isColimitOfIsColimitπ <;>
          exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm (cokernelIsCokernel _)
      L₁_exact := h₁.exact
      epi_L₁_g := h₁.epi_g
      L₂_exact := h₂.exact
      mono_L₂_f := h₂.mono_f }
  have hmono : Mono SI.L₃.f := SI.L₂'_exact.mono_g ((Limits.isZero_zero C).eq_of_src _ _)
  have : Epi SI.L₂.g := h₂.epi_g
  exact ShortComplex.ShortExact.mk' SI.L₃_exact hmono SI.epi_L₃_g

end CategoryTheory.ShortComplex

/-! ### The abstract dévissage -/

namespace CategoryTheory.KZero

variable {𝒜 𝒞 : Type*} [Category 𝒜] [Category 𝒞] [Abelian 𝒞]

/-- **A nilpotent radical for a functor `Φ : 𝒜 ⥤ 𝒞` of abelian categories**, the input of the
dévissage `CategoryTheory.KZero.Devissage.bijective`: a subfunctor `M ↦ ℛM` of the identity of
`𝒞` which preserves epimorphisms and vanishes on the essential image of `Φ`, such that every
quotient `M / ℛM` lies in that essential image and every object is killed by an iterate of `ℛ`.
The model is multiplication `M ↦ ℐM` by the ideal sheaf of a closed subscheme, for `Φ` the direct
image from the closed subscheme. -/
structure Devissage (Φ : 𝒜 ⥤ 𝒞) where
  /-- The radical `M ↦ ℛM`. -/
  rad : 𝒞 ⥤ 𝒞
  /-- The inclusion `ℛM ⟶ M`. -/
  ι : rad ⟶ 𝟭 𝒞
  /-- `ℛM` is a subobject of `M`. -/
  mono_ι (M : 𝒞) : Mono (ι.app M)
  /-- The radical preserves epimorphisms. -/
  epi_rad_map {M N : 𝒞} (f : M ⟶ N) : Epi f → Epi (rad.map f)
  /-- The quotient `M / ℛM` lies in the essential image of `Φ`. -/
  essImage_cokernel_ι (M : 𝒞) : Φ.essImage (cokernel (ι.app M))
  /-- The radical vanishes on the image of `Φ`. -/
  isZero_rad_obj_obj (A : 𝒜) : IsZero (rad.obj (Φ.obj A))
  /-- The radical is nilpotent: every object is killed by an iterate. -/
  exists_isZero_rad_iterate (M : 𝒞) : ∃ n : ℕ, IsZero (rad.obj^[n] M)

namespace Devissage

variable {Φ : 𝒜 ⥤ 𝒞} (D : Devissage Φ)

/-- The inclusion `ℛM ⟶ M` is a monomorphism. -/
instance (M : 𝒞) : Mono (D.ι.app M) := D.mono_ι M

/-- The naturality square of the inclusion `ℛ ⟶ 𝟭`. -/
theorem rad_map_comp_ι {M N : 𝒞} (f : M ⟶ N) : D.rad.map f ≫ D.ι.app N = D.ι.app M ≫ f :=
  D.ι.naturality f

/-- The radical preserves monomorphisms. -/
instance mono_rad_map {M N : 𝒞} (f : M ⟶ N) [Mono f] : Mono (D.rad.map f) :=
  mono_of_mono_fac (D.rad_map_comp_ι f)

/-- The radical preserves zero morphisms, being a subfunctor of the identity. -/
instance : D.rad.PreservesZeroMorphisms where
  map_zero M N := by
    rw [← cancel_mono (D.ι.app N), D.rad_map_comp_ι]
    simp

/-- The radical of the inclusion `ℛM ⟶ M` is the inclusion `ℛℛM ⟶ ℛM`. -/
theorem rad_map_ι_app (M : 𝒞) : D.rad.map (D.ι.app M) = D.ι.app (D.rad.obj M) := by
  rw [← cancel_mono (D.ι.app M)]
  exact D.rad_map_comp_ι (D.ι.app M)

/-- If `j : K ⟶ N` is a monomorphism through which `ℛN ⟶ N` factors as `h ≫ j`, then
`ℛK ⟶ K` factors through `h` as `ℛ(j) ≫ h`. -/
theorem rad_map_comp_eq_ι {N K : 𝒞} (j : K ⟶ N) [Mono j] {h : D.rad.obj N ⟶ K}
    (hj : h ≫ j = D.ι.app N) : D.rad.map j ≫ h = D.ι.app K := by
  rw [← cancel_mono j, Category.assoc, hj]
  exact D.rad_map_comp_ι j

/-- The radical of a zero object is zero. -/
theorem isZero_rad_obj {M : 𝒞} (h : IsZero M) : IsZero (D.rad.obj M) :=
  IsZero.of_mono (D.ι.app M) h

/-- Every iterated radical of a zero object is zero. -/
theorem isZero_rad_iterate {M : 𝒞} (h : IsZero M) (n : ℕ) : IsZero (D.rad.obj^[n] M) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact D.isZero_rad_obj ih

/-- If `ℛM = 0`, then `ℛN = 0` for every quotient `N` of `M`. -/
theorem isZero_rad_obj_of_epi {M N : 𝒞} (p : M ⟶ N) [Epi p] (h : IsZero (D.rad.obj M)) :
    IsZero (D.rad.obj N) :=
  have := D.epi_rad_map p inferInstance
  IsZero.of_epi (D.rad.map p) h

/-- The radical of `M / ℛM` vanishes, `M / ℛM` lying in the essential image of `Φ`. -/
theorem isZero_rad_obj_cokernel (M : 𝒞) : IsZero (D.rad.obj (cokernel (D.ι.app M))) :=
  IsZero.of_iso (D.isZero_rad_obj_obj _) (D.rad.mapIso (D.essImage_cokernel_ι M).getIso).symm

/-- An object with vanishing radical lies in the essential image of `Φ`. -/
theorem essImage_of_isZero_rad_obj {M : 𝒞} (h : IsZero (D.rad.obj M)) : Φ.essImage M :=
  have := cokernel.π_of_zero (h.eq_of_src (D.ι.app M) 0)
  Functor.essImage.ofIso (asIso (cokernel.π (D.ι.app M))).symm (D.essImage_cokernel_ι M)

/-- If `ℛN ⟶ N` factors through a monomorphism `j : K ⟶ N`, then `N / K` lies in the essential
image of `Φ`: it is a quotient of `N / ℛN`. -/
theorem essImage_cokernel_of_fac {N K : 𝒞} (j : K ⟶ N) (h : D.rad.obj N ⟶ K)
    (hj : h ≫ j = D.ι.app N) : Φ.essImage (cokernel j) :=
  have hw : D.ι.app N ≫ cokernel.π j = 0 := by
    rw [← hj, Category.assoc, cokernel.condition, comp_zero]
  have : Epi (cokernel.desc (D.ι.app N) (cokernel.π j) hw) :=
    epi_of_epi_fac (cokernel.π_desc _ _ _)
  D.essImage_of_isZero_rad_obj (D.isZero_rad_obj_of_epi
    (cokernel.desc (D.ι.app N) (cokernel.π j) hw) (D.isZero_rad_obj_cokernel N))

/-! #### Classes of objects of the essential image -/

variable [Abelian 𝒜]

omit [Abelian 𝒞] in
/-- The class in `K₀(𝒜)` of an object of the essential image of `Φ`. -/
def cls {Q : 𝒞} (h : Φ.essImage Q) : KZero 𝒜 := KZero.mk 𝒜 h.witness

variable [Φ.Full] [Φ.Faithful]

omit [Abelian 𝒞] in
/-- The class of `Q ≅ Φ A` is `[A]`. -/
theorem cls_eq_mk {Q : 𝒞} (h : Φ.essImage Q) {A : 𝒜} (e : Φ.obj A ≅ Q) :
    cls h = KZero.mk 𝒜 A :=
  KZero.mk_eq_of_iso (Φ.preimageIso (h.getIso ≪≫ e.symm))

omit [Abelian 𝒞] in
/-- Isomorphic objects of the essential image have the same class. -/
theorem cls_eq_of_iso {Q Q' : 𝒞} (h : Φ.essImage Q) (h' : Φ.essImage Q') (e : Q ≅ Q') :
    cls h = cls h' :=
  cls_eq_mk h (h'.getIso ≪≫ e.symm)

omit [Abelian 𝒞] in
/-- A zero object has class zero. -/
theorem cls_eq_zero {Q : 𝒞} (h : Φ.essImage Q) (hQ : IsZero Q) : cls h = 0 :=
  KZero.mk_eq_zero_of_isZero
    (IsZero.of_full_of_faithful_of_isZero Φ _ (IsZero.of_iso hQ h.getIso))

/-- The class in `K₀(𝒜)` is additive along short exact sequences of `𝒞` whose terms lie in the
essential image of `Φ`: the sequence is the image of one in `𝒜`, by fullness, and a faithful
functor reflects short exactness. -/
theorem cls_add {S : ShortComplex 𝒞} (hS : S.ShortExact) (h₁ : Φ.essImage S.X₁)
    (h₂ : Φ.essImage S.X₂) (h₃ : Φ.essImage S.X₃) : cls h₂ = cls h₁ + cls h₃ := by
  let e₁ := h₁.getIso
  let e₂ := h₂.getIso
  let e₃ := h₃.getIso
  let S' : ShortComplex 𝒜 := ShortComplex.mk (Φ.preimage (e₁.hom ≫ S.f ≫ e₂.inv))
    (Φ.preimage (e₂.hom ≫ S.g ≫ e₃.inv)) (Φ.map_injective (by simp))
  let e : S'.map Φ ≅ S := ShortComplex.isoMk e₁ e₂ e₃ (by simp [S']) (by simp [S'])
  exact KZero.mk_of_shortExact S' (ShortExact.reflects_shortExact_of_faithful Φ
    (ShortComplex.shortExact_of_iso e.symm hS))

/-- For monomorphisms `h : X ⟶ Y` and `j : Y ⟶ Z`, the third isomorphism theorem
`0 → Y/X → Z/X → Z/Y → 0` gives `[Z/X] = [Y/X] + [Z/Y]`, for quotients in the essential image. -/
theorem cls_cokernel_comp {X Y Z : 𝒞} (h : X ⟶ Y) (j : Y ⟶ Z) [Mono h] [Mono j]
    (h₁ : Φ.essImage (cokernel h)) (h₂ : Φ.essImage (cokernel (h ≫ j)))
    (h₃ : Φ.essImage (cokernel j)) : cls h₂ = cls h₁ + cls h₃ := by
  let S₁ : ShortComplex 𝒞 := ShortComplex.mk (𝟙 X) (0 : X ⟶ 0) (by simp)
  let S₂ : ShortComplex 𝒞 := ShortComplex.mk j (cokernel.π j) (by simp)
  have hS₁ : S₁.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _
      (CokernelCofork.IsColimit.ofEpiOfIsZero _ (by dsimp [S₁]; infer_instance)
        (Limits.isZero_zero 𝒞))) (by dsimp [S₁]; infer_instance) (by dsimp [S₁]; infer_instance)
  have hS₂ : S₂.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) (by dsimp [S₂]; infer_instance)
    (by dsimp [S₂]; infer_instance)
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := h
      τ₂ := h ≫ j
      τ₃ := 0
      comm₁₂ := by simp [S₁, S₂]
      comm₂₃ := by simp [S₁, S₂] }
  have : Mono φ.τ₁ := inferInstanceAs (Mono h)
  have : Mono φ.τ₂ := inferInstanceAs (Mono (h ≫ j))
  have : Mono φ.τ₃ := ⟨fun _ _ _ => (Limits.isZero_zero 𝒞).eq_of_tgt _ _⟩
  rw [cls_add (ShortComplex.shortExact_cokernelShortComplex_of_mono φ hS₁ hS₂) h₁ h₂
    (Functor.essImage.ofIso (asIso (cokernel.π φ.τ₃)) h₃)]
  congr 1
  exact cls_eq_of_iso _ _ (asIso (cokernel.π φ.τ₃)).symm

/-! #### The inverse on objects -/

/-- The class `[M / ℛM]` in `K₀(𝒜)`. -/
def grClass (M : 𝒞) : KZero 𝒜 := cls (D.essImage_cokernel_ι M)

/-- The class `[M / ℛM]` of a zero object vanishes. -/
theorem grClass_eq_zero {M : 𝒞} (h : IsZero M) : D.grClass M = 0 :=
  cls_eq_zero _ (IsZero.of_epi (cokernel.π _) h)

/-- The partial sum `∑_{p < n} [ℛᵖM / ℛᵖ⁺¹M]` in `K₀(𝒜)`. -/
def grSum (n : ℕ) (M : 𝒞) : KZero 𝒜 := ∑ k ∈ Finset.range n, D.grClass (D.rad.obj^[k] M)

/-- Once `ℛⁿM = 0`, the partial sums are constant from `n` on. -/
theorem grSum_add {n : ℕ} {M : 𝒞} (h : IsZero (D.rad.obj^[n] M)) (d : ℕ) :
    D.grSum (n + d) M = D.grSum n M := by
  rw [grSum, Finset.sum_range_add, grSum, add_eq_left]
  refine Finset.sum_eq_zero fun k _ => D.grClass_eq_zero ?_
  rw [add_comm, Function.iterate_add_apply]
  exact D.isZero_rad_iterate h k

/-- **The inverse on objects**, `M ↦ ∑ₚ [ℛᵖM / ℛᵖ⁺¹M]`, the sum running up to any `n` with
`ℛⁿM = 0` (`CategoryTheory.KZero.Devissage.invObj_eq`). -/
def invObj (M : 𝒞) : KZero 𝒜 := D.grSum (D.exists_isZero_rad_iterate M).choose M

/-- The inverse on objects is the partial sum up to any `n` with `ℛⁿM = 0`. -/
theorem invObj_eq {n : ℕ} {M : 𝒞} (h : IsZero (D.rad.obj^[n] M)) :
    D.invObj M = D.grSum n M := by
  have h' := (D.exists_isZero_rad_iterate M).choose_spec
  set m := (D.exists_isZero_rad_iterate M).choose
  rw [invObj, ← D.grSum_add h' (n - m), ← D.grSum_add h (m - n)]
  congr 1
  omega

/-- The inverse on objects vanishes on a zero object. -/
theorem invObj_eq_zero {M : 𝒞} (h : IsZero M) : D.invObj M = 0 := by
  rw [D.invObj_eq (n := 0) h, grSum, Finset.sum_range_zero]

/-- The recursion `c(M) = [M / ℛM] + c(ℛM)`. -/
theorem invObj_eq_grClass_add (M : 𝒞) : D.invObj M = D.grClass M + D.invObj (D.rad.obj M) := by
  obtain ⟨n, hn⟩ := D.exists_isZero_rad_iterate M
  have hn' : IsZero (D.rad.obj^[n + 1] M) := by
    rw [Function.iterate_succ_apply']
    exact D.isZero_rad_obj hn
  have hn'' : IsZero (D.rad.obj^[n] (D.rad.obj M)) := by
    rwa [← Function.iterate_succ_apply]
  rw [D.invObj_eq hn', D.invObj_eq hn'', grSum, Finset.sum_range_succ', add_comm, grSum]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]

/-- One step of `CategoryTheory.KZero.Devissage.invObj_eq_cls_add`: the formula for the pair
`(K, ℛN)` implies the formula for the pair `(N, K)`. -/
theorem invObj_eq_cls_add_of_step {N K : 𝒞} (j : K ⟶ N) [Mono j] (h : D.rad.obj N ⟶ K)
    (hj : h ≫ j = D.ι.app N)
    (H : D.invObj K = cls (D.essImage_cokernel_of_fac h (D.rad.map j)
      (D.rad_map_comp_eq_ι j hj)) + D.invObj (D.rad.obj N)) :
    D.invObj N = cls (D.essImage_cokernel_of_fac j h hj) + D.invObj K := by
  have : Mono h := mono_of_mono_fac hj
  have hg : D.grClass N = cls (D.essImage_cokernel_of_fac h (D.rad.map j)
      (D.rad_map_comp_eq_ι j hj)) + cls (D.essImage_cokernel_of_fac j h hj) := by
    rw [grClass, cls_eq_of_iso _ (Functor.essImage.ofIso (cokernelIsoOfEq hj).symm
      (D.essImage_cokernel_ι N)) (cokernelIsoOfEq hj).symm]
    exact cls_cokernel_comp h j _ _ _
  rw [D.invObj_eq_grClass_add N, hg, H]
  abel

/-- `CategoryTheory.KZero.Devissage.invObj_eq_cls_add` for `N` with `ℛⁿN = 0`, by induction on
`n`, two steps of `CategoryTheory.KZero.Devissage.invObj_eq_cls_add_of_step` at a time. -/
theorem invObj_eq_cls_add_aux (n : ℕ) : ∀ {N K : 𝒞} (j : K ⟶ N) [Mono j]
    (h : D.rad.obj N ⟶ K) (hj : h ≫ j = D.ι.app N), IsZero (D.rad.obj^[n] N) →
      D.invObj N = cls (D.essImage_cokernel_of_fac j h hj) + D.invObj K := by
  induction n with
  | zero =>
    intro N K j _ h hj hN
    rw [Function.iterate_zero_apply] at hN
    have hK : IsZero K := IsZero.of_mono j hN
    rw [D.invObj_eq_zero hN, D.invObj_eq_zero hK,
      cls_eq_zero _ (IsZero.of_epi (cokernel.π j) hN), add_zero]
  | succ n ih =>
    intro N K j _ h hj hN
    have : Mono h := mono_of_mono_fac hj
    refine D.invObj_eq_cls_add_of_step j h hj
      (D.invObj_eq_cls_add_of_step h (D.rad.map j) (D.rad_map_comp_eq_ι j hj) ?_)
    refine ih (D.rad.map j) (D.rad.map h) (D.rad_map_comp_eq_ι h (D.rad_map_comp_eq_ι j hj)) ?_
    rwa [← Function.iterate_succ_apply]

/-- **The key formula.** If `j : K ⟶ N` is a monomorphism through which `ℛN ⟶ N` factors, i.e.
`ℛN ⊆ K ⊆ N`, then `c(N) = [N/K] + c(K)`. -/
theorem invObj_eq_cls_add {N K : 𝒞} (j : K ⟶ N) [Mono j] (h : D.rad.obj N ⟶ K)
    (hj : h ≫ j = D.ι.app N) :
    D.invObj N = cls (D.essImage_cokernel_of_fac j h hj) + D.invObj K :=
  D.invObj_eq_cls_add_aux (D.exists_isZero_rad_iterate N).choose j h hj
    (D.exists_isZero_rad_iterate N).choose_spec

/-- `CategoryTheory.KZero.Devissage.invObj_add` for a middle term `X₂` with `ℛⁿX₂ = 0`, by
induction on `n`. -/
theorem invObj_add_aux (n : ℕ) : ∀ (S : ShortComplex 𝒞), S.ShortExact →
    IsZero (D.rad.obj^[n] S.X₂) → D.invObj S.X₂ = D.invObj S.X₁ + D.invObj S.X₃ := by
  induction n with
  | zero =>
    intro S hS h
    rw [Function.iterate_zero_apply] at h
    have := hS.mono_f
    have := hS.epi_g
    rw [D.invObj_eq_zero h, D.invObj_eq_zero (IsZero.of_mono S.f h),
      D.invObj_eq_zero (IsZero.of_epi S.g h), add_zero]
  | succ n ih =>
    intro S hS h
    have := hS.mono_f
    have := hS.epi_g
    have := D.epi_rad_map S.g inferInstance
    -- the short exact sequence `0 → K → ℛX₂ → ℛX₃ → 0`
    let S' : ShortComplex 𝒞 := ShortComplex.mk (kernel.ι (D.rad.map S.g)) (D.rad.map S.g)
      (kernel.condition _)
    have hS' : S'.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _)
      (by dsimp [S']; infer_instance) (by dsimp [S']; infer_instance)
    have h' : IsZero (D.rad.obj^[n] S'.X₂) := by dsimp [S']; rwa [← Function.iterate_succ_apply]
    -- the comparison `K ⟶ X₁`, through which `ℛX₁ ⟶ X₁` factors
    have hw : (kernel.ι (D.rad.map S.g) ≫ D.ι.app S.X₂) ≫ S.g = 0 := by
      rw [Category.assoc, ← D.rad_map_comp_ι, ← Category.assoc, kernel.condition, zero_comp]
    let u : kernel (D.rad.map S.g) ⟶ S.X₁ := hS.exact.lift _ hw
    have hu : u ≫ S.f = kernel.ι (D.rad.map S.g) ≫ D.ι.app S.X₂ := hS.exact.lift_f _ hw
    have : Mono u := mono_of_mono_fac hu
    let v : D.rad.obj S.X₁ ⟶ kernel (D.rad.map S.g) := kernel.lift _ (D.rad.map S.f)
      (by rw [← D.rad.map_comp, S.zero, D.rad.map_zero])
    have hv : v ≫ u = D.ι.app S.X₁ := by
      rw [← cancel_mono S.f, Category.assoc, hu, ← Category.assoc, kernel.lift_ι]
      exact D.rad_map_comp_ι S.f
    -- the monomorphism of short exact sequences `S' ⟶ S` and its cokernels
    let φ : S' ⟶ S :=
      { τ₁ := u
        τ₂ := D.ι.app S.X₂
        τ₃ := D.ι.app S.X₃
        comm₁₂ := hu
        comm₂₃ := (D.rad_map_comp_ι S.g).symm }
    have : Mono φ.τ₁ := inferInstanceAs (Mono u)
    have : Mono φ.τ₂ := inferInstanceAs (Mono (D.ι.app S.X₂))
    have : Mono φ.τ₃ := inferInstanceAs (Mono (D.ι.app S.X₃))
    have e₃ := cls_add (ShortComplex.shortExact_cokernelShortComplex_of_mono φ hS' hS)
      (D.essImage_cokernel_of_fac u v hv) (D.essImage_cokernel_ι S.X₂)
      (D.essImage_cokernel_ι S.X₃)
    rw [D.invObj_eq_grClass_add S.X₂, D.invObj_eq_grClass_add S.X₃, D.invObj_eq_cls_add u v hv]
    change D.grClass S.X₂ + D.invObj S'.X₂ = _
    rw [ih S' hS' h', grClass, e₃, grClass]
    abel

/-- **Additivity of the inverse on objects** along short exact sequences of `𝒞`. -/
theorem invObj_add (S : ShortComplex 𝒞) (hS : S.ShortExact) :
    D.invObj S.X₂ = D.invObj S.X₁ + D.invObj S.X₃ :=
  D.invObj_add_aux _ S hS (D.exists_isZero_rad_iterate S.X₂).choose_spec

/-! #### The inverse homomorphism -/

/-- **The inverse of dévissage**, `K₀(𝒞) ⟶ K₀(𝒜)`, `[M] ↦ ∑ₚ [ℛᵖM / ℛᵖ⁺¹M]`. -/
def inv : KZero 𝒞 →+ KZero 𝒜 := KZero.lift D.invObj D.invObj_add

/-- The inverse of dévissage on the class of an object. -/
@[simp]
theorem inv_mk (M : 𝒞) : D.inv (KZero.mk 𝒞 M) = D.invObj M := KZero.lift_mk _ _ _

/-- The inverse on objects sends `Φ A` to `[A]`: the radical of `Φ A` vanishes. -/
theorem invObj_obj (A : 𝒜) : D.invObj (Φ.obj A) = KZero.mk 𝒜 A := by
  rw [D.invObj_eq_grClass_add, D.invObj_eq_zero (D.isZero_rad_obj_obj A), add_zero, grClass]
  have := cokernel.π_of_zero ((D.isZero_rad_obj_obj A).eq_of_src (D.ι.app (Φ.obj A)) 0)
  exact cls_eq_mk _ (asIso (cokernel.π (D.ι.app (Φ.obj A))))

/-- A homomorphism `[A] ↦ [Φ A]` sends the inverse of `M` back to `[M]`, by the short exact
sequences `0 → ℛM → M → M/ℛM → 0`. -/
theorem map_invObj (φ : KZero 𝒜 →+ KZero 𝒞)
    (hφ : ∀ A, φ (KZero.mk 𝒜 A) = KZero.mk 𝒞 (Φ.obj A)) (M : 𝒞) :
    φ (D.invObj M) = KZero.mk 𝒞 M := by
  obtain ⟨n, hn⟩ := D.exists_isZero_rad_iterate M
  induction n generalizing M with
  | zero =>
    rw [Function.iterate_zero_apply] at hn
    rw [D.invObj_eq_zero hn, map_zero, KZero.mk_eq_zero_of_isZero hn]
  | succ n ih =>
    rw [D.invObj_eq_grClass_add, map_add,
      ih (D.rad.obj M) (by rwa [← Function.iterate_succ_apply]), grClass, cls, hφ,
      show KZero.mk 𝒞 M = KZero.mk 𝒞 (D.rad.obj M) + KZero.mk 𝒞 (cokernel (D.ι.app M))
        from KZero.mk_eq_add_cokernel (D.ι.app M), add_comm]
    exact congrArg _ (KZero.mk_eq_of_iso (D.essImage_cokernel_ι M).getIso)

/-- The inverse is a left inverse of any homomorphism `[A] ↦ [Φ A]`. -/
theorem inv_comp (φ : KZero 𝒜 →+ KZero 𝒞)
    (hφ : ∀ A, φ (KZero.mk 𝒜 A) = KZero.mk 𝒞 (Φ.obj A)) :
    D.inv.comp φ = AddMonoidHom.id _ :=
  KZero.hom_ext fun A => by rw [AddMonoidHom.comp_apply, hφ, inv_mk, invObj_obj]; rfl

/-- The inverse is a right inverse of any homomorphism `[A] ↦ [Φ A]`. -/
theorem comp_inv (φ : KZero 𝒜 →+ KZero 𝒞)
    (hφ : ∀ A, φ (KZero.mk 𝒜 A) = KZero.mk 𝒞 (Φ.obj A)) :
    φ.comp D.inv = AddMonoidHom.id _ :=
  KZero.hom_ext fun M => by rw [AddMonoidHom.comp_apply, inv_mk, D.map_invObj φ hφ]; rfl

include D in
/-- **Dévissage.** Let `Φ : 𝒜 ⥤ 𝒞` be a fully faithful functor of abelian categories carrying a
nilpotent radical `CategoryTheory.KZero.Devissage`. Then the homomorphism `K₀(𝒜) ⟶ K₀(𝒞)`,
`[A] ↦ [Φ A]`, is bijective. -/
theorem bijective (φ : KZero 𝒜 →+ KZero 𝒞)
    (hφ : ∀ A, φ (KZero.mk 𝒜 A) = KZero.mk 𝒞 (Φ.obj A)) : Function.Bijective φ :=
  Function.bijective_iff_has_inverse.mpr ⟨D.inv, fun x => DFunLike.congr_fun (D.inv_comp φ hφ) x,
    fun y => DFunLike.congr_fun (D.comp_inv φ hφ) y⟩

end Devissage

end CategoryTheory.KZero

open AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

/-! ### Images of closed subsets -/

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f]

/-- The image of a closed subset under a universally closed morphism grows with the subset. -/
theorem closedImage_mono : Monotone f.closedImage :=
  fun _ _ h => Set.image_mono h

/-- The monotone map `Z ↦ f(Z)` on closed subsets, for `f` universally closed, as a functor. -/
def closedImageFunctor : Closeds X ⥤ Closeds Y :=
  (closedImage_mono f).functor

/-- The functor `Z ↦ f(Z)` on objects. -/
@[simp]
theorem closedImageFunctor_obj (Z : Closeds X) : f.closedImageFunctor.obj Z = f.closedImage Z :=
  rfl

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Chow

/-! ### Multiplication by an ideal sheaf on coherent modules with supports -/

section IdealSmul

variable {Y : Scheme.{u}} (I : Y.IdealSheafData)

/-- `I ^ n • (-)` preserves identities. -/
theorem idealPowSmulMap_id (n : ℕ) (A : Y.Modules) [A.IsQuasicoherent] :
    idealPowSmulMap I n (𝟙 A) = 𝟙 _ :=
  Mono.right_cancellation (f := (idealPowSmul I n A).ι) _ _
    ((idealPowSmulMap_comp_ι I n (𝟙 A)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- `I ^ n • (-)` preserves composition. -/
theorem idealPowSmulMap_comp (n : ℕ) {A B C : Y.Modules} [A.IsQuasicoherent]
    [B.IsQuasicoherent] [C.IsQuasicoherent] (f : A ⟶ B) (g : B ⟶ C) :
    idealPowSmulMap I n (f ≫ g) = idealPowSmulMap I n f ≫ idealPowSmulMap I n g :=
  Mono.right_cancellation (f := (idealPowSmul I n C).ι) _ _ <|
    (idealPowSmulMap_comp_ι I n (f ≫ g)).trans <|
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g) (idealPowSmulMap_comp_ι I n f).symm)).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (idealPowSmulMap I n f ≫ ·) (idealPowSmulMap_comp_ι I n g).symm).trans
          (Category.assoc _ _ _).symm

/-- A section over an affine open `U` lies in `I ^ n • A` iff it is in `I(U) ^ n • Γ(A, U)`. -/
private theorem mem_idealPowSmul_iff (n : ℕ) (A : Y.Modules) [A.IsQuasicoherent]
    (U : Y.affineOpens) (x : Γ(A, U.1)) :
    x ∈ (idealPowSmul I n A).toSubmodule.obj (op U.1) ↔
      x ∈ I.ideal U ^ n • (⊤ : Submodule Γ(Y, U.1) Γ(A, U.1)) := by
  rw [obj_idealPowSmul]; exact Iff.rfl

/-- **`I ^ n • (-)` preserves epimorphisms of quasi-coherent modules.** Over an affine open `V`
an epimorphism of quasi-coherent modules is surjective on sections, so it maps
`I(V) ^ n • Γ(A, V)` onto `I(V) ^ n • Γ(B, V)`, and the affine opens form a basis. -/
theorem epi_idealPowSmulMap (n : ℕ) {A B : Y.Modules} [A.IsQuasicoherent] [B.IsQuasicoherent]
    (f : A ⟶ B) (hf : Epi f) : Epi (idealPowSmulMap I n f) := by
  have := hf
  refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun U t x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  let t' := (idealPowSmul I n B).toSheafOfModules.val.map (homOfLE hVU).op t
  have ht' : t'.val ∈ I.ideal ⟨V, hV⟩ ^ n • (⊤ : Submodule Γ(Y, V) Γ(B, V)) :=
    (mem_idealPowSmul_iff I n B ⟨V, hV⟩ _).mp t'.property
  have hsurj : Function.Surjective (f.app V) :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen Y f V hV
  have hlift : ∀ y ∈ I.ideal ⟨V, hV⟩ ^ n • (⊤ : Submodule Γ(Y, V) Γ(B, V)),
      ∃ s ∈ I.ideal ⟨V, hV⟩ ^ n • (⊤ : Submodule Γ(Y, V) Γ(A, V)), f.app V s = y := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun a ha b _ => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
    · obtain ⟨b', rfl⟩ := hsurj b
      exact ⟨a • b', Submodule.smul_mem_smul ha Submodule.mem_top,
        Scheme.Modules.Hom.app_smul _ _ _⟩
    · obtain ⟨x₁, hx₁, rfl⟩ := h₁
      obtain ⟨x₂, hx₂, rfl⟩ := h₂
      exact ⟨x₁ + x₂, Submodule.add_mem _ hx₁ hx₂, map_add _ _ _⟩
  obtain ⟨s, hs, hfs⟩ := hlift _ ht'
  exact ⟨V, hVU, hxV, ⟨s, (mem_idealPowSmul_iff I n A ⟨V, hV⟩ _).mpr hs⟩, Subtype.ext hfs⟩

/-- If `I ^ n` kills the sections of `F` over every affine open, then `I ^ n • F` is zero. -/
theorem isZero_idealPowSmul_of_smul_eq_zero (n : ℕ) (F : Y.Modules) [F.IsQuasicoherent]
    (h : ∀ (U : Y.affineOpens) (a : Γ(Y, U)), a ∈ I.ideal U ^ n → ∀ m : Γ(F, U), a • m = 0) :
    IsZero (idealPowSmul I n F).toSheafOfModules := by
  refine Stacks.Coherent.isZero_of_affine_sections _ fun U => ?_
  have hz : ∀ x ∈ I.ideal U ^ n • (⊤ : Submodule Γ(Y, U.1) Γ(F, U.1)), x = 0 := fun x hx =>
    (Submodule.mem_bot _).mp (Submodule.smul_le.mpr
      (fun a ha m _ => (Submodule.mem_bot _).mpr (h U a ha m)) hx)
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => Subtype.ext ?_⟩
  rw [hz _ ((mem_idealPowSmul_iff I n F U _).mp x.property),
    hz _ ((mem_idealPowSmul_iff I n F U _).mp y.property)]

/-- If `I ^ n • F` is zero, then `I ^ n` kills the sections of `F` over every affine open. -/
theorem smul_eq_zero_of_isZero_idealPowSmul (n : ℕ) (F : Y.Modules) [F.IsQuasicoherent]
    (hF : IsZero (idealPowSmul I n F).toSheafOfModules) (U : Y.affineOpens) (a : Γ(Y, U))
    (ha : a ∈ I.ideal U ^ n) (m : Γ(F, U)) : a • m = 0 := by
  have hm : a • m ∈ (idealPowSmul I n F).toSubmodule.obj (op U.1) :=
    (mem_idealPowSmul_iff I n F U _).mpr (Submodule.smul_mem_smul ha Submodule.mem_top)
  have := Stacks.subsingleton_of_isZero hF (op U.1)
  exact congrArg Subtype.val (@Subsingleton.elim _ this ⟨a • m, hm⟩ 0)

/-- **`F / I • F` is killed by `I`**, read on any module isomorphic to it: the quotient is the
first graded piece of the `I`-adic filtration, which
`Stacks.AlgebraicGeometry.IrreducibleDevissage.smul_top_cokernel_idealPowStep` shows is killed
by `I(U)` over every affine open `U`. -/
theorem smul_eq_zero_of_iso_cokernel_idealPowSmul [IsNoetherian Y] (F : Y.Modules)
    [F.IsQuasicoherent] [F.IsCoherent] {Q : Y.Modules} (e : Q ≅ cokernel (idealPowSmul I 1 F).ι)
    (U : Y.affineOpens) (a : Γ(Y, U)) (ha : a ∈ I.ideal U) (m : Γ(Q, U)) : a • m = 0 := by
  have : IsIso (idealPowSmulHom I 0 F) :=
    Stacks.AlgebraicGeometry.IrreducibleDevissage.isIso_idealPowSmulHom_zero I F
  let e' : cokernel (idealPowSmul I 1 F).ι ≅
      cokernel (Stacks.AlgebraicGeometry.IrreducibleDevissage.idealPowStep I F 0) :=
    (cokernelIsoOfEq
      (Stacks.AlgebraicGeometry.IrreducibleDevissage.idealPowStep_comp_hom I F 0)).symm ≪≫
      @cokernelCompIsIso _ _ _ _ _ _ _ _ _ this
  refine Stacks.Sheaves.PushforwardEssentialImage.smul_eq_zero_of_iso (e ≪≫ e').symm _ a
    (fun n => ?_) m
  have h := Stacks.AlgebraicGeometry.IrreducibleDevissage.smul_top_cokernel_idealPowStep I F 0 U
  exact Submodule.smul_le.mp h.le a ha n Submodule.mem_top

variable (W : Set Y)

/-- The underlying `𝒪_Y`-module of an object of `Coh_W(Y)`. -/
abbrev supportedCoherentModule {W : Set Y} (M : (coherentSupportedIn W).FullSubcategory) :
    Y.Modules :=
  M.obj.obj

/-- An object of `Coh_W(Y)` is coherent. -/
instance isCoherent_supportedCoherentModule (M : (coherentSupportedIn W).FullSubcategory) :
    (supportedCoherentModule M).IsCoherent :=
  CoherentAbelian.isCoherent_of_stacksIsCoherent M.obj.property

/-- An object of `Coh_W(Y)` is quasi-coherent. -/
instance isQuasicoherent_supportedCoherentModule
    (M : (coherentSupportedIn W).FullSubcategory) :
    (supportedCoherentModule M).IsQuasicoherent :=
  isQuasicoherent_of_isCoherent _

variable {W} in
/-- Morphisms of `Coh_W(Y)` are determined by the underlying morphisms of `𝒪_Y`-modules. -/
theorem supportedCoherent_hom_ext {M N : (coherentSupportedIn W).FullSubcategory} {f g : M ⟶ N}
    (h : f.hom.hom = g.hom.hom) : f = g := by
  ext1; ext1; exact h

variable [IsLocallyNoetherian Y]

/-- The object `I • M` of `Coh_W(Y)`: it is coherent because `Y` is locally Noetherian, and it is
supported in `W` because it is a subsheaf of `M`. -/
def supportedCoherentIdealSmulObj (M : (coherentSupportedIn W).FullSubcategory) :
    (coherentSupportedIn W).FullSubcategory :=
  ⟨⟨(idealPowSmul I 1 (supportedCoherentModule M)).toSheafOfModules,
    CoherentAbelian.stacksIsCoherent_of_isCoherent (isCoherent_idealPowSmul I 1 _)⟩,
    (Stacks.AlgebraicGeometry.Tag01YHTopIdeals.supp_subset_of_mono
      (idealPowSmul I 1 (supportedCoherentModule M)).ι
      (inferInstanceAs (Mono (idealPowSmul I 1 (supportedCoherentModule M)).ι))).trans
      M.property⟩

/-- **Multiplication `M ↦ I • M` by an ideal sheaf**, as an endofunctor of the coherent
`𝒪_Y`-modules supported in `W`. -/
def supportedCoherentIdealSmul :
    (coherentSupportedIn W).FullSubcategory ⥤ (coherentSupportedIn W).FullSubcategory where
  obj := supportedCoherentIdealSmulObj I W
  map f := ObjectProperty.homMk (ObjectProperty.homMk (idealPowSmulMap I 1 f.hom.hom))
  map_id M := supportedCoherent_hom_ext (idealPowSmulMap_id I 1 (supportedCoherentModule M))
  map_comp f g := supportedCoherent_hom_ext (idealPowSmulMap_comp I 1 f.hom.hom g.hom.hom)

/-- The underlying module of `I • M` is the subsheaf `I • M` of `M`. -/
@[simp]
theorem supportedCoherentModule_supportedCoherentIdealSmul_obj
    (M : (coherentSupportedIn W).FullSubcategory) :
    supportedCoherentModule ((supportedCoherentIdealSmul I W).obj M) =
      (idealPowSmul I 1 (supportedCoherentModule M)).toSheafOfModules :=
  rfl

/-- Multiplication by `I` on morphisms is the morphism induced on `I`-multiples. -/
@[simp]
theorem supportedCoherentIdealSmul_map_hom_hom {M N : (coherentSupportedIn W).FullSubcategory}
    (f : M ⟶ N) :
    ((supportedCoherentIdealSmul I W).map f).hom.hom = idealPowSmulMap I 1 f.hom.hom :=
  rfl

/-- The inclusion `I • M ⟶ M`, natural in `M`. -/
def supportedCoherentIdealSmulι : supportedCoherentIdealSmul I W ⟶ 𝟭 _ where
  app M := ObjectProperty.homMk (ObjectProperty.homMk (idealPowSmul I 1 M.obj.obj).ι)
  naturality _ _ f := supportedCoherent_hom_ext (idealPowSmulMap_comp_ι I 1 f.hom.hom)

/-- The inclusion `I • M ⟶ M` is the inclusion of the subsheaf. -/
@[simp]
theorem supportedCoherentIdealSmulι_app_hom_hom (M : (coherentSupportedIn W).FullSubcategory) :
    ((supportedCoherentIdealSmulι I W).app M).hom.hom =
      (idealPowSmul I 1 (supportedCoherentModule M)).ι :=
  rfl

/-- The inclusion `I • M ⟶ M` is a monomorphism. -/
instance (M : (coherentSupportedIn W).FullSubcategory) :
    Mono ((supportedCoherentIdealSmulι I W).app M) := by
  have : Mono (((coherentSupportedIn W).ι ⋙ (Stacks.SheafOfModules.coherentModules
      Y.ringCatSheaf).ι).map ((supportedCoherentIdealSmulι I W).app M)) :=
    inferInstanceAs (Mono (idealPowSmul I 1 (supportedCoherentModule M)).ι)
  exact Functor.mono_of_mono_map _ this

/-- Multiplication by `I` preserves epimorphisms of `Coh_W(Y)`, for `W` closed. -/
theorem epi_supportedCoherentIdealSmul_map (W : Closeds Y)
    {M N : (coherentSupportedIn (W : Set Y)).FullSubcategory} (f : M ⟶ N) (hf : Epi f) :
    Epi ((supportedCoherentIdealSmul I (W : Set Y)).map f) := by
  let G := (coherentSupportedIn (W : Set Y)).ι ⋙
    (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf).ι
  have : PreservesFiniteColimits (coherentSupportedIn (W : Set Y)).ι :=
    (coherentSupportedIn (W : Set Y)).preservesFiniteColimits_ι_of_isWeakSerreClass
  have : PreservesFiniteColimits G := inferInstance
  have : (G.obj M).IsQuasicoherent := isQuasicoherent_supportedCoherentModule _ M
  have : (G.obj N).IsQuasicoherent := isQuasicoherent_supportedCoherentModule _ N
  have := hf
  have : Epi (G.map f) := G.map_epi f
  have : Epi (G.map ((supportedCoherentIdealSmul I W).map f)) :=
    epi_idealPowSmulMap I 1 (G.map f) this
  exact G.epi_of_epi_map this

/-- **`I ^ n` kills `M` on affine opens only if the `n`-th iterate of `M ↦ I • M` vanishes.** The
sections of `I • M` over an affine open `U` are `I(U) • Γ(M, U)`, so `I(U) ^ n` killing
`Γ(M, U)` makes `I(U) ^ (n - 1)` kill the sections of `I • M`. -/
theorem isZero_iterate_supportedCoherentIdealSmul (n : ℕ) :
    ∀ (M : (coherentSupportedIn W).FullSubcategory),
      (∀ (U : Y.affineOpens) (a : Γ(Y, U)), a ∈ I.ideal U ^ n →
        ∀ m : Γ(supportedCoherentModule M, U), a • m = 0) →
      IsZero ((supportedCoherentIdealSmul I W).obj^[n] M) := by
  induction n with
  | zero =>
    intro M h
    rw [Function.iterate_zero_apply]
    refine IsZero.of_full_of_faithful_of_isZero ((coherentSupportedIn W).ι ⋙
      (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf).ι) M ?_
    refine Stacks.Coherent.isZero_of_affine_sections _ fun U => ?_
    refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
    have hx := h U 1 (by simp) x
    have hy := h U 1 (by simp) y
    rw [one_smul] at hx hy
    rw [hx, hy]
  | succ n ih =>
    intro M h
    rw [Function.iterate_succ_apply]
    refine ih _ fun U a ha x => Subtype.ext ?_
    have hx := (mem_idealPowSmul_iff I 1 _ U _).mp x.property
    have key : ∀ y ∈
        I.ideal U ^ 1 • (⊤ : Submodule Γ(Y, U.1) Γ(supportedCoherentModule M, U.1)),
        a • y = 0 := fun y hy => by
      refine Submodule.smul_induction_on hy (fun b hb m _ => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
      · rw [smul_smul]
        exact h U _ (by rw [pow_succ]; exact Ideal.mul_mem_mul ha (by simpa using hb)) m
      · rw [smul_add, h₁, h₂, add_zero]
    exact key x.val hx

end IdealSmul

/-! ### Direct image on coherent modules with supports -/

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]

section Functor

variable [IsLocallyNoetherian Y] (Z : Closeds X)

/-- **Direct image `Coh_Z(X) ⥤ Coh_{i(Z)}(Y)`.** The direct image of a coherent `𝒪_X`-module is
coherent by [Stacks, Tag 087T], and its support is the image of the support. -/
def supportedCoherentPushforward :
    (coherentSupportedIn (Z : Set X)).FullSubcategory ⥤
      (coherentSupportedIn (i.closedImage Z : Set Y)).FullSubcategory :=
  ObjectProperty.lift _ ((coherentSupportedIn (Z : Set X)).ι ⋙ pushforwardCoherentModules i)
    fun F => (supp_pushforward_of_isClosedImmersion i F.obj.obj).trans_subset
      (Set.image_mono F.property)

/-- Composed with the inclusion of `Coh_{i(Z)}(Y)`, direct image is direct image of coherent
modules. -/
theorem supportedCoherentPushforward_comp_ι :
    supportedCoherentPushforward i Z ⋙ (coherentSupportedIn (i.closedImage Z : Set Y)).ι =
      (coherentSupportedIn (Z : Set X)).ι ⋙ pushforwardCoherentModules i :=
  rfl

/-- The underlying module of the direct image of `ℱ` is `i_*ℱ`. -/
@[simp]
theorem supportedCoherentModule_supportedCoherentPushforward_obj
    (F : (coherentSupportedIn (Z : Set X)).FullSubcategory) :
    supportedCoherentModule ((supportedCoherentPushforward i Z).obj F) =
      (Scheme.Modules.pushforward i).obj (supportedCoherentModule F) :=
  rfl

/-- Direct image `Coh_Z(X) ⥤ Coh_{i(Z)}(Y)` is fully faithful, by [Stacks, Tag 08KS]. -/
def fullyFaithfulSupportedCoherentPushforward :
    (supportedCoherentPushforward i Z).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := (coherentSupportedIn (i.closedImage Z : Set Y)).ι)
    (show ((coherentSupportedIn (Z : Set X)).ι ⋙ pushforwardCoherentModules i).FullyFaithful from
      (ObjectProperty.fullyFaithfulι _).comp (fullyFaithfulPushforwardCoherentModules i))

/-- Direct image `Coh_Z(X) ⥤ Coh_{i(Z)}(Y)` is full. -/
instance : (supportedCoherentPushforward i Z).Full :=
  (fullyFaithfulSupportedCoherentPushforward i Z).full

/-- Direct image `Coh_Z(X) ⥤ Coh_{i(Z)}(Y)` is faithful. -/
instance : (supportedCoherentPushforward i Z).Faithful :=
  (fullyFaithfulSupportedCoherentPushforward i Z).faithful

/-- **Direct image `Coh_Z(X) ⥤ Coh_{i(Z)}(Y)` is exact**: it is exact on coherent modules, and the
inclusion of `Coh_{i(Z)}(Y)` reflects short exactness. -/
theorem shortExact_map_supportedCoherentPushforward [IsLocallyNoetherian X]
    {S : ShortComplex (coherentSupportedIn (Z : Set X)).FullSubcategory} (hS : S.ShortExact) :
    (S.map (supportedCoherentPushforward i Z)).ShortExact :=
  ShortExact.reflects_shortExact_of_faithful (coherentSupportedIn (i.closedImage Z : Set Y)).ι
    (shortExact_map_pushforwardCoherentModules i _
      ((coherentSupportedIn (Z : Set X)).shortExact_map_ι hS))

/-- **The homomorphism `K₀(Coh_Z(X)) ⟶ K₀(Coh_{i(Z)}(Y))` of [Stacks, Tag 0FDT]**, induced by the
exact functor `ℱ ↦ i_*ℱ`. -/
def supportedCoherentKZeroPushforward [IsLocallyNoetherian X] :
    supportedCoherentKZero Z →+ supportedCoherentKZero (i.closedImage Z) :=
  KZero.lift (fun F => KZero.mk _ ((supportedCoherentPushforward i Z).obj F)) fun _ hS =>
    KZero.mk_of_shortExact _ (shortExact_map_supportedCoherentPushforward i Z hS)

/-- The homomorphism `K₀(Coh_Z(X)) ⟶ K₀(Coh_{i(Z)}(Y))` sends `[ℱ]` to `[i_*ℱ]`. -/
@[simp]
theorem supportedCoherentKZeroPushforward_mk [IsLocallyNoetherian X]
    (F : (coherentSupportedIn (Z : Set X)).FullSubcategory) :
    supportedCoherentKZeroPushforward i Z (KZero.mk _ F) =
      KZero.mk _ ((supportedCoherentPushforward i Z).obj F) :=
  KZero.lift_mk _ _ _

/-- **Direct image commutes with enlarging the support**: for `Z' ⊆ Z` the square formed by the
maps `K₀(Coh_{Z'}(X)) ⟶ K₀(Coh_Z(X))` and `K₀(Coh_{i(Z')}(Y)) ⟶ K₀(Coh_{i(Z)}(Y))` commutes. -/
theorem supportedCoherentKZeroPushforward_comp_map [IsLocallyNoetherian X] {Z' : Closeds X}
    (h : Z' ≤ Z) :
    (supportedCoherentKZeroPushforward i Z).comp (supportedCoherentKZeroMap h) =
      (supportedCoherentKZeroMap (Scheme.Hom.closedImage_mono i h)).comp
        (supportedCoherentKZeroPushforward i Z') :=
  KZero.hom_ext fun F => by
    simp only [AddMonoidHom.comp_apply, supportedCoherentKZeroMap_mk,
      supportedCoherentKZeroPushforward_mk]
    rfl

end Functor

/-! ### Dévissage along the closed immersion -/

section Devissage

variable [IsLocallyNoetherian Y] (Z : Closeds X)

/-- **`M / ℐM` is a direct image.** For `M` in `Coh_{i(Z)}(Y)` and `ℐ = ker i`, the quotient of
`M` by `ℐM` is killed by `ℐ`, hence is the direct image of a coherent `𝒪_X`-module by
[Stacks, Tag 087T], which is supported in `Z` because its direct image is supported in `i(Z)`. -/
theorem essImage_cokernel_supportedCoherentIdealSmulι [CompactSpace Y]
    (M : (coherentSupportedIn (i.closedImage Z : Set Y)).FullSubcategory) :
    (supportedCoherentPushforward i Z).essImage
      (cokernel ((supportedCoherentIdealSmulι i.ker (i.closedImage Z : Set Y)).app M)) := by
  have : IsNoetherian Y := {}
  let W : Set Y := (i.closedImage Z : Set Y)
  let f := (supportedCoherentIdealSmulι i.ker W).app M
  let G := (coherentSupportedIn W).ι ⋙ (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf).ι
  have : PreservesFiniteColimits (coherentSupportedIn W).ι :=
    (coherentSupportedIn W).preservesFiniteColimits_ι_of_isWeakSerreClass
  have : PreservesFiniteColimits G := inferInstance
  let e₁ : G.obj (cokernel f) ≅ cokernel (G.map f) := PreservesCokernel.iso G f
  let Q : Y.Modules := supportedCoherentModule (cokernel f)
  have hann : ∀ (U : Y.affineOpens) (a : Γ(Y, U)), a ∈ i.ker.ideal U → ∀ m : Γ(Q, U),
      a • m = 0 := fun U a ha m =>
    smul_eq_zero_of_iso_cokernel_idealPowSmul i.ker (supportedCoherentModule M) e₁ U a ha m
  obtain ⟨G', hG', ⟨e⟩⟩ := exists_isCoherent_pushforward_iso_of_smul_eq_zero i Q
    ((Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal i Q).mpr hann)
  have hsupp : SheafOfModules.supp G' ⊆ (Z : Set X) := by
    intro x hx
    have h1 : i.base x ∈ SheafOfModules.supp Q := by
      rw [← SheafOfModules.supp_eq_of_iso e]
      exact (mem_supp_pushforward_iff i G' x).mpr hx
    obtain ⟨z, hz, hzx⟩ := (cokernel f).property h1
    rwa [← i.isClosedEmbedding.injective hzx]
  exact ⟨⟨⟨G', CoherentAbelian.stacksIsCoherent_of_isCoherent hG'⟩, hsupp⟩,
    ⟨ObjectProperty.isoMk _ (ObjectProperty.isoMk _ e)⟩⟩

/-- **`ℐ` kills direct images**: `ℐ · i_*ℱ = 0`. -/
theorem isZero_supportedCoherentIdealSmul_obj_obj
    (F : (coherentSupportedIn (Z : Set X)).FullSubcategory) :
    IsZero ((supportedCoherentIdealSmul i.ker (i.closedImage Z : Set Y)).obj
      ((supportedCoherentPushforward i Z).obj F)) := by
  let G := (coherentSupportedIn (i.closedImage Z : Set Y)).ι ⋙
    (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf).ι
  let M : Y.Modules := supportedCoherentModule ((supportedCoherentPushforward i Z).obj F)
  have h := (Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal i M).mp
    ((Stacks.ClosedImmersion.pushforward_essImage_iff i M).mp ⟨F.obj.obj, ⟨Iso.refl _⟩⟩)
  exact IsZero.of_full_of_faithful_of_isZero G _
    (isZero_idealPowSmul_of_smul_eq_zero i.ker 1 M fun U b hb m => h U b (by simpa using hb) m)

/-- **[Stacks, Tag 01Y9]: `ℐ` is nilpotent on `Coh_{i(Z)}(Y)`.** A coherent module supported in
`i(Z)` is killed by a power of the vanishing ideal of `i(Z)`, which contains `ℐ = ker i`. -/
theorem exists_isZero_iterate_supportedCoherentIdealSmul [CompactSpace Y]
    (M : (coherentSupportedIn (i.closedImage Z : Set Y)).FullSubcategory) :
    ∃ n : ℕ,
      IsZero ((supportedCoherentIdealSmul i.ker (i.closedImage Z : Set Y)).obj^[n] M) := by
  have : IsNoetherian Y := {}
  obtain ⟨n, hn⟩ := Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_isZero_idealPowSmul
    (supportedCoherentModule M) (i.closedImage Z) M.property
  refine ⟨n, isZero_iterate_supportedCoherentIdealSmul i.ker _ n M fun U a ha m => ?_⟩
  have hle : i.ker ≤ closedIdeal (i.closedImage Z) :=
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp fun x hx =>
      i.range_subset_ker_support (Set.image_subset_range _ _ hx)
  exact smul_eq_zero_of_isZero_idealPowSmul _ n _ hn U a
    (Ideal.pow_right_mono (Scheme.IdealSheafData.le_def.mp hle U) n ha) m

/-- Multiplication by `ℐ = ker i` is a nilpotent radical for direct image
`Coh_Z(X) ⥤ Coh_{i(Z)}(Y)`. -/
def supportedCoherentKZeroDevissage [CompactSpace Y] :
    KZero.Devissage (supportedCoherentPushforward i Z) where
  rad := supportedCoherentIdealSmul i.ker (i.closedImage Z : Set Y)
  ι := supportedCoherentIdealSmulι i.ker (i.closedImage Z : Set Y)
  mono_ι _ := inferInstance
  epi_rad_map f hf := epi_supportedCoherentIdealSmul_map i.ker _ f hf
  essImage_cokernel_ι M := essImage_cokernel_supportedCoherentIdealSmulι i Z M
  isZero_rad_obj_obj F := isZero_supportedCoherentIdealSmul_obj_obj i Z F
  exists_isZero_rad_iterate M := exists_isZero_iterate_supportedCoherentIdealSmul i Z M

/-- **[Stacks, Tag 0FDT] with supports.** For a closed immersion `i : X ⟶ Y` into a Noetherian
scheme and a closed subset `Z ⊆ X`, direct image induces a bijection
`K₀(Coh_Z(X)) ⟶ K₀(Coh_{i(Z)}(Y))`. -/
theorem bijective_supportedCoherentKZeroPushforward [IsLocallyNoetherian X] [CompactSpace Y] :
    Function.Bijective (supportedCoherentKZeroPushforward i Z) :=
  (supportedCoherentKZeroDevissage i Z).bijective _ (supportedCoherentKZeroPushforward_mk i Z)

/-- **[Stacks, Tag 0FDT] with supports**, as an isomorphism
`K₀(Coh_Z(X)) ≃ K₀(Coh_{i(Z)}(Y))`. -/
def supportedCoherentKZeroPushforwardEquiv [IsLocallyNoetherian X] [CompactSpace Y] :
    supportedCoherentKZero Z ≃+ supportedCoherentKZero (i.closedImage Z) :=
  AddEquiv.ofBijective _ (bijective_supportedCoherentKZeroPushforward i Z)

/-- The isomorphism of K-groups is the homomorphism induced by direct image. -/
@[simp]
theorem supportedCoherentKZeroPushforwardEquiv_apply [IsLocallyNoetherian X] [CompactSpace Y]
    (a : supportedCoherentKZero Z) :
    supportedCoherentKZeroPushforwardEquiv i Z a = supportedCoherentKZeroPushforward i Z a :=
  rfl

/-- The inverse of `K₀(Coh_Z(X)) ≃ K₀(Coh_{i(Z)}(Y))` sends `[i_*ℱ]` to `[ℱ]`. -/
@[simp]
theorem supportedCoherentKZeroPushforwardEquiv_symm_mk [IsLocallyNoetherian X] [CompactSpace Y]
    (F : (coherentSupportedIn (Z : Set X)).FullSubcategory) :
    (supportedCoherentKZeroPushforwardEquiv i Z).symm
        (KZero.mk _ ((supportedCoherentPushforward i Z).obj F)) = KZero.mk _ F :=
  (AddEquiv.symm_apply_eq _).mpr (supportedCoherentKZeroPushforward_mk i Z F).symm

end Devissage

/-! ### The rational form -/

/-- **[Stacks, Tag 0FDT] with supports, rationally and naturally in `Z`.** Direct image induces a
natural isomorphism `𝐐 ⊗ K₀(Coh_Z(X)) ≅ 𝐐 ⊗ K₀(Coh_{i(Z)}(Y))` of functors on the closed subsets
of `X`. -/
def supportedCoherentKZeroRatPushforwardIso [IsLocallyNoetherian Y] [IsLocallyNoetherian X]
    [CompactSpace Y] :
    supportedCoherentKZeroRat X ≅ i.closedImageFunctor ⋙ supportedCoherentKZeroRat Y :=
  NatIso.ofComponents (fun Z => (LinearEquiv.baseChange ℤ ℚ _ _
      (supportedCoherentKZeroPushforwardEquiv i Z).toIntLinearEquiv).toModuleIso)
    fun {Z' Z} f => by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      induction x using TensorProduct.inductionOn with
      | tmul q a =>
        change q ⊗ₜ[ℤ] supportedCoherentKZeroPushforward i Z
            (supportedCoherentKZeroMap (leOfHom f) a) =
          q ⊗ₜ[ℤ] supportedCoherentKZeroMap
            (Scheme.Hom.closedImage_mono i (leOfHom f))
            (supportedCoherentKZeroPushforward i Z' a)
        rw [← AddMonoidHom.comp_apply, supportedCoherentKZeroPushforward_comp_map,
          AddMonoidHom.comp_apply]
      | add x y hx hy =>
        exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- The natural isomorphism `𝐐 ⊗ K₀(Coh_Z(X)) ≅ 𝐐 ⊗ K₀(Coh_{i(Z)}(Y))` on a pure tensor. -/
@[simp]
theorem supportedCoherentKZeroRatPushforwardIso_hom_app_tmul [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X] [CompactSpace Y] (Z : Closeds X) (q : ℚ)
    (a : supportedCoherentKZero Z) :
    ((supportedCoherentKZeroRatPushforwardIso i).hom.app Z).hom (q ⊗ₜ[ℤ] a) =
      q ⊗ₜ[ℤ] supportedCoherentKZeroPushforward i Z a :=
  rfl

/-! ### Multiplicities -/

/-- **Direct image along a closed immersion preserves multiplicities.** The stalk of `i_*ℱ` at
`i(ξ)` is the stalk `ℱ_ξ` with scalars restricted along the surjection `𝒪_{Y,i(ξ)} ⟶ 𝒪_{X,ξ}`,
which does not change its length ([Stacks, Tag 0EE3]). -/
theorem sheafMultiplicity_pushforward_of_isClosedImmersion (F : X.Modules) (ξ : X) :
    sheafMultiplicity ((Scheme.Modules.pushforward i).obj F) (i.base ξ) =
      sheafMultiplicity F ξ := by
  unfold sheafMultiplicity
  congr 2
  exact length_stalk_pushforward_of_isClosedImmersion i F ξ

end Stacks.Chow

end
