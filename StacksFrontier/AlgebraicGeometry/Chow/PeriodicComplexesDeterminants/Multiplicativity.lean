module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.GammaNatural
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.GammaThreeByThree
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Functor
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Basic

/-!
# Multiplicativity of the periodic determinant

Let three endomorphisms of a finite-length module over a local ring have complementary images
and kernels for every ordering. They give exact two-periodic complexes on the module, on the
image of the third endomorphism, and on the quotient by the kernel of the second. The
determinant of the first complex is the product of the other two.

## Main definitions

* `AlgebraicGeometry.ComplementaryImagesKernels` packages the image and kernel equalities for
  all permutations of three endomorphisms.
* `AlgebraicGeometry.alphaOnGammaRange` and `AlgebraicGeometry.betaOnGammaRange` are the
  restricted endomorphisms.
* `AlgebraicGeometry.alphaOnKerBetaQuotient` and
  `AlgebraicGeometry.gammaOnKerBetaQuotient` are the induced endomorphisms.

## Main results

* `AlgebraicGeometry.exact_alpha_betaGamma` and
  `AlgebraicGeometry.exact_betaGamma_alpha` give the exactness on the module.
* `AlgebraicGeometry.exact_alpha_beta_onGammaRange` and
  `AlgebraicGeometry.exact_beta_alpha_onGammaRange` give the exactness on the image of the
  third endomorphism.
* `AlgebraicGeometry.exact_alpha_gamma_onKerBetaQuotient` and
  `AlgebraicGeometry.exact_gamma_alpha_onKerBetaQuotient` give the exactness on the quotient by
  the kernel of the second endomorphism.
* `AlgebraicGeometry.periodicDeterminant_mul` is the multiplicativity formula.

## Implementation notes

The two-periodic complexes in parts (1), (2) and (3) are represented by their two
`Function.Exact` assertions. The image, quotient and induced endomorphisms are the literal
submodule and quotient constructions; the equalities in the hypothesis ensure that these maps
are well defined.

## References

* [Stacks Project, Tag 02PU](https://stacks.math.columbia.edu/tag/02PU)
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

section Generic

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The image of each endomorphism is the kernel of either composite of the other two, and its
kernel is either composite image. -/
structure ComplementaryImagesKernels (α β γ : M →ₗ[R] M) : Prop where
  range_alpha_eq_ker_beta_gamma : LinearMap.range α = LinearMap.ker (β ∘ₗ γ)
  range_alpha_eq_ker_gamma_beta : LinearMap.range α = LinearMap.ker (γ ∘ₗ β)
  range_beta_eq_ker_alpha_gamma : LinearMap.range β = LinearMap.ker (α ∘ₗ γ)
  range_beta_eq_ker_gamma_alpha : LinearMap.range β = LinearMap.ker (γ ∘ₗ α)
  range_gamma_eq_ker_alpha_beta : LinearMap.range γ = LinearMap.ker (α ∘ₗ β)
  range_gamma_eq_ker_beta_alpha : LinearMap.range γ = LinearMap.ker (β ∘ₗ α)
  ker_alpha_eq_range_beta_gamma : LinearMap.ker α = LinearMap.range (β ∘ₗ γ)
  ker_alpha_eq_range_gamma_beta : LinearMap.ker α = LinearMap.range (γ ∘ₗ β)
  ker_beta_eq_range_alpha_gamma : LinearMap.ker β = LinearMap.range (α ∘ₗ γ)
  ker_beta_eq_range_gamma_alpha : LinearMap.ker β = LinearMap.range (γ ∘ₗ α)
  ker_gamma_eq_range_alpha_beta : LinearMap.ker γ = LinearMap.range (α ∘ₗ β)
  ker_gamma_eq_range_beta_alpha : LinearMap.ker γ = LinearMap.range (β ∘ₗ α)

/-- Restriction of `f` to the image of `g`, when their composite images agree. -/
def restrictToRange (f g : M →ₗ[R] M)
    (h : LinearMap.range (f ∘ₗ g) = LinearMap.range (g ∘ₗ f)) :
    LinearMap.range g →ₗ[R] LinearMap.range g :=
  (f.comp g.range.subtype).codRestrict (LinearMap.range g) (by
    intro x
    obtain ⟨y, hy⟩ := x.2
    change f x.1 ∈ LinearMap.range g
    rw [← hy]
    have hfg : f (g y) ∈ LinearMap.range (g ∘ₗ f) := by
      rw [← h]
      exact LinearMap.mem_range_self _ _
    obtain ⟨z, hz⟩ := hfg
    exact ⟨f z, hz⟩)

/-- The restriction of `α` to the image of `γ`. -/
def alphaOnGammaRange (α β γ : M →ₗ[R] M)
    (h : ComplementaryImagesKernels α β γ) :
    LinearMap.range γ →ₗ[R] LinearMap.range γ :=
  restrictToRange α γ (h.ker_beta_eq_range_alpha_gamma.symm.trans
    h.ker_beta_eq_range_gamma_alpha)

/-- The restriction of `β` to the image of `γ`. -/
def betaOnGammaRange (α β γ : M →ₗ[R] M)
    (h : ComplementaryImagesKernels α β γ) :
    LinearMap.range γ →ₗ[R] LinearMap.range γ :=
  restrictToRange β γ (h.ker_alpha_eq_range_beta_gamma.symm.trans
    h.ker_alpha_eq_range_gamma_beta)

/-- The endomorphism induced by `α` on the quotient by the kernel of `β`. -/
def alphaOnKerBetaQuotient (α β γ : M →ₗ[R] M)
    (h : ComplementaryImagesKernels α β γ) :
    (M ⧸ LinearMap.ker β) →ₗ[R] (M ⧸ LinearMap.ker β) :=
  Submodule.mapQ _ _ α (by
    intro x hx
    rw [h.ker_beta_eq_range_gamma_alpha] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [h.ker_beta_eq_range_alpha_gamma]
    exact ⟨α y, rfl⟩)

/-- The endomorphism induced by `γ` on the quotient by the kernel of `β`. -/
def gammaOnKerBetaQuotient (α β γ : M →ₗ[R] M)
    (h : ComplementaryImagesKernels α β γ) :
    (M ⧸ LinearMap.ker β) →ₗ[R] (M ⧸ LinearMap.ker β) :=
  Submodule.mapQ _ _ γ (by
    intro x hx
    rw [h.ker_beta_eq_range_alpha_gamma] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [h.ker_beta_eq_range_gamma_alpha]
    exact ⟨γ y, rfl⟩)

/-- **Stacks Project, Tag 02PU.** Exactness of `α` followed by `βγ` on the original
module. -/
@[stacks 02PU "part (1)"]
theorem exact_alpha_betaGamma (α β γ : M →ₗ[R] M)
    (h : ComplementaryImagesKernels α β γ) :
    Function.Exact α (β ∘ₗ γ) :=
  LinearMap.exact_iff.mpr h.range_alpha_eq_ker_beta_gamma.symm

/-- **Stacks Project, Tag 02PU.** Exactness of `βγ` followed by `α` on the original
module. -/
@[stacks 02PU "part (1)"]
theorem exact_betaGamma_alpha (α β γ : M →ₗ[R] M)
    (h : ComplementaryImagesKernels α β γ) :
    Function.Exact (β ∘ₗ γ) α :=
  LinearMap.exact_iff.mpr h.ker_alpha_eq_range_beta_gamma

/-- Exactness of the restrictions of two endomorphisms to the image of `γ`. -/
private lemma exact_restrictToRange (f g γ : M →ₗ[R] M)
    (hg : LinearMap.ker g = LinearMap.range (f ∘ₗ γ))
    (hγ : LinearMap.range γ = LinearMap.ker (g ∘ₗ f))
    (hfg : LinearMap.range (f ∘ₗ γ) = LinearMap.range (γ ∘ₗ f))
    (hgf : LinearMap.range (g ∘ₗ γ) = LinearMap.range (γ ∘ₗ g)) :
    Function.Exact (restrictToRange f γ hfg) (restrictToRange g γ hgf) := by
  apply LinearMap.exact_iff.mpr
  ext x
  constructor
  · intro hx
    have hxg : x.1 ∈ LinearMap.ker g := by
      change restrictToRange g γ hgf x = 0 at hx
      exact congrArg Subtype.val hx
    rw [hg] at hxg
    rcases hxg with ⟨y, hy⟩
    refine ⟨⟨γ y, ⟨y, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show f (γ y) = x.1
    simpa [LinearMap.comp_apply] using hy
  · rintro ⟨y, rfl⟩
    have hy : y.1 ∈ LinearMap.ker (g ∘ₗ f) := hγ ▸ y.2
    exact Subtype.ext hy

/-- **Stacks Project, Tag 02PU.** Exactness of `α` followed by `β` on the image of `γ`. -/
@[stacks 02PU "part (2)"]
theorem exact_alpha_beta_onGammaRange (α β γ : M →ₗ[R] M)
    (h : ComplementaryImagesKernels α β γ) :
    Function.Exact (alphaOnGammaRange α β γ h) (betaOnGammaRange α β γ h) :=
  exact_restrictToRange α β γ h.ker_beta_eq_range_alpha_gamma
    h.range_gamma_eq_ker_beta_alpha _ _

/-- **Stacks Project, Tag 02PU.** Exactness of `β` followed by `α` on the image of `γ`. -/
@[stacks 02PU "part (2)"]
theorem exact_beta_alpha_onGammaRange (α β γ : M →ₗ[R] M)
    (h : ComplementaryImagesKernels α β γ) :
    Function.Exact (betaOnGammaRange α β γ h) (alphaOnGammaRange α β γ h) :=
  exact_restrictToRange β α γ h.ker_alpha_eq_range_beta_gamma
    h.range_gamma_eq_ker_alpha_beta _ _

/-- The preimage under `f` of the kernel of `β` is the image of `g`. -/
private lemma comap_ker_eq_range (β f g : M →ₗ[R] M)
    (hβ : LinearMap.ker β = LinearMap.range (f ∘ₗ g))
    (hf : LinearMap.ker f = LinearMap.range (g ∘ₗ β)) :
    (LinearMap.ker β).comap f = LinearMap.range g := by
  ext x
  constructor
  · intro hx
    change f x ∈ LinearMap.ker β at hx
    rw [hβ] at hx
    rcases hx with ⟨y, hy⟩
    have hxker : x - g y ∈ LinearMap.ker f := by
      apply LinearMap.mem_ker.mpr
      rw [map_sub, ← (show f (g y) = f x by simpa [LinearMap.comp_apply] using hy)]
      simp
    rw [hf] at hxker
    rcases hxker with ⟨z, hz⟩
    refine ⟨y + β z, ?_⟩
    rw [map_add, (show g (β z) = x - g y by simpa [LinearMap.comp_apply] using hz)]
    simp
  · rintro ⟨y, rfl⟩
    show f (g y) ∈ LinearMap.ker β
    rw [hβ]
    exact ⟨y, rfl⟩

/-- **Stacks Project, Tag 02PU.** Exactness of `α` followed by `γ` on the quotient by the
kernel of `β`. -/
@[stacks 02PU "part (3)"]
theorem exact_alpha_gamma_onKerBetaQuotient (α β γ : M →ₗ[R] M)
    (h : ComplementaryImagesKernels α β γ) :
    Function.Exact (alphaOnKerBetaQuotient α β γ h)
      (gammaOnKerBetaQuotient α β γ h) := by
  apply LinearMap.exact_iff.mpr
  show LinearMap.ker (Submodule.mapQ (LinearMap.ker β) (LinearMap.ker β) γ _) =
    LinearMap.range (Submodule.mapQ (LinearMap.ker β) (LinearMap.ker β) α _)
  rw [Submodule.ker_mapQ, Submodule.range_mapQ,
    comap_ker_eq_range β γ α h.ker_beta_eq_range_gamma_alpha
      h.ker_gamma_eq_range_alpha_beta]

/-- **Stacks Project, Tag 02PU.** Exactness of `γ` followed by `α` on the quotient by the
kernel of `β`. -/
@[stacks 02PU "part (3)"]
theorem exact_gamma_alpha_onKerBetaQuotient (α β γ : M →ₗ[R] M)
    (h : ComplementaryImagesKernels α β γ) :
    Function.Exact (gammaOnKerBetaQuotient α β γ h)
      (alphaOnKerBetaQuotient α β γ h) := by
  apply LinearMap.exact_iff.mpr
  show LinearMap.ker (Submodule.mapQ (LinearMap.ker β) (LinearMap.ker β) α _) =
    LinearMap.range (Submodule.mapQ (LinearMap.ker β) (LinearMap.ker β) γ _)
  rw [Submodule.ker_mapQ, Submodule.range_mapQ,
    comap_ker_eq_range β α γ h.ker_beta_eq_range_alpha_gamma
      h.ker_alpha_eq_range_gamma_beta]

/-- A map killing the kernel of a surjection descends along it. -/
private def descendSurjective
    {X Y Z : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (p : X →ₗ[R] Y) (hp : Function.Surjective p) (f : X →ₗ[R] Z)
    (h : LinearMap.ker p ≤ LinearMap.ker f) : Y →ₗ[R] Z :=
  (p.ker.liftQ f h).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap

/-- The descended map recovers the original one. -/
private lemma descendSurjective_apply
    {X Y Z : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (p : X →ₗ[R] Y) (hp : Function.Surjective p) (f : X →ₗ[R] Z)
    (h : LinearMap.ker p ≤ LinearMap.ker f) (x : X) :
    descendSurjective p hp f h (p x) = f x := by
  simp [descendSurjective, LinearMap.quotKerEquivOfSurjective_symm_apply]

/-- Exactness of the inclusion and projection extracted from two factorised exact composites. -/
private lemma exact_of_factorizations
    {X A C : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]
    (f g : X →ₗ[R] X) (hfg : Function.Exact f g)
    (i : A →ₗ[R] X) (p : X →ₗ[R] A)
    (j : C →ₗ[R] X) (q : X →ₗ[R] C)
    (hp : Function.Surjective p) (hj : Function.Injective j)
    (hf : f = i.comp p) (hg : g = j.comp q) : Function.Exact i q := by
  intro x
  show q x = 0 ↔ ∃ a, i a = x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hfg x).mp (by rw [hg]; simp [hx])
    exact ⟨p y, by simpa [hf] using hy⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨y, rfl⟩ := hp a
    apply hj
    simpa [hg] using (hfg (i (p y))).mpr ⟨y, by rw [hf]; rfl⟩

/-- A factorisation `f = i ∘ p` with `i` injective and `p` surjective identifies the source of
`i` with the image of `f`. -/
private abbrev rangePresentation
    {A : Type*} [AddCommGroup A] [Module R A]
    (f : M →ₗ[R] M) (i : A →ₗ[R] M) (p : M →ₗ[R] A)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hf : f = i.comp p) :
    A ≃ₗ[R] LinearMap.range f :=
  LinearEquiv.ofBijective (i.codRestrict _ (fun a => by
    obtain ⟨x, rfl⟩ := hp a
    exact ⟨x, by rw [hf]; rfl⟩))
    ⟨fun _ _ h => hi (congrArg Subtype.val h), by
      rintro ⟨_, x, rfl⟩
      exact ⟨p x, Subtype.ext (by change i (p x) = f x; exact (LinearMap.congr_fun hf x).symm)⟩⟩

end Generic

section Local

universe u v

open CategoryTheory

open scoped TensorProduct

open Module.FiniteLength

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]

/-- A finite-length module as an object of the source category of the determinant functor. -/
private abbrev finiteLengthIsoObject (R : Type u) [CommRing R] [IsLocalRing R]
    (N : Type v) [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) :
    FiniteLengthModuleIso R :=
  ⟨⟨ModuleCat.of R N, hN⟩⟩

/-- A linear isomorphism as a morphism of that category. -/
private abbrev finiteLengthIsoHom {R : Type u} [CommRing R] [IsLocalRing R]
    {N N' : Type v} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (hN : IsFiniteLength R N) (hN' : IsFiniteLength R N')
    (e : N ≃ₗ[R] N') :
    finiteLengthIsoObject R N hN ⟶ finiteLengthIsoObject R N' hN' :=
  (CategoryTheory.Core.isoMk (CategoryTheory.ObjectProperty.isoMk
    (fun X : ModuleCat R => IsFiniteLength R X) e.toModuleIso)).hom

/-- The identity isomorphism gives the identity morphism. -/
private lemma finiteLengthIsoHom_refl {R : Type u} [CommRing R] [IsLocalRing R]
    {N : Type v} [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) :
    finiteLengthIsoHom hN hN (LinearEquiv.refl R N) =
      𝟙 (finiteLengthIsoObject R N hN) := by
  apply CategoryTheory.Core.hom_ext
  apply CategoryTheory.ObjectProperty.hom_ext
  ext x
  rfl

/-- The determinant functor sends the identity morphism to the identity. -/
private lemma determinantMapLinearEquiv_refl {R : Type u} [CommRing R] [IsLocalRing R]
    {N : Type v} [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) :
    ((determinantFunctor R).mapLinearEquiv
      (finiteLengthIsoHom hN hN (LinearEquiv.refl R N))).toLinearMap = LinearMap.id := by
  rw [finiteLengthIsoHom_refl]
  let O := finiteLengthIsoObject R N hN
  show ((determinantFunctor R).mapLinearEquiv (𝟙 O)).toLinearMap = LinearMap.id
  simpa using congrArg ModuleCat.Hom.hom (show ModuleCat.ofHom
    ((determinantFunctor R).mapLinearEquiv (𝟙 O)).toLinearMap =
    𝟙 (ModuleCat.of (IsLocalRing.ResidueField R) (determinant R O.of.obj)) from by
      simpa using ((determinantFunctor R).map_iso (𝟙 O)).symm)

/-- Naturality of the determinant map of a short exact sequence along isomorphisms of its three
terms. -/
private lemma determinantExactSequenceMap_natural_of_linearEquiv
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K L Q K' L' Q' : Type v}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup K'] [Module R K'] [AddCommGroup L'] [Module R L']
    [AddCommGroup Q'] [Module R Q']
    (i : K →ₗ[R] L) (p : L →ₗ[R] Q)
    (i' : K' →ₗ[R] L') (p' : L' →ₗ[R] Q')
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (hi' : Function.Injective i') (hp' : Function.Surjective p')
    (hip' : Function.Exact i' p')
    (hK : IsFiniteLength R K) (hL : IsFiniteLength R L) (hQ : IsFiniteLength R Q)
    (hK' : IsFiniteLength R K') (hL' : IsFiniteLength R L') (hQ' : IsFiniteLength R Q')
    (eK : K ≃ₗ[R] K') (eL : L ≃ₗ[R] L') (eQ : Q ≃ₗ[R] Q')
    (hcommI : i'.comp eK.toLinearMap = eL.toLinearMap.comp i)
    (hcommP : p'.comp eL.toLinearMap = eQ.toLinearMap.comp p) :
    (determinantExactSequenceMap i' p' hi' hp' hip' hK' hL' hQ').comp
        (TensorProduct.map
          ((determinantFunctor R).mapLinearEquiv
            (finiteLengthIsoHom hK hK' eK)).toLinearMap
          ((determinantFunctor R).mapLinearEquiv
            (finiteLengthIsoHom hQ hQ' eQ)).toLinearMap) =
      ((determinantFunctor R).mapLinearEquiv
        (finiteLengthIsoHom hL hL' eL)).toLinearMap.comp
        (determinantExactSequenceMap i p hi hp hip hK hL hQ) := by
  let u := finiteLengthIsoHom hK hK' eK
  let v := finiteLengthIsoHom hL hL' eL
  let w := finiteLengthIsoHom hQ hQ' eQ
  have hu : i'.comp u.iso.hom.hom.hom = v.iso.hom.hom.hom.comp i := by
    rw [show u.iso.hom.hom.hom = eK.toLinearMap by ext x; rfl,
      show v.iso.hom.hom.hom = eL.toLinearMap by ext x; rfl]
    exact hcommI
  have hw : p'.comp v.iso.hom.hom.hom = w.iso.hom.hom.hom.comp p := by
    rw [show v.iso.hom.hom.hom = eL.toLinearMap by ext x; rfl,
      show w.iso.hom.hom.hom = eQ.toLinearMap by ext x; rfl]
    exact hcommP
  exact determinantExactSequenceMap_natural
    i p i' p' hi hp hip hi' hp' hip' u v w hu hw

variable {N : Type v} [AddCommGroup N] [Module R N]

/-- Induction principle for the determinant: zero, sums, scalar multiples and symbols suffice. -/
private lemma determinant_induction (P : determinant R N → Prop)
    (h0 : P 0) (ha : ∀ x y, P x → P y → P (x + y))
    (hs : ∀ (c : IsLocalRing.ResidueField R) x, P x → P (c • x)) (he : ∀ e, P (symbol e))
    (x : determinant R N) : P x := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro f
  induction f using Finsupp.induction_linear with
  | zero => simpa using h0
  | add f g hf hg => simpa using ha _ _ hf hg
  | single e c =>
    simpa [symbol, ← Submodule.Quotient.mk_smul, Finsupp.smul_single] using hs c (symbol e) (he e)

omit [IsLocalRing R] in
/-- The trivial module has length zero. -/
private lemma moduleLength_punit : moduleLength R PUnit.{v + 1} = 0 := by
  simp [moduleLength, Module.length_eq_zero]

/-- The empty admissible sequence of the trivial module. -/
private def emptySequence : AdmissibleSequence R PUnit.{v + 1} :=
  ⟨fun _ => 0, by
    intro i
    have := i.isLt
    simp only [moduleLength_punit] at this
    omega⟩

/-- The symbol of the empty sequence is nonzero. -/
private lemma emptySequence_symbol_ne_zero :
    symbol (emptySequence (R := R) : AdmissibleSequence R PUnit.{v + 1}) ≠ 0 := by
  have hh := span_symbol_eq_top (R := R)
    (M := PUnit.{v + 1}) IsFiniteLength.of_subsingleton emptySequence
    (Subsingleton.elim _ _)
  have hn : Module.finrank (IsLocalRing.ResidueField R) (determinant R PUnit.{v + 1}) = 1 :=
    finrank_determinant_eq_one IsFiniteLength.of_subsingleton
  intro hz
  simp only [hz, Submodule.span_zero_singleton] at hh
  have : Subsingleton (determinant R PUnit.{v + 1}) := ⟨fun x y => by
    have hx : x = 0 := show x ∈ (⊥ : Submodule _ _) from hh ▸ Submodule.mem_top
    have hy : y = 0 := show y ∈ (⊥ : Submodule _ _) from hh ▸ Submodule.mem_top
    exact hx.trans hy.symm⟩
  have hzdim := Module.finrank_zero_of_subsingleton
    (R := IsLocalRing.ResidueField R) (M := determinant R PUnit.{v + 1})
  omega

/-- The determinant map of `0 → N → N → 0 → 0` is the right unit. -/
private lemma determinantExactSequenceMap_right_unit
    (hN : IsFiniteLength R N) (a : determinant R N) :
    determinantExactSequenceMap (LinearMap.id : N →ₗ[R] N) (0 : N →ₗ[R] PUnit.{v + 1})
      Function.injective_id (by intro x; exact ⟨0, Subsingleton.elim _ _⟩)
      (by rw [LinearMap.exact_iff]; simp) hN hN IsFiniteLength.of_subsingleton
      (a ⊗ₜ[IsLocalRing.ResidueField R] symbol (emptySequence (R := R))) = a := by
  let g := determinantExactSequenceMap (LinearMap.id : N →ₗ[R] N)
      (0 : N →ₗ[R] PUnit.{v + 1})
      Function.injective_id (by intro x; exact ⟨0, Subsingleton.elim _ _⟩)
      (by rw [LinearMap.exact_iff]; simp) hN hN IsFiniteLength.of_subsingleton
  show g _ = _
  induction a using determinant_induction with
  | h0 => simp
  | ha x y hx hy => simp [TensorProduct.add_tmul, hx, hy]
  | hs c x hx =>
      simpa only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul]
        using congrArg (c • ·) hx
  | he e =>
    by_cases he : symbol e = 0
    · simp [he]
    obtain ⟨hl, had, hv⟩ := determinantExactSequenceMap_spec
      (LinearMap.id : N →ₗ[R] N) (0 : N →ₗ[R] PUnit.{v + 1})
      Function.injective_id (by intro x; exact ⟨0, Subsingleton.elim _ _⟩)
      (by rw [LinearMap.exact_iff]; simp) hN hN IsFiniteLength.of_subsingleton e emptySequence he
      emptySequence_symbol_ne_zero (fun _ => 0) (by intro i; exact Subsingleton.elim _ _)
    change g _ = _ at hv
    rw [hv]
    congr 1
    apply Subtype.ext
    funext i
    simp [Fin.append_right_nil _ _ (moduleLength_punit (R := R))]

/-- The determinant map of `0 → 0 → N → N → 0` is the left unit. -/
private lemma determinantExactSequenceMap_left_unit
    (hN : IsFiniteLength R N) (a : determinant R N) :
    determinantExactSequenceMap (0 : PUnit.{v + 1} →ₗ[R] N) (LinearMap.id : N →ₗ[R] N)
      (by intro x y _; exact Subsingleton.elim _ _)
      Function.surjective_id
      (by rw [LinearMap.exact_iff]; simp) IsFiniteLength.of_subsingleton hN hN
      (symbol (emptySequence (R := R)) ⊗ₜ[IsLocalRing.ResidueField R] a) = a := by
  let g := determinantExactSequenceMap (0 : PUnit.{v + 1} →ₗ[R] N)
      (LinearMap.id : N →ₗ[R] N)
      (by intro x y _; exact Subsingleton.elim _ _)
      Function.surjective_id
      (by rw [LinearMap.exact_iff]; simp) IsFiniteLength.of_subsingleton hN hN
  show g _ = _
  induction a using determinant_induction with
  | h0 => simp
  | ha x y hx hy => simp [TensorProduct.tmul_add, hx, hy]
  | hs c x hx =>
      simpa only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul]
        using congrArg (c • ·) hx
  | he e =>
    by_cases he : symbol e = 0
    · simp [he]
    obtain ⟨hl, had, hv⟩ := determinantExactSequenceMap_spec
      (0 : PUnit.{v + 1} →ₗ[R] N) (LinearMap.id : N →ₗ[R] N)
      (by intro x y _; exact Subsingleton.elim _ _)
      Function.surjective_id
      (by rw [LinearMap.exact_iff]; simp) IsFiniteLength.of_subsingleton hN hN emptySequence e
      emptySequence_symbol_ne_zero he e.1 (by intro i; rfl)
    change g _ = _ at hv
    rw [hv]
    congr 1
    apply Subtype.ext
    funext i
    simp [Fin.append_left_nil _ _ (moduleLength_punit (R := R))]

/-- Associativity of the determinant maps of a compatible pair of short exact sequences. -/
private lemma determinantExactSequenceMap_assoc
    {A B C E F T : Type v}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] [AddCommGroup T] [Module R T]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (j : B →ₗ[R] E) (q : E →ₗ[R] T)
    (k : A →ₗ[R] E) (r : E →ₗ[R] F)
    (l : C →ₗ[R] F) (s : F →ₗ[R] T)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hj : Function.Injective j) (hq : Function.Surjective q) (hjq : Function.Exact j q)
    (hk : Function.Injective k) (hr : Function.Surjective r) (hkr : Function.Exact k r)
    (hl : Function.Injective l) (hs : Function.Surjective s) (hls : Function.Exact l s)
    (hki : k = j.comp i) (hrj : r.comp j = l.comp p) (hsr : q = s.comp r)
    (hA : IsFiniteLength R A) (hB : IsFiniteLength R B) (hC : IsFiniteLength R C)
    (hE : IsFiniteLength R E) (hF : IsFiniteLength R F) (hT : IsFiniteLength R T)
    (a : determinant R A) (c : determinant R C) (t : determinant R T) :
    determinantExactSequenceMap j q hj hq hjq hB hE hT
      (determinantExactSequenceMap i p hi hp hip hA hB hC
        (a ⊗ₜ[IsLocalRing.ResidueField R] c) ⊗ₜ[IsLocalRing.ResidueField R] t) =
    determinantExactSequenceMap k r hk hr hkr hA hE hF
      (a ⊗ₜ[IsLocalRing.ResidueField R]
        determinantExactSequenceMap l s hl hs hls hC hF hT
          (c ⊗ₜ[IsLocalRing.ResidueField R] t)) := by
  have hzT : Function.Injective (0 : PUnit.{v + 1} →ₗ[R] T) :=
    fun _ _ _ => Subsingleton.elim _ _
  have haz : Function.Surjective (0 : A →ₗ[R] PUnit.{v + 1}) :=
    fun _ => ⟨0, Subsingleton.elim _ _⟩
  have hezT : Function.Exact (0 : PUnit.{v + 1} →ₗ[R] T) (LinearMap.id : T →ₗ[R] T) := by
    rw [LinearMap.exact_iff]; simp
  have heaz : Function.Exact (LinearMap.id : A →ₗ[R] A) (0 : A →ₗ[R] PUnit.{v + 1}) := by
    rw [LinearMap.exact_iff]; simp
  have hqk : q.comp k = 0 := by
    rw [hki, ← LinearMap.comp_assoc]
    have hh : q.comp j = 0 := by
      apply LinearMap.range_le_ker_iff.mp
      rw [hjq.linearMap_ker_eq]
    rw [hh, LinearMap.zero_comp]
  have ht := determinantExactSequenceMap_three_by_three
    i p k r (0 : PUnit.{v + 1} →ₗ[R] T) (LinearMap.id : T →ₗ[R] T)
    LinearMap.id j l 0 q s
    hi hp hip hk hr hkr hzT Function.surjective_id hezT
    Function.injective_id haz heaz hj hq hjq hl hs hls
    (by simpa using hki) hrj (by simpa using hqk.symm) (by simpa using hsr)
    hA hB hC hA hE hF IsFiniteLength.of_subsingleton hT hT
  have hv := LinearMap.congr_fun ht
    ((a ⊗ₜ[IsLocalRing.ResidueField R] c) ⊗ₜ[IsLocalRing.ResidueField R]
      (symbol (emptySequence (R := R)) ⊗ₜ[IsLocalRing.ResidueField R] t))
  simpa [signedTensorInterchange, moduleLength_punit,
    determinantExactSequenceMap_left_unit, determinantExactSequenceMap_right_unit] using hv

/-- For a periodic complex presented by factorisations, the two determinant maps differ by the
signed periodic determinant. -/
private lemma periodicDeterminant_comparison
    {M A C : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]
    (f g : M →ₗ[R] M) (hfg : Function.Exact f g) (hgf : Function.Exact g f)
    (iA : A →ₗ[R] M) (pA : M →ₗ[R] A)
    (iC : C →ₗ[R] M) (pC : M →ₗ[R] C)
    (hiA : Function.Injective iA) (hpA : Function.Surjective pA)
    (hiC : Function.Injective iC) (hpC : Function.Surjective pC)
    (hexA : Function.Exact iA pC) (hexC : Function.Exact iC pA)
    (hf : f = iC.comp pC) (hg : g = iA.comp pA)
    (hM : IsFiniteLength R M) (hA : IsFiniteLength R A) (hC : IsFiniteLength R C)
    (a : determinant R A) (c : determinant R C) :
    determinantExactSequenceMap iC pA hiC hpA hexC hC hM hA
      (c ⊗ₜ[IsLocalRing.ResidueField R] a) =
    ((-1 : IsLocalRing.ResidueField R) ^ (moduleLength R C * moduleLength R A) *
      (periodicDeterminant f g hfg hgf hM : IsLocalRing.ResidueField R)) •
    determinantExactSequenceMap iA pC hiA hpC hexA hA hM hC
      (a ⊗ₜ[IsLocalRing.ResidueField R] c) := by
  let eA := rangePresentation g iA pA hiA hpA hg
  let eC := rangePresentation f iC pC hiC hpC hf
  have hA' : IsFiniteLength R (LinearMap.range g) := hM.of_injective g.range.subtype_injective
  have hC' : IsFiniteLength R (LinearMap.range f) := hM.of_injective f.range.subtype_injective
  have hexf : Function.Exact g.range.subtype f.rangeRestrict := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]
    exact hgf.linearMap_ker_eq
  have hexg : Function.Exact f.range.subtype g.rangeRestrict := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]
    exact hfg.linearMap_ker_eq
  have nf := determinantExactSequenceMap_natural_of_linearEquiv
    iA pC g.range.subtype f.rangeRestrict hiA hpC hexA
    g.range.subtype_injective (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict f))
    hexf hA hM hC hA' hM hC' eA (LinearEquiv.refl R M) eC
    (by ext; rfl) (by ext x; change f x = iC (pC x); rw [hf]; rfl)
  have ng := determinantExactSequenceMap_natural_of_linearEquiv
    iC pA f.range.subtype g.rangeRestrict hiC hpA hexC
    f.range.subtype_injective (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict g))
    hexg hC hM hA hC' hM hA' eC (LinearEquiv.refl R M) eA
    (by ext; rfl) (by ext x; change g x = iA (pA x); rw [hg]; rfl)
  rw [determinantMapLinearEquiv_refl, LinearMap.id_comp] at nf ng
  have hv := LinearMap.congr_fun (periodicDeterminant_spec f g hfg hgf hM)
    (((determinantFunctor R).mapLinearEquiv (finiteLengthIsoHom hA hA' eA) a)
      ⊗ₜ[IsLocalRing.ResidueField R]
      ((determinantFunctor R).mapLinearEquiv (finiteLengthIsoHom hC hC' eC) c))
  have nf' := LinearMap.congr_fun nf (a ⊗ₜ[IsLocalRing.ResidueField R] c)
  have ng' := LinearMap.congr_fun ng (c ⊗ₜ[IsLocalRing.ResidueField R] a)
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe] at nf' ng'
  simp only [LinearMap.comp_apply,
    TensorProduct.comm_tmul, LinearEquiv.coe_coe, LinearMap.smul_apply,
    periodicGamma] at hv
  rwa [nf', ng', ← moduleLength_eq_of_equiv eA, ← moduleLength_eq_of_equiv eC] at hv

/-- The map from the image of `γ` to the kernel of `β` induced by `α`. -/
private abbrev alphaOnGammaToKerBeta (α β γ : M →ₗ[R] M)
    (h : ComplementaryImagesKernels α β γ) :
    LinearMap.range γ →ₗ[R] LinearMap.ker β :=
  (α.comp (LinearMap.range γ).subtype).codRestrict (LinearMap.ker β) (by
    intro x
    rcases LinearMap.mem_range.mp x.2 with ⟨y, hy⟩
    rw [h.ker_beta_eq_range_alpha_gamma]
    exact ⟨y, by simpa [LinearMap.comp_apply] using congrArg α hy⟩)

/-- **Stacks Project, Tag 02PU.** The determinant of `(M, α, βγ)` is the product of the
determinants on the image of `γ` and the quotient by the kernel of `β`. -/
@[stacks 02PU "part (4)"]
theorem periodicDeterminant_mul (α β γ : M →ₗ[R] M)
    (hM : IsFiniteLength R M) (h : ComplementaryImagesKernels α β γ) :
    periodicDeterminant α (β ∘ₗ γ)
        (exact_alpha_betaGamma α β γ h) (exact_betaGamma_alpha α β γ h) hM =
      periodicDeterminant (alphaOnGammaRange α β γ h)
          (betaOnGammaRange α β γ h)
          (exact_alpha_beta_onGammaRange α β γ h)
          (exact_beta_alpha_onGammaRange α β γ h)
          (hM.of_injective (LinearMap.range γ).subtype_injective) *
        periodicDeterminant (alphaOnKerBetaQuotient α β γ h)
          (gammaOnKerBetaQuotient α β γ h)
          (exact_alpha_gamma_onKerBetaQuotient α β γ h)
          (exact_gamma_alpha_onKerBetaQuotient α β γ h)
          (hM.of_surjective (Submodule.mkQ_surjective (LinearMap.ker β))) := by
  let A := LinearMap.ker α
  let B := LinearMap.range γ
  let C := LinearMap.ker β
  let F := LinearMap.range α
  let T := M ⧸ B
  let Q := M ⧸ C
  have hAB : A ≤ B := by
    dsimp only [A, B, C, F]
    rw [h.ker_alpha_eq_range_gamma_beta]
    rintro _ ⟨x, rfl⟩
    exact ⟨β x, rfl⟩
  have hCB : C ≤ B := by
    dsimp only [A, B, C, F]
    rw [h.ker_beta_eq_range_gamma_alpha]
    rintro _ ⟨x, rfl⟩
    exact ⟨α x, rfl⟩
  have hCF : C ≤ F := by
    dsimp only [A, B, C, F]
    rw [h.ker_beta_eq_range_alpha_gamma]
    rintro _ ⟨x, rfl⟩
    exact ⟨γ x, rfl⟩
  let iAB : A →ₗ[R] B := A.subtype.codRestrict B (fun x => hAB x.2)
  let iCB : C →ₗ[R] B := C.subtype.codRestrict B (fun x => hCB x.2)
  let iCF : C →ₗ[R] F := C.subtype.codRestrict F (fun x => hCF x.2)
  let pA : M →ₗ[R] A := (β ∘ₗ γ).codRestrict A (by
    intro x; change (β ∘ₗ γ) x ∈ LinearMap.ker α
    rw [h.ker_alpha_eq_range_beta_gamma]; exact ⟨x, rfl⟩)
  have hpA : Function.Surjective pA := by
    rintro ⟨a, ha⟩
    have ha' : a ∈ LinearMap.range (β ∘ₗ γ) := by
      rw [← h.ker_alpha_eq_range_beta_gamma]; exact ha
    obtain ⟨x, hx⟩ := ha'
    exact ⟨x, Subtype.ext hx⟩
  let pBC : B →ₗ[R] C := alphaOnGammaToKerBeta α β γ h
  let pBA : B →ₗ[R] A := (β.comp B.subtype).codRestrict A (by
    rintro ⟨x, y, rfl⟩
    dsimp only [A, B, C, F]
    rw [h.ker_alpha_eq_range_beta_gamma]
    exact ⟨y, rfl⟩)
  have hpBC : Function.Surjective pBC := by
    rintro ⟨c, hc⟩
    have hc' : c ∈ LinearMap.range (α ∘ₗ γ) := by
      rw [← h.ker_beta_eq_range_alpha_gamma]; exact hc
    obtain ⟨x, hx⟩ := hc'
    exact ⟨⟨γ x, ⟨x, rfl⟩⟩, Subtype.ext hx⟩
  have hpBA : Function.Surjective pBA := by
    intro a
    obtain ⟨x, rfl⟩ := hpA a
    exact ⟨⟨γ x, ⟨x, rfl⟩⟩, rfl⟩
  have hiAB : Function.Injective iAB :=
    Function.Injective.of_comp (f := B.subtype) A.subtype_injective
  have hiCB : Function.Injective iCB :=
    Function.Injective.of_comp (f := B.subtype) C.subtype_injective
  have hiCF : Function.Injective iCF :=
    Function.Injective.of_comp (f := F.subtype) C.subtype_injective
  let fB := alphaOnGammaRange α β γ h
  let gB := betaOnGammaRange α β γ h
  have hfB : fB = iCB.comp pBC := by ext; rfl
  have hgB : gB = iAB.comp pBA := by ext; rfl
  have exB := exact_of_factorizations gB fB (exact_beta_alpha_onGammaRange α β γ h)
    iAB pBA iCB pBC hpBA hiCB hgB hfB
  have exB' := exact_of_factorizations fB gB (exact_alpha_beta_onGammaRange α β γ h)
    iCB pBC iAB pBA hpBC hiAB hfB hgB
  let pF := α.rangeRestrict
  have hpF : Function.Surjective pF :=
    LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict α)
  have hfM : α = F.subtype.comp pF := by ext; rfl
  have hgM : β ∘ₗ γ = A.subtype.comp pA := by ext; rfl
  have exM := exact_of_factorizations (β ∘ₗ γ) α (exact_betaGamma_alpha α β γ h)
    A.subtype pA F.subtype pF hpA F.subtype_injective hgM hfM
  have exM' := exact_of_factorizations α (β ∘ₗ γ) (exact_alpha_betaGamma α β γ h)
    F.subtype pF A.subtype pA hpF A.subtype_injective hfM hgM
  have hkerFT : LinearMap.ker pF ≤ LinearMap.ker B.mkQ := by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero B).mpr
    apply hAB
    exact congrArg Subtype.val (LinearMap.mem_ker.mp hx)
  let pFT : F →ₗ[R] T := descendSurjective pF hpF B.mkQ hkerFT
  have hpFT_apply (x : M) : pFT (pF x) = B.mkQ x :=
    descendSurjective_apply pF hpF B.mkQ hkerFT x
  have hpFT : Function.Surjective pFT := by
    intro t
    obtain ⟨x, rfl⟩ := B.mkQ_surjective t
    exact ⟨pF x, hpFT_apply x⟩
  have exF : Function.Exact iCF pFT := by
    intro f
    obtain ⟨x, rfl⟩ := hpF f
    show pFT (pF x) = 0 ↔ ∃ c, iCF c = pF x
    rw [hpFT_apply]
    constructor
    · intro hx
      have hxB : x ∈ B := (Submodule.Quotient.mk_eq_zero B).mp hx
      have hc : α x ∈ C := by
        dsimp only [A, B, C, F]
        rw [h.ker_beta_eq_range_alpha_gamma]
        obtain ⟨y, rfl⟩ := hxB
        exact ⟨y, rfl⟩
      exact ⟨⟨α x, hc⟩, rfl⟩
    · rintro ⟨c, hc⟩
      apply (Submodule.Quotient.mk_eq_zero B).mpr
      dsimp only [A, B, C, F]
      rw [h.range_gamma_eq_ker_beta_alpha]
      have hc' := congrArg (fun z : F => z.1) hc
      change c.1 = α x at hc'
      show β (α x) = 0
      rw [← hc']
      exact c.2
  have hkerV : LinearMap.ker B.mkQ ≤ LinearMap.ker (C.mkQ.comp α) := by
    intro x hx
    have hxB : x ∈ B := (Submodule.Quotient.mk_eq_zero B).mp hx
    apply (Submodule.Quotient.mk_eq_zero C).mpr
    dsimp only [A, B, C, F]
    rw [h.ker_beta_eq_range_alpha_gamma]
    obtain ⟨y, rfl⟩ := hxB
    exact ⟨y, rfl⟩
  let v : T →ₗ[R] Q := descendSurjective B.mkQ B.mkQ_surjective (C.mkQ.comp α) hkerV
  have hv_apply (x : M) : v (B.mkQ x) = C.mkQ (α x) :=
    descendSurjective_apply B.mkQ B.mkQ_surjective (C.mkQ.comp α) hkerV x
  have hv : Function.Injective v := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro t ht
    obtain ⟨x, rfl⟩ := B.mkQ_surjective t
    have hx : α x ∈ C := (Submodule.Quotient.mk_eq_zero C).mp
      ((hv_apply x).symm.trans ht)
    show B.mkQ x = 0
    apply (Submodule.Quotient.mk_eq_zero B).mpr
    dsimp only [A, B, C, F]
    rw [h.range_gamma_eq_ker_beta_alpha]
    exact hx
  have hkerW : LinearMap.ker pA ≤ LinearMap.ker (C.mkQ.comp γ) := by
    intro x hx
    have hxF : x ∈ F := by
      dsimp only [A, B, C, F]
      rw [h.range_alpha_eq_ker_beta_gamma]
      exact congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    apply (Submodule.Quotient.mk_eq_zero C).mpr
    dsimp only [A, B, C, F]
    rw [h.ker_beta_eq_range_gamma_alpha]
    obtain ⟨y, rfl⟩ := hxF
    exact ⟨y, rfl⟩
  let w : A →ₗ[R] Q := descendSurjective pA hpA (C.mkQ.comp γ) hkerW
  have hw_apply (x : M) : w (pA x) = C.mkQ (γ x) :=
    descendSurjective_apply pA hpA (C.mkQ.comp γ) hkerW x
  have hw : Function.Injective w := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro a ha
    obtain ⟨x, rfl⟩ := hpA a
    have hx : γ x ∈ C := (Submodule.Quotient.mk_eq_zero C).mp
      ((hw_apply x).symm.trans ha)
    show pA x = 0
    apply Subtype.ext
    exact hx
  have hkerU : LinearMap.ker C.mkQ ≤ LinearMap.ker pA := by
    intro x hx
    have hxF := hCF ((Submodule.Quotient.mk_eq_zero C).mp hx)
    have hx0 : (β ∘ₗ γ) x = 0 := by
      have : x ∈ LinearMap.ker (β ∘ₗ γ) := by
        rw [← h.range_alpha_eq_ker_beta_gamma]; exact hxF
      exact this
    apply Subtype.ext
    exact hx0
  let u : Q →ₗ[R] A := descendSurjective C.mkQ C.mkQ_surjective pA hkerU
  have hu_apply (x : M) : u (C.mkQ x) = pA x :=
    descendSurjective_apply C.mkQ C.mkQ_surjective pA hkerU x
  have hu : Function.Surjective u := by
    intro a
    obtain ⟨x, rfl⟩ := hpA a
    exact ⟨C.mkQ x, hu_apply x⟩
  let t : Q →ₗ[R] T := Submodule.factor hCB
  have ht_apply (x : M) : t (C.mkQ x) = B.mkQ x := rfl
  have ht : Function.Surjective t := Submodule.factor_surjective hCB
  let fQ := alphaOnKerBetaQuotient α β γ h
  let gQ := gammaOnKerBetaQuotient α β γ h
  have hfQ : fQ = v.comp t := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := C.mkQ_surjective q
    exact (hv_apply x).symm
  have hgQ : gQ = w.comp u := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := C.mkQ_surjective q
    show C.mkQ (γ x) = w (u (C.mkQ x))
    rw [hu_apply, hw_apply]
  have exQ := exact_of_factorizations gQ fQ (exact_gamma_alpha_onKerBetaQuotient α β γ h)
    w u v t hu hv hgQ hfQ
  have exQ' := exact_of_factorizations fQ gQ (exact_alpha_gamma_onKerBetaQuotient α β γ h)
    v t w u ht hw hfQ hgQ
  have exCQ : Function.Exact C.subtype C.mkQ := LinearMap.exact_subtype_mkQ C
  have exBT : Function.Exact B.subtype B.mkQ := LinearMap.exact_subtype_mkQ B
  have hA : IsFiniteLength R A := hM.of_injective A.subtype_injective
  have hB : IsFiniteLength R B := hM.of_injective B.subtype_injective
  have hC : IsFiniteLength R C := hM.of_injective C.subtype_injective
  have hF : IsFiniteLength R F := hM.of_injective F.subtype_injective
  have hT : IsFiniteLength R T := hM.of_surjective B.mkQ_surjective
  have hQ : IsFiniteLength R Q := hM.of_surjective C.mkQ_surjective
  have commFT : B.mkQ = pFT.comp pF := by ext x; exact (hpFT_apply x).symm
  have commFQ : C.mkQ.comp F.subtype = v.comp pFT := by
    apply LinearMap.ext
    intro f
    obtain ⟨x, rfl⟩ := hpF f
    show C.mkQ (α x) = v (pFT (pF x))
    rw [hpFT_apply, hv_apply]
  have commBQ : C.mkQ.comp B.subtype = w.comp pBA := by
    apply LinearMap.ext
    rintro ⟨x, y, rfl⟩
    exact (hw_apply y).symm
  let d := periodicDeterminant α (β ∘ₗ γ)
    (exact_alpha_betaGamma α β γ h) (exact_betaGamma_alpha α β γ h) hM
  let dB := periodicDeterminant fB gB
    (exact_alpha_beta_onGammaRange α β γ h) (exact_beta_alpha_onGammaRange α β γ h) hB
  let dQ := periodicDeterminant fQ gQ
    (exact_alpha_gamma_onKerBetaQuotient α β γ h)
    (exact_gamma_alpha_onKerBetaQuotient α β γ h) hQ
  let GM := determinantExactSequenceMap A.subtype pF A.subtype_injective hpF exM hA hM hF
  let GN := determinantExactSequenceMap F.subtype pA F.subtype_injective hpA exM' hF hM hA
  let GB := determinantExactSequenceMap iAB pBC hiAB hpBC exB hA hB hC
  let GB' := determinantExactSequenceMap iCB pBA hiCB hpBA exB' hC hB hA
  let GF := determinantExactSequenceMap iCF pFT hiCF hpFT exF hC hF hT
  let GQ := determinantExactSequenceMap w t hw ht exQ hA hQ hT
  let GQ' := determinantExactSequenceMap v u hv hu exQ' hT hQ hA
  let GCQ := determinantExactSequenceMap C.subtype C.mkQ C.subtype_injective
    C.mkQ_surjective exCQ hC hM hQ
  let GBT := determinantExactSequenceMap B.subtype B.mkQ B.subtype_injective
    B.mkQ_surjective exBT hB hM hT
  have assoc1 (a : determinant R A) (c : determinant R C) (z : determinant R T) :
      GBT (GB (a ⊗ₜ[_] c) ⊗ₜ[_] z) = GM (a ⊗ₜ[_] GF (c ⊗ₜ[_] z)) :=
    determinantExactSequenceMap_assoc iAB pBC B.subtype B.mkQ A.subtype pF iCF pFT
      hiAB hpBC exB B.subtype_injective B.mkQ_surjective exBT
      A.subtype_injective hpF exM hiCF hpFT exF
      (by ext; rfl) (by ext; rfl) commFT hA hB hC hM hF hT a c z
  have assoc2 (c : determinant R C) (z : determinant R T) (a : determinant R A) :
      GN (GF (c ⊗ₜ[_] z) ⊗ₜ[_] a) = GCQ (c ⊗ₜ[_] GQ' (z ⊗ₜ[_] a)) :=
    determinantExactSequenceMap_assoc iCF pFT F.subtype pA C.subtype C.mkQ v u
      hiCF hpFT exF F.subtype_injective hpA exM'
      C.subtype_injective C.mkQ_surjective exCQ hv hu exQ'
      (by ext; rfl) commFQ (by apply LinearMap.ext; intro x; exact (hu_apply x).symm)
      hC hF hT hM hQ hA c z a
  have assoc3 (c : determinant R C) (a : determinant R A) (z : determinant R T) :
      GBT (GB' (c ⊗ₜ[_] a) ⊗ₜ[_] z) = GCQ (c ⊗ₜ[_] GQ (a ⊗ₜ[_] z)) :=
    determinantExactSequenceMap_assoc iCB pBA B.subtype B.mkQ C.subtype C.mkQ w t
      hiCB hpBA exB' B.subtype_injective B.mkQ_surjective exBT
      C.subtype_injective C.mkQ_surjective exCQ hw ht exQ
      (by ext; rfl) commBQ (by ext; rfl) hC hB hA hM hQ hT c a z
  have cmpM (a : determinant R A) (f : determinant R F) :
      GN (f ⊗ₜ[_] a) =
        ((-1 : IsLocalRing.ResidueField R) ^ (moduleLength R F * moduleLength R A) * ↑d) •
          GM (a ⊗ₜ[_] f) :=
    periodicDeterminant_comparison α (β ∘ₗ γ) (exact_alpha_betaGamma α β γ h)
      (exact_betaGamma_alpha α β γ h) A.subtype pA F.subtype pF
      A.subtype_injective hpA F.subtype_injective hpF exM exM' hfM hgM hM hA hF a f
  have cmpB (a : determinant R A) (c : determinant R C) :
      GB' (c ⊗ₜ[_] a) =
        ((-1 : IsLocalRing.ResidueField R) ^ (moduleLength R C * moduleLength R A) * ↑dB) •
          GB (a ⊗ₜ[_] c) :=
    periodicDeterminant_comparison fB gB (exact_alpha_beta_onGammaRange α β γ h)
      (exact_beta_alpha_onGammaRange α β γ h) iAB pBA iCB pBC
      hiAB hpBA hiCB hpBC exB exB' hfB hgB hB hA hC a c
  have cmpQ (a : determinant R A) (z : determinant R T) :
      GQ' (z ⊗ₜ[_] a) =
        ((-1 : IsLocalRing.ResidueField R) ^ (moduleLength R T * moduleLength R A) * ↑dQ) •
          GQ (a ⊗ₜ[_] z) :=
    periodicDeterminant_comparison fQ gQ (exact_alpha_gamma_onKerBetaQuotient α β γ h)
      (exact_gamma_alpha_onKerBetaQuotient α β γ h) w u v t
      hw hu hv ht exQ exQ' hfQ hgQ hQ hA hT a z
  let k := IsLocalRing.ResidueField R
  let sM : k := (-1 : k) ^ (moduleLength R F * moduleLength R A) * ↑d
  let sB : k := (-1 : k) ^ (moduleLength R C * moduleLength R A) * ↑dB
  let sQ : k := (-1 : k) ^ (moduleLength R T * moduleLength R A) * ↑dQ
  have compare (a : determinant R A) (c : determinant R C) (z : determinant R T) :
      sM • GM (a ⊗ₜ[k] GF (c ⊗ₜ[k] z)) = (sQ * sB) • GM (a ⊗ₜ[k] GF (c ⊗ₜ[k] z)) := by
    calc
      _ = GN (GF (c ⊗ₜ[k] z) ⊗ₜ[k] a) := (cmpM a _).symm
      _ = GCQ (c ⊗ₜ[k] GQ' (z ⊗ₜ[k] a)) := assoc2 c z a
      _ = sQ • GCQ (c ⊗ₜ[k] GQ (a ⊗ₜ[k] z)) := by
        rw [cmpQ]
        simp only [TensorProduct.tmul_smul, map_smul]
        rfl
      _ = sQ • GBT (GB' (c ⊗ₜ[k] a) ⊗ₜ[k] z) := by rw [assoc3]
      _ = (sQ * sB) • GBT (GB (a ⊗ₜ[k] c) ⊗ₜ[k] z) := by
        rw [cmpB]
        simp only [← TensorProduct.smul_tmul', map_smul, smul_smul]
        rfl
      _ = _ := by rw [assoc1]
  have hGF : Function.Surjective GF :=
    (determinantExactSequenceMap_bijective iCF pFT hiCF hpFT exF hC hF hT).2
  have compareF (a : determinant R A) (f : determinant R F) :
      sM • GM (a ⊗ₜ[k] f) = (sQ * sB) • GM (a ⊗ₜ[k] f) := by
    obtain ⟨x, rfl⟩ := hGF f
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c z => exact compare a c z
    | add x y hx hy =>
        simpa only [map_add, TensorProduct.tmul_add, smul_add] using congrArg₂ (· + ·) hx hy
  have hGM : Function.Surjective GM :=
    (determinantExactSequenceMap_bijective
      A.subtype pF A.subtype_injective hpF exM hA hM hF).2
  have compareM (m : determinant R M) : sM • m = (sQ * sB) • m := by
    obtain ⟨x, rfl⟩ := hGM m
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a f => exact compareF a f
    | add x y hx hy =>
        simpa only [map_add, smul_add] using congrArg₂ (· + ·) hx hy
  have : Nontrivial (determinant R M) :=
    Module.nontrivial_of_finrank_eq_succ (finrank_determinant_eq_one hM)
  obtain ⟨m, hm⟩ := exists_ne (0 : determinant R M)
  have hs : sM = sQ * sB := smul_left_injective k hm (compareM m)
  have hlen : moduleLength R F = moduleLength R C + moduleLength R T := by
    unfold moduleLength
    rw [Module.length_eq_add_of_exact iCF pFT hiCF hpFT exF,
      ENat.toNat_add (Module.length_ne_top_iff.mpr hC) (Module.length_ne_top_iff.mpr hT)]
  apply Units.ext
  show (d : k) = (dB : k) * (dQ : k)
  apply mul_left_cancel₀ (pow_ne_zero (moduleLength R F * moduleLength R A)
    (neg_ne_zero.mpr (one_ne_zero : (1 : k) ≠ 0)))
  show sM = (-1 : k) ^ (moduleLength R F * moduleLength R A) * ((dB : k) * (dQ : k))
  rw [hs]
  dsimp [sQ, sB]
  rw [hlen, Nat.add_mul, pow_add]
  ring

end Local

end AlgebraicGeometry
