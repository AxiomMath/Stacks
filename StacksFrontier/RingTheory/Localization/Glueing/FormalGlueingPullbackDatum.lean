module

public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence
public import StacksFrontier.RingTheory.Localization.Glueing.Transport

/-!
# Glueing data presented by a fibre product

Let `R → S` be a ring map and `f = (f₁, …, f_t)` a finite family in `R`.  The stalkwise proof of
Stacks 0AF0 meets objects of `Glue(R → S, f₁, …, f_t)` (Stacks 05EL) in a particular shape: an
`R`-module `N`, an `S`-module `P` and an `S`-module `Q`, with maps `a : S ⊗_R N → Q` and
`b : P → Q` both of which become bijective after inverting each `f i`.  (At a pair of geometric
points `ȳ ↦ x̄` of Situation 0AEV these are `N = (j_*ℋ)_x̄`, `P = 𝒢_ȳ` and `Q = (j'_*𝒢|_V)_ȳ`.)
Such data determine a glueing datum `pullbackDatum` with generic part `P` and local pieces
`N[1 / fᵢ]`, and the compatible sections `H⁰` of that datum are the fibre product `N ×_Q P` as
soon as `N` is separated and glues along `f` and `Q` is separated along `f`.

Combined with Stacks 05ER this gives the two statements the stalk checks of Stacks 0AF0 need,
in a form that mentions only `N`, `P`, `Q`, `a` and `b`:

* `FormalGlueing.pullbackGenericMap_bijective`: `S ⊗_R (N ×_Q P) → P` is bijective (the stalk
  check of the counit on the `Y`-side);
* `FormalGlueing.pullbackLift_bijective`: a pair `g : M → N`, `h : S ⊗_R M → P` agreeing in `Q`,
  with `h` bijective and `g` bijective after inverting each `f i`, induces a bijection
  `M ≅ N ×_Q P` (the stalk check of the unit).

## Main definitions

* `FormalGlueing.retractDatum`: a glueing datum with its generic part replaced by a module
  mapping into it by a map which is bijective after inverting each `f i` (the direction opposite
  to `FormalGlueing.transportDatum`).
* `FormalGlueing.pullbackDatum`: the glueing datum of `(N, P, Q, a, b)`.
* `FormalGlueing.pullbackSections`: the fibre product `N ×_Q P` as an `R`-module.
* `FormalGlueing.pullbackComparison`: the map of glueing data from the canonical datum of
  `N ×_Q P` to `pullbackDatum`.
* `FormalGlueing.CechSeparated` and `FormalGlueing.CechGlueing`: separation and glueing of a
  module along `f`, i.e. the two halves of exactness of `M → ∏ M[1/fᵢ] ⇉ ∏ M[1/fᵢfⱼ]`.

## Main results

* `FormalGlueing.pullbackToSections_bijective`: `N ×_Q P ≅ H⁰(pullbackDatum)`.
* `FormalGlueing.isIso_pullbackComparison`: under the hypotheses of Stacks 05ER the comparison is
  an isomorphism of glueing data.
* `FormalGlueing.bijective_of_bijective_lTensor_of_bijective_localized`: under the hypotheses of
  Stacks 05ER a map of `R`-modules is bijective when it is so after `S ⊗_R -` and after inverting
  each `f i`.
* `FormalGlueing.pullbackGenericMap_bijective`,
  `FormalGlueing.canonicalLocalMap_pullbackFst_bijective` and
  `FormalGlueing.pullbackLift_bijective`: the consequences listed above.

## Implementation notes

The map `a` is taken out of `S ⊗_R N` rather than out of `N`, so that no `R`-module structure on
the `S`-module `Q` is needed; its restriction to `1 ⊗ N` is the map `N → Q` of the source.  The
datum is built in two moves: `FormalGlueing.transportDatum` moves the generic part of the
canonical datum of `N` forward along `a`, and `FormalGlueing.retractDatum` moves it back along
`b`.  Only the first move needs the power-of-`fᵢ` argument of `transportDatum`; the second is
immediate because the new comparison is the old one precomposed with a localized map.

The two consequences are derived from the *public* statements of Stacks 05ER and Stacks 0H77
only — the unit `FormalGlueing.canonicalSectionsUnit_isIso` and the equivalence
`FormalGlueing.canonicalFunctor_sections_areQuasiInverse`, which makes both functors reflect
isomorphisms — so nothing about the internal counit of that proof is needed.

## References

* [Stacks Project, Tag 05EL](https://stacks.math.columbia.edu/tag/05EL)
* [Stacks Project, Tag 05ER](https://stacks.math.columbia.edu/tag/05ER)
* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
-/

@[expose] public noncomputable section

namespace FormalGlueing

universe u v w

open CategoryTheory Cech TensorProduct

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R)

/-! ### Moving the generic part along a map into it -/

section Retract

variable (Y : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
  (G : ModuleCat.{max u v w} S) (ψ : G ⟶ Y.generic)

/-- The localization of a map into the generic part at `f i`, as a map over `S`. -/
abbrev retractMap (i : Fin r) :
    LocalizedModule.Away (algebraMap R S (f i)) G →ₗ[S]
      LocalizedModule.Away (algebraMap R S (f i)) Y.generic :=
  (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) ψ.hom).restrictScalars S

variable (hψ : ∀ i, Function.Bijective (retractMap S f Y G ψ i))

/-- The comparison of the new generic part with the local pieces: localize `ψ`, then compare. -/
def retractAlpha (i : Fin r) :
    LocalizedModule.Away (algebraMap R S (f i)) G ≃ₗ[S]
      TensorProduct R S (restrictFromAway f i (Y.localPiece i)) :=
  (LinearEquiv.ofBijective _ (hψ i)).trans (Y.alpha i)

/-- `retractAlpha` sends `m / 1` to the image under `Y.alpha i` of `ψ m / 1`. -/
theorem retractAlpha_mk (i : Fin r) (m : G) :
    retractAlpha S f Y G ψ hψ i
        (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) G m) =
      Y.alpha i (LocalizedModule.mkLinearMap
        (Submonoid.powers (algebraMap R S (f i))) Y.generic (ψ m)) := by
  exact congrArg (Y.alpha i) (LocalizedModule.map_mk _ _ _ _)

/-- A system of glueing data with its generic part replaced by a module mapping into it by a map
which becomes bijective after inverting each `f i`. -/
def retractDatum : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f) where
  generic := G
  localPiece := Y.localPiece
  alpha := retractAlpha S f Y G ψ hψ
  alphaIJ := Y.alphaIJ
  alpha_compatibility i j m := by
    rw [retractAlpha_mk, retractAlpha_mk]
    exact Y.alpha_compatibility i j (ψ m)
  cocycle := Y.cocycle

end Retract




/-! ### The datum of a fibre product -/

section Pullback

/-- The underlying `R`-module of an `S`-module is a scalar tower. -/
theorem restrictFromTarget_isScalarTower (M : ModuleCat.{w} S) :
    IsScalarTower R S (restrictFromTarget (R := R) S M) :=
  ⟨fun a b m ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩


variable (N : ModuleCat.{max u v w} R) (P Q : ModuleCat.{max u v w} S)
  (a : ModuleCat.of S (S ⊗[R] N) ⟶ Q) (b : P ⟶ Q)
  (ha : ∀ i, Function.Bijective (transportMap S f (canonicalDatum S f N) Q a i))
  (hb : ∀ i, Function.Bijective
    ((LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) b.hom).restrictScalars S))

/-- The glueing datum with generic part `P` and local pieces `N[1/fᵢ]`, the comparison
`P[1/fᵢ] ≅ S ⊗ N[1/fᵢ]` being the composite of the localizations at `f i` of `b : P → Q` and of
`a : S ⊗ N → Q`, both assumed bijective. -/
def pullbackDatum : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f) :=
  retractDatum S f (transportDatum S f (canonicalDatum S f N) Q a ha) P b hb

/-- The generic part of `pullbackDatum` is `P`. -/
theorem pullbackDatum_generic : (pullbackDatum S f N P Q a b ha hb).generic = P := rfl

/-- The local pieces of `pullbackDatum` are the localizations `N[1 / fᵢ]`. -/
theorem pullbackDatum_localPiece :
    (pullbackDatum S f N P Q a b ha hb).localPiece = canonicalLocalPiece f N := rfl

/-- The overlap comparisons of `pullbackDatum` are those of the canonical datum of `N`. -/
theorem pullbackDatum_alphaIJ :
    (pullbackDatum S f N P Q a b ha hb).alphaIJ = canonicalAlphaIJ f N := rfl

/-- The comparison of `pullbackDatum` sends `p / 1` to the image of `b p / 1` under the
transported comparison of `Q`. -/
theorem pullbackDatum_alpha_mk (i : Fin r) (p : P) :
    (pullbackDatum S f N P Q a b ha hb).alpha i
        (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i)))
          (pullbackDatum S f N P Q a b ha hb).generic p) =
      transportAlpha S f (canonicalDatum S f N) Q a ha i
        (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) Q (b p)) :=
  congrArg (transportAlpha S f (canonicalDatum S f N) Q a ha i)
    (LocalizedModule.map_mk (Submonoid.powers (algebraMap R S (f i))) b.hom p 1)

/-- The fibre product `N ×_Q P` of `n ↦ a (1 ⊗ n)` and `b`, as an `R`-module. -/
def pullbackSections : Submodule R (N × restrictFromTarget (R := R) S P) where
  carrier := {x | a.hom ((1 : S) ⊗ₜ[R] x.1) = b.hom x.2}
  zero_mem' := by
    change a.hom ((1 : S) ⊗ₜ[R] (0 : N)) = b.hom 0
    rw [TensorProduct.tmul_zero, map_zero, map_zero]
  add_mem' := by
    rintro x y (hx : a.hom _ = b.hom _) (hy : a.hom _ = b.hom _)
    change a.hom ((1 : S) ⊗ₜ[R] (x.1 + y.1)) = b.hom (x.2 + y.2)
    rw [TensorProduct.tmul_add]
    exact (map_add a.hom _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add b.hom _ _).symm)
  smul_mem' := by
    rintro c x (hx : a.hom _ = b.hom _)
    change a.hom ((1 : S) ⊗ₜ[R] (c • x.1)) = b.hom ((algebraMap R S c) • (show P from x.2))
    rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul S c, map_smul, map_smul, hx]

/-- The fibre product as an object of `ModuleCat`. -/
abbrev pullbackModule : ModuleCat.{max u v w} R :=
  ModuleCat.of R (pullbackSections S N P Q a b)

/-- The first projection of the fibre product. -/
def pullbackFst : pullbackModule S N P Q a b ⟶ N :=
  ModuleCat.ofHom ((LinearMap.fst R _ _).comp (pullbackSections S N P Q a b).subtype)

attribute [local instance] restrictFromTarget_isScalarTower

/-- The second projection of the fibre product, extended to `S ⊗ (N ×_Q P) → P`. -/
def pullbackGenericMap : S ⊗[R] pullbackSections S N P Q a b →ₗ[S] P :=
  ((LinearMap.snd R _ _).comp (pullbackSections S N P Q a b).subtype).liftBaseChange S

/-- `pullbackGenericMap` sends `s ⊗ (n, p)` to `s • p`. -/
theorem pullbackGenericMap_tmul (s : S) (x : pullbackSections S N P Q a b) :
    pullbackGenericMap S N P Q a b (s ⊗ₜ[R] x) = s • (show P from x.1.2) := rfl

/-- The map of glueing data from the canonical datum of the fibre product to `pullbackDatum`:
the second projection on generic parts, the first projection on local pieces. -/
def pullbackComparison :
    ModuleGlueingMap S f (localizationComparisons f)
      (canonicalDatum S f (pullbackModule S N P Q a b)) (pullbackDatum S f N P Q a b ha hb) where
  generic := ModuleCat.ofHom (pullbackGenericMap S N P Q a b)
  localPiece := canonicalLocalMap f (pullbackFst S N P Q a b)
  alpha_compatibility i m := by
    dsimp only [canonicalDatum] at m ⊢
    change S ⊗[R] pullbackSections S N P Q a b at m
    induction m using TensorProduct.induction_on with
    | zero =>
      change (pullbackDatum S f N P Q a b ha hb).alpha i (LocalizedModule.mkLinearMap _ _
          (pullbackGenericMap S N P Q a b 0)) = TensorProduct.map LinearMap.id _
        (canonicalAlpha S f (pullbackModule S N P Q a b) i (LocalizedModule.mkLinearMap _ _ 0))
      simp only [map_zero]
      exact (congrArg _ (map_zero _)).trans (map_zero _)
    | tmul s x =>
      have hg : pullbackGenericMap S N P Q a b (s ⊗ₜ[R] x) =
          s • pullbackGenericMap S N P Q a b ((1 : S) ⊗ₜ[R] x) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hb' : b (pullbackGenericMap S N P Q a b ((1 : S) ⊗ₜ[R] x)) =
          a ((1 : S) ⊗ₜ[R] x.1.1) := by
        rw [pullbackGenericMap_tmul, one_smul]
        exact x.2.symm
      change (pullbackDatum S f N P Q a b ha hb).alpha i (LocalizedModule.mkLinearMap _ _
          (pullbackGenericMap S N P Q a b (s ⊗ₜ[R] x))) = TensorProduct.map LinearMap.id _
        (canonicalAlpha S f (pullbackModule S N P Q a b) i
          (LocalizedModule.mkLinearMap _ _ (s ⊗ₜ[R] x)))
      have h2 : ∀ y : (pullbackDatum S f N P Q a b ha hb).generic,
          (pullbackDatum S f N P Q a b ha hb).alpha i (LocalizedModule.mkLinearMap _ _ (s • y)) =
            s • (pullbackDatum S f N P Q a b ha hb).alpha i (LocalizedModule.mkLinearMap _ _ y) :=
        fun y ↦ by rw [map_smul, map_smul]
      rw [hg]
      refine (h2 _).trans ?_
      rw [pullbackDatum_alpha_mk, hb']
      refine (congrArg (s • ·) (transportAlpha_mk S f (canonicalDatum S f N) Q a ha i
        ((1 : S) ⊗ₜ[R] x.1.1))).trans ?_
      rw [canonicalAlpha_mk, TensorProduct.map_tmul]
      change s • canonicalAlpha S f N i
          (LocalizedModule.mkLinearMap _ _ ((1 : S) ⊗ₜ[R] x.1.1)) = _
      rw [canonicalAlpha_mk, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      exact congrArg (TensorProduct.mk R S _ s)
        (canonicalLocalMap_mk f (pullbackFst S N P Q a b) i x).symm
    | add x y hx hy =>
      change (pullbackDatum S f N P Q a b ha hb).alpha i (LocalizedModule.mkLinearMap _ _
          (pullbackGenericMap S N P Q a b (x + y))) = TensorProduct.map LinearMap.id _
        (canonicalAlpha S f (pullbackModule S N P Q a b) i
          (LocalizedModule.mkLinearMap _ _ (x + y)))
      have hadd : ∀ y z : (pullbackDatum S f N P Q a b ha hb).generic,
          (pullbackDatum S f N P Q a b ha hb).alpha i (LocalizedModule.mkLinearMap _ _ (y + z)) =
            (pullbackDatum S f N P Q a b ha hb).alpha i (LocalizedModule.mkLinearMap _ _ y) +
              (pullbackDatum S f N P Q a b ha hb).alpha i (LocalizedModule.mkLinearMap _ _ z) :=
        fun y z ↦ by rw [map_add, map_add]
      rw [map_add (pullbackGenericMap S N P Q a b)]
      refine (hadd _ _).trans ?_
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hy
  alphaIJ_compatibility i j m :=
    (canonicalDatumMap S f (pullbackFst S N P Q a b)).alphaIJ_compatibility i j m

/-- The fibre product mapped to the compatible sections of `pullbackDatum`: a pair `(n, p)` goes
to `(p, (n / 1)ᵢ)`. -/
def pullbackToSections :
    pullbackSections S N P Q a b →ₗ[R]
      compatibleSections S f (localizationComparisons f) (pullbackDatum S f N P Q a b ha hb) :=
  (compatibleSectionsMap S f (pullbackComparison S f N P Q a b ha hb)).comp
    (canonicalToCompatibleSections S f (pullbackModule S N P Q a b))

/-- The generic component of `pullbackToSections (n, p)` is `p`. -/
theorem pullbackToSections_generic (x : pullbackSections S N P Q a b) :
    (pullbackToSections S f N P Q a b ha hb x).1.1 = x.1.2 :=
  one_smul S (show P from x.1.2)

/-- The `i`-th local component of `pullbackToSections (n, p)` is `n / 1` in `N[1 / fᵢ]`. -/
theorem pullbackToSections_local (x : pullbackSections S N P Q a b) (i : Fin r) :
    (pullbackToSections S f N P Q a b ha hb x).1.2 i = canonicalLocalMk f N i x.1.1 :=
  canonicalLocalMap_mk f (pullbackFst S N P Q a b) i x

/-- Separation of a module along `f`: an element killed by a power of every `f i` is zero. -/
def CechSeparated (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∀ m : M, (∀ i, ∃ k : ℕ, f i ^ k • m = 0) → m = 0

/-- Glueing for a module along `f`: a family of elements of the `M[1 / fᵢ]` which agree in the
`M[1 / fᵢfⱼ]` comes from an element of `M`. -/
def CechGlueing (M : ModuleCat.{w} R) : Prop :=
  ∀ x : ∀ i, restrictFromAway f i (canonicalLocalPiece f M i),
    (∀ i j, canonicalAlphaIJ f M i j (LocalizedModule.mkLinearMap (cechSub f {j}) _ (x i)) =
      LocalizedModule.mkLinearMap (cechSub f {i}) _ (x j)) →
    ∃ m : M, ∀ i, canonicalLocalMk f M i m = x i

/-- If `N` is separated and glues along `f` and `Q` is separated along `f`, then
`pullbackToSections` is a bijection of `N ×_Q P` onto the compatible sections of
`pullbackDatum`. -/
theorem pullbackToSections_bijective (hN : CechSeparated f N) (hN' : CechGlueing f N)
    (hQ : CechSeparated (fun i ↦ algebraMap R S (f i)) Q) :
    Function.Bijective (pullbackToSections S f N P Q a b ha hb) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h2 : x.1.2 = 0 := by
      rw [← pullbackToSections_generic S f N P Q a b ha hb x, hx]
      rfl
    have h1 : x.1.1 = 0 := by
      refine hN _ fun i ↦ ?_
      have h := pullbackToSections_local S f N P Q a b ha hb x i
      rw [hx] at h
      obtain ⟨⟨c, k, rfl⟩, hc⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f i))
        (canonicalLocalMk f N i)).1 h.symm
      exact ⟨k, hc⟩
    exact Subtype.ext (Prod.ext h1 h2)
  · rintro ⟨⟨p, x⟩, h1, h2⟩
    obtain ⟨n, hn⟩ := hN' x h2
    have hab : a ((1 : S) ⊗ₜ[R] n) = b p := by
      refine sub_eq_zero.1 (hQ _ fun i ↦ ?_)
      have hi : transportAlpha S f (canonicalDatum S f N) Q a ha i
          (LocalizedModule.mkLinearMap _ Q (b p)) =
            (TensorProduct.mk R S _) 1 (canonicalLocalMk f N i n) :=
        (pullbackDatum_alpha_mk S f N P Q a b ha hb i p).symm.trans
          ((h1 i).trans (congrArg ((TensorProduct.mk R S _) 1) (hn i).symm))
      have hi' : transportAlpha S f (canonicalDatum S f N) Q a ha i
          (LocalizedModule.mkLinearMap _ Q (b p)) =
        transportAlpha S f (canonicalDatum S f N) Q a ha i
          (LocalizedModule.mkLinearMap _ Q (a ((1 : S) ⊗ₜ[R] n))) := by
        refine hi.trans ?_
        refine Eq.trans ?_ (transportAlpha_mk S f (canonicalDatum S f N) Q a ha i
          ((1 : S) ⊗ₜ[R] n)).symm
        exact (canonicalAlpha_mk S f N i 1 n).symm
      obtain ⟨⟨c, k, rfl⟩, hc⟩ := (IsLocalizedModule.eq_iff_exists
        (Submonoid.powers (algebraMap R S (f i))) (LocalizedModule.mkLinearMap _ Q)).1
          ((transportAlpha S f (canonicalDatum S f N) Q a ha i).injective hi').symm
      refine ⟨k, ?_⟩
      show (algebraMap R S (f i)) ^ k • _ = 0
      rw [smul_sub]
      exact sub_eq_zero.2 hc
    refine ⟨⟨(n, p), hab⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact pullbackToSections_generic S f N P Q a b ha hb _
    · funext i
      exact (pullbackToSections_local S f N P Q a b ha hb _ i).trans (hn i)

variable (hflat : Module.Flat R S)
  (hq : Function.Bijective
    (Ideal.quotientMap ((Ideal.span (Set.range f)).map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map))

include hflat hq in
/-- Under the hypotheses of Stacks 05ER, the compatible-sections functor reflects isomorphisms. -/
theorem compatibleSectionsFunctor_reflectsIsomorphisms :
    letI := moduleGlueingCategory S f (localizationComparisons f)
    (compatibleSectionsFunctor.{u, v, w} S f (localizationComparisons f)).ReflectsIsomorphisms := by
  let c := moduleGlueingConstruction.{u, v, w} S f
  let := c.category
  obtain ⟨e, -, he⟩ := canonicalFunctor_sections_areQuasiInverse.{u, v, w} R S f hflat hq
  have h : e.inverse.ReflectsIsomorphisms := inferInstance
  rw [he] at h
  exact h

include hflat hq in
/-- Under the hypotheses of Stacks 05ER, the canonical functor reflects isomorphisms. -/
theorem canonicalFunctor_reflectsIsomorphisms :
    letI := moduleGlueingCategory S f (localizationComparisons f)
    (canonicalFunctor.{u, v, w} S f).ReflectsIsomorphisms := by
  let c := moduleGlueingConstruction.{u, v, w} S f
  let := c.category
  obtain ⟨e, he, -⟩ := canonicalFunctor_sections_areQuasiInverse.{u, v, w} R S f hflat hq
  have h : e.functor.ReflectsIsomorphisms := inferInstance
  rw [he] at h
  exact h

include hflat hq in
/-- **Under the hypotheses of Stacks 05ER a map of `R`-modules is bijective as soon as it is so
after base change to `S` and after inverting each `f i`.** -/
theorem bijective_of_bijective_lTensor_of_bijective_localized
    {M M' : ModuleCat.{max u v w} R} (g : M ⟶ M')
    (hg : Function.Bijective (AlgebraTensorModule.lTensor S S g.hom))
    (hl : ∀ i, Function.Bijective (canonicalLocalMap f g i)) :
    Function.Bijective g := by
  let := moduleGlueingCategory S f (localizationComparisons f)
  have := canonicalFunctor_reflectsIsomorphisms S f hflat hq
  have : IsIso ((canonicalFunctor S f).map g) :=
    glueingMap_isIso_of_bijective S f (canonicalDatumMap S f g) hg hl
  have : IsIso g := isIso_of_reflects_iso g (canonicalFunctor S f)
  exact (asIso g).toLinearEquiv.bijective

include hflat hq in
/-- Under the hypotheses of Stacks 05ER, if `N` is separated and glues along `f` and `Q` is
separated along `f`, then `pullbackComparison` is an isomorphism of glueing data. -/
theorem isIso_pullbackComparison (hN : CechSeparated f N) (hN' : CechGlueing f N)
    (hQ : CechSeparated (fun i ↦ algebraMap R S (f i)) Q) :
    letI := moduleGlueingCategory S f (localizationComparisons f)
    IsIso (show canonicalDatum S f (pullbackModule S N P Q a b) ⟶
      pullbackDatum S f N P Q a b ha hb from pullbackComparison S f N P Q a b ha hb) := by
  let := moduleGlueingCategory S f (localizationComparisons f)
  have := compatibleSectionsFunctor_reflectsIsomorphisms S f hflat hq
  have : IsIso (canonicalSectionsUnit.{u, v, w} S f) :=
    canonicalSectionsUnit_isIso R S f hflat hq
  let eθ := LinearEquiv.ofBijective _ (pullbackToSections_bijective S f N P Q a b ha hb hN hN' hQ)
  let φ : canonicalDatum S f (pullbackModule S N P Q a b) ⟶ pullbackDatum S f N P Q a b ha hb :=
    pullbackComparison S f N P Q a b ha hb
  have h1 : IsIso ((canonicalSectionsUnit S f).app (pullbackModule S N P Q a b) ≫
      (compatibleSectionsFunctor S f (localizationComparisons f)).map φ) :=
    ⟨⟨ModuleCat.ofHom eθ.symm.toLinearMap,
      by ext x; exact eθ.symm_apply_apply x, by ext x; exact eθ.apply_symm_apply x⟩⟩
  have h0 : IsIso ((canonicalSectionsUnit S f).app (pullbackModule S N P Q a b)) :=
    inferInstance
  have : IsIso ((compatibleSectionsFunctor S f (localizationComparisons f)).map φ) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _
      ((canonicalSectionsUnit S f).app (pullbackModule S N P Q a b))
      ((compatibleSectionsFunctor S f (localizationComparisons f)).map φ) h0 h1
  exact isIso_of_reflects_iso φ (compatibleSectionsFunctor S f (localizationComparisons f))

/-- If `pullbackComparison` is an isomorphism of glueing data, both its components are
bijective. -/
private theorem pullbackComparison_bijective
    (hiso : letI := moduleGlueingCategory S f (localizationComparisons f)
      IsIso (show canonicalDatum S f (pullbackModule S N P Q a b) ⟶
        pullbackDatum S f N P Q a b ha hb from pullbackComparison S f N P Q a b ha hb)) :
    Function.Bijective (pullbackGenericMap S N P Q a b) ∧
      ∀ i, Function.Bijective (canonicalLocalMap f (pullbackFst S N P Q a b) i) := by
  let := moduleGlueingCategory S f (localizationComparisons f)
  have := hiso
  let φ : canonicalDatum S f (pullbackModule S N P Q a b) ⟶ pullbackDatum S f N P Q a b ha hb :=
    pullbackComparison S f N P Q a b ha hb
  let e : ModuleCat.of S (S ⊗[R] pullbackSections S N P Q a b) ≅ P :=
    { hom := ModuleCat.ofHom (pullbackGenericMap S N P Q a b)
      inv := ModuleGlueingMap.generic (inv φ)
      hom_inv_id := congrArg ModuleGlueingMap.generic (IsIso.hom_inv_id φ)
      inv_hom_id := congrArg ModuleGlueingMap.generic (IsIso.inv_hom_id φ) }
  refine ⟨e.toLinearEquiv.bijective, fun i ↦ ?_⟩
  let e' : canonicalLocalPiece f (pullbackModule S N P Q a b) i ≅ canonicalLocalPiece f N i :=
    { hom := canonicalLocalMap f (pullbackFst S N P Q a b) i
      inv := ModuleGlueingMap.localPiece (inv φ) i
      hom_inv_id := congrFun (congrArg ModuleGlueingMap.localPiece (IsIso.hom_inv_id φ)) i
      inv_hom_id := congrFun (congrArg ModuleGlueingMap.localPiece (IsIso.inv_hom_id φ)) i }
  exact e'.toLinearEquiv.bijective

include ha hb hflat hq in
/-- **The generic part of the fibre product.**  Under the hypotheses of Stacks 05ER, if `N` is
separated and glues along `f` and `Q` is separated along `f`, the map
`S ⊗_R (N ×_Q P) → P` is bijective. -/
theorem pullbackGenericMap_bijective (hN : CechSeparated f N) (hN' : CechGlueing f N)
    (hQ : CechSeparated (fun i ↦ algebraMap R S (f i)) Q) :
    Function.Bijective (pullbackGenericMap S N P Q a b) :=
  (pullbackComparison_bijective S f N P Q a b ha hb
    (isIso_pullbackComparison S f N P Q a b ha hb hflat hq hN hN' hQ)).1

include ha hb hflat hq in
/-- **The local pieces of the fibre product.**  Under the same hypotheses the first projection
`N ×_Q P → N` becomes bijective after inverting each `f i`. -/
theorem canonicalLocalMap_pullbackFst_bijective (hN : CechSeparated f N) (hN' : CechGlueing f N)
    (hQ : CechSeparated (fun i ↦ algebraMap R S (f i)) Q) (i : Fin r) :
    Function.Bijective (canonicalLocalMap f (pullbackFst S N P Q a b) i) :=
  (pullbackComparison_bijective S f N P Q a b ha hb
    (isIso_pullbackComparison S f N P Q a b ha hb hflat hq hN hN' hQ)).2 i

/-- A map into the fibre product, from a pair of maps `u : M → N` and `v : S ⊗ M → P` agreeing
in `Q`. -/
def pullbackLift (M : ModuleCat.{max u v w} R) (g : M ⟶ N) (h : ModuleCat.of S (S ⊗[R] M) ⟶ P)
    (hgh : ∀ m : M, a ((1 : S) ⊗ₜ[R] g m) = b (h ((1 : S) ⊗ₜ[R] m))) :
    M →ₗ[R] pullbackSections S N P Q a b where
  toFun m := ⟨(g m, h ((1 : S) ⊗ₜ[R] m)), hgh m⟩
  map_add' m m' := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_add g.hom m m'
    · change h ((1 : S) ⊗ₜ[R] (m + m')) = h ((1 : S) ⊗ₜ[R] m) + h ((1 : S) ⊗ₜ[R] m')
      rw [TensorProduct.tmul_add, map_add]
  map_smul' c m := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_smul g.hom c m
    · change h ((1 : S) ⊗ₜ[R] (c • m)) = (algebraMap R S c) • h ((1 : S) ⊗ₜ[R] m)
      rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul S c, map_smul]

/-- Localizing at `f i` is compatible with composition of maps of `R`-modules. -/
theorem canonicalLocalMap_comp {M M' M'' : ModuleCat.{w} R} (g : M ⟶ M') (h : M' ⟶ M'')
    (i : Fin r) (x : canonicalLocalPiece f M i) :
    canonicalLocalMap f (g ≫ h) i x = canonicalLocalMap f h i (canonicalLocalMap f g i x) := by
  induction x using LocalizedModule.induction_on with
  | h m c =>
    show LocalizedModule.map _ (h.hom.comp g.hom) (LocalizedModule.mk m c) =
      LocalizedModule.map _ h.hom (LocalizedModule.map _ g.hom (LocalizedModule.mk m c))
    simp only [LocalizedModule.map_mk, LinearMap.comp_apply]

include ha hb hflat hq in
/-- **Maps into the fibre product.**  Under the hypotheses of Stacks 05ER, if `N` is separated
and glues along `f` and `Q` is separated along `f`, then a pair `g : M → N`, `h : S ⊗ M → P`
agreeing in `Q`, with `h` bijective and `g` bijective after inverting each `f i`, induces a
bijection of `M` onto `N ×_Q P`. -/
theorem pullbackLift_bijective (hN : CechSeparated f N) (hN' : CechGlueing f N)
    (hQ : CechSeparated (fun i ↦ algebraMap R S (f i)) Q)
    (M : ModuleCat.{max u v w} R) (g : M ⟶ N) (h : ModuleCat.of S (S ⊗[R] M) ⟶ P)
    (hgh : ∀ m : M, a ((1 : S) ⊗ₜ[R] g m) = b (h ((1 : S) ⊗ₜ[R] m)))
    (hh : Function.Bijective h.hom) (hg : ∀ i, Function.Bijective (canonicalLocalMap f g i)) :
    Function.Bijective (pullbackLift S N P Q a b M g h hgh) := by
  let w : M ⟶ pullbackModule S N P Q a b := ModuleCat.ofHom (pullbackLift S N P Q a b M g h hgh)
  refine bijective_of_bijective_lTensor_of_bijective_localized S f hflat hq w ?_ ?_
  · have hcomp : (pullbackGenericMap S N P Q a b) ∘ (AlgebraTensorModule.lTensor S S w.hom) =
        h.hom := by
      funext z
      induction z using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero h.hom).symm
      | tmul s m =>
        show s • h.hom ((1 : S) ⊗ₜ[R] m) = h.hom (s ⊗ₜ[R] m)
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy =>
        simp only [Function.comp_apply, map_add] at hx hy ⊢
        rw [hx, hy]
    rw [← hcomp] at hh
    exact (Function.Bijective.of_comp_iff'
      (pullbackGenericMap_bijective S f N P Q a b ha hb hflat hq hN hN' hQ) _).1 hh
  · intro i
    have hcomp : (canonicalLocalMap f (pullbackFst S N P Q a b) i) ∘ (canonicalLocalMap f w i) =
        canonicalLocalMap f g i := by
      funext x
      exact (canonicalLocalMap_comp f w (pullbackFst S N P Q a b) i x).symm
    have := hg i
    rw [← hcomp] at this
    exact (Function.Bijective.of_comp_iff'
      (canonicalLocalMap_pullbackFst_bijective S f N P Q a b ha hb hflat hq hN hN' hQ i) _).1 this

end Pullback

/-! ### Glueing in terms of elements -/

section Elementary

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- Glueing along `f` written with elements and powers: a family `nᵢ`, read as `nᵢ / fᵢᵏ`, whose
members agree in every `M[1 / fᵢfⱼ]`, comes from an element of `M`. -/
def CechGlueingElementary (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (k : ℕ) (n : Fin r → M),
    (∀ i j, ∃ l : ℕ, (f i * f j) ^ l • (f j ^ k • n i - f i ^ k • n j) = 0) →
    ∃ m : M, ∀ i, ∃ l : ℕ, f i ^ l • (f i ^ k • m - n i) = 0

/-- The map `M → M[1 / fᵢ]` commutes with multiplication by `a ^ k`. -/
theorem canonicalLocalMk_pow_smul (M : ModuleCat.{w} R) (i : Fin r) (a : R) (k : ℕ) (m : M) :
    a ^ k • canonicalLocalMk f M i m = canonicalLocalMk f M i (a ^ k • m) :=
  (map_smul (canonicalLocalMk f M i) _ m).symm

/-- **Glueing in terms of elements gives glueing in terms of the canonical local pieces.** -/
theorem cechGlueing_of_elementary (M : ModuleCat.{w} R) (hM : CechGlueingElementary f M) :
    CechGlueing f M := by
  classical
  intro x hx
  have hpow : ∀ (i : Fin r) (a : ℕ), f i ^ a ∈ Submonoid.powers (f i) :=
    fun i a ↦ (Submonoid.mem_powers_iff _ _).2 ⟨a, rfl⟩
  have hsurj : ∀ i, ∃ (k : ℕ) (n : M), f i ^ k • x i = canonicalLocalMk f M i n := by
    intro i
    obtain ⟨⟨n, c⟩, hc⟩ := IsLocalizedModule.surj (Submonoid.powers (f i))
      (canonicalLocalMk f M i) (x i)
    obtain ⟨k, hk⟩ := c.2
    refine ⟨k, n, ?_⟩
    rw [show f i ^ k = (c : R) from hk]
    exact hc
  choose k n hkn using hsurj
  set K := ∑ i, k i with hK
  have hle : ∀ i, k i ≤ K := fun i ↦ Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ i)
  let n' : Fin r → M := fun i ↦ f i ^ (K - k i) • n i
  have hn' : ∀ i, f i ^ K • x i = canonicalLocalMk f M i (n' i) := by
    intro i
    have h : f i ^ (K - k i) • f i ^ k i • x i = f i ^ (K - k i) • canonicalLocalMk f M i (n i) :=
      congrArg (f i ^ (K - k i) • ·) (hkn i)
    rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (hle i), canonicalLocalMk_pow_smul] at h
    exact h
  have hunit : ∀ i (a : ℕ) (y : restrictFromAway f i (canonicalLocalPiece f M i)),
      f i ^ a • y = 0 → y = 0 := by
    intro i a y hy
    have hu := IsLocalizedModule.map_units (canonicalLocalMk f M i) ⟨f i ^ a, hpow i a⟩
    rw [Module.End.isUnit_iff] at hu
    exact hu.1 (hy.trans (map_zero _).symm)
  obtain ⟨m, hm⟩ := hM K n' (by
    intro i j
    have e1 : (f i * f j) ^ K • x i = canonicalLocalMk f M i (f j ^ K • n' i) := by
      rw [mul_pow, mul_comm (f i ^ K), mul_smul, hn' i, canonicalLocalMk_pow_smul]
    have e2 : (f i * f j) ^ K • x j = canonicalLocalMk f M j (f i ^ K • n' j) := by
      rw [mul_pow, mul_smul, hn' j, canonicalLocalMk_pow_smul]
    have h2 : canonicalAlphaIJ f M i j (LocalizedModule.mkLinearMap (cechSub f {j}) _
        ((f i * f j) ^ K • x i)) =
          LocalizedModule.mkLinearMap (cechSub f {i}) _ ((f i * f j) ^ K • x j) := by
      rw [map_smul, map_smul, hx i j, map_smul]
    rw [e1, e2, canonicalAlphaIJ_mk] at h2
    let Φ := (LocalizedModule.mkLinearMap (cechSub f {i}) _).comp (canonicalLocalMk f M j)
    have hΦ : Φ (f j ^ K • n' i - f i ^ K • n' j) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 h2
    have hloc : IsLocalizedModule
        (Submonoid.closure (f '' (↑({j} ∪ {i} : Finset (Fin r)) : Set (Fin r)))) Φ :=
      canonicalOverlap_isLocalized f M j {i}
    obtain ⟨⟨c, hc⟩, hc0⟩ := (IsLocalizedModule.eq_zero_iff
      (Submonoid.closure (f '' (↑({j} ∪ {i} : Finset (Fin r)) : Set (Fin r)))) Φ).1 hΦ
    have himg : f '' (↑({j} ∪ {i} : Finset (Fin r)) : Set (Fin r)) = {f j, f i} := by
      ext y
      simp [or_comm]
    rw [himg, Submonoid.mem_closure_pair] at hc
    obtain ⟨a, b, rfl⟩ := hc
    refine ⟨a + b, ?_⟩
    have hsplit : (f i * f j) ^ (a + b) = (f i ^ a * f j ^ b) * (f j ^ a * f i ^ b) := by ring
    rw [hsplit, mul_smul]
    change (f j ^ a * f i ^ b) • (f j ^ K • n' i - f i ^ K • n' j) = 0 at hc0
    rw [hc0, smul_zero])
  refine ⟨m, fun i ↦ ?_⟩
  obtain ⟨l, hl⟩ := hm i
  apply sub_eq_zero.1
  apply hunit i K
  rw [smul_sub, hn' i, canonicalLocalMk_pow_smul, ← map_sub]
  exact (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f i)) (canonicalLocalMk f M i)).2
    ⟨⟨f i ^ l, hpow i l⟩, hl⟩

end Elementary

end FormalGlueing

end
