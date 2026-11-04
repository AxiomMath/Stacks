module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom
public import StacksFrontier.AlgebraicGeometry.Morphism.Composition
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Hom
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SituationRestrict
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.CanonicalSymHom
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion

/-!
# Homomorphisms of graded algebras over an affine scheme are read on global sections

Let `S` be an affine scheme and let `A`, `B` be quasi-coherent graded `𝒪_S`-algebras in the
sheaf-level form `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` of Situation
01NN. A homomorphism `A ⟶ B` in the sense of
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom` is the same thing as a
homomorphism of their graded rings of global sections, given degreewise as `Γ(S, ⊤)`-linear maps
`Γ(A_n, ⊤) → Γ(B_n, ⊤)`, `n ≥ 0`, that are multiplicative and unital. This file proves that,
compatibly with identities and composition, and so that isomorphisms in every degree correspond
to families of bijections.

It also identifies, over an arbitrary base, the inverse image `A.pullback (𝟙 S)` of `A` along
the identity with `A`, as a homomorphism of graded algebras that is an isomorphism in every
degree, and hence identifies their global sections compatibly with multiplication and unit.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.id`: the identity.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.globalSectionsMap`: the
  `Γ(S, ⊤)`-linear map induced on global sections in degree `n`.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.ofGlobalSections`: over
  an affine base, the homomorphism determined by a multiplicative unital family of linear maps of
  global sections.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.globalSectionsEquiv`:
  over an affine base, the equivalence between homomorphisms and such families.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.invOfIsIso`: the inverse
  of a homomorphism that is an isomorphism in every degree.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.pullbackIdHom`: the
  canonical homomorphism `A.pullback (𝟙 S) ⟶ A`, an isomorphism in every degree, and
  `...SheafGradedAlgebraHom.pullbackIdGlobalSectionsEquiv`, the induced identification of global
  sections.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafBilinearMap.map_app_eq_of_isAffine`: over an
  affine scheme, morphisms of quasi-coherent modules intertwining two bilinear maps on global
  sections intertwine them on every open.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.ext_of_isAffine`: over an
  affine base a homomorphism is determined by its action on global sections in degrees `n ≥ 0`.
* `...SheafGradedAlgebraHom.ofGlobalSections_app_app_top`: `ofGlobalSections f` acts on global
  sections by `f`.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.globalSectionsEquiv_id`,
  `...globalSectionsEquiv_comp`: compatibility with identities and composition.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.forall_isIso_app_iff` and
  `...forall_isIso_app_globalSectionsEquiv_symm_iff`: isomorphisms in every degree correspond to
  families of bijections.

## Implementation notes

The degreewise morphisms come from the fullness and faithfulness of global sections on
quasi-coherent modules over an affine scheme,
`Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq` and
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top`. Multiplicativity on every open is the
only real content, and it is proved once for an arbitrary `SheafBilinearMap`, in three steps:
for a global section in the first variable both sides are morphisms of sheaves of modules in the
second variable (`Stacks.AlgebraicGeometry.ModuleLimits.homOfSections`) agreeing on global
sections; over a basic open `D(s)` the sections of a quasi-coherent module are a localization of
its global sections
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`), so a power of
`s` carries any section to a global one and is cancelled in the target; and an arbitrary open is
covered by basic opens.

Negative degrees carry no information, since the pieces vanish there: the degreewise morphisms
of `ofGlobalSections` are zero in negative degrees, and products with a negative-degree factor
vanish (`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.section_eq_zero_of_isZero`).

The identification along `𝟙 S` uses that `𝟙 S` is an open immersion: the inverse image along it
is compared with the restriction along it by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.restrictPullbackUnitalHom`, which is
multiplicative, and the restriction along the identity is the module itself by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorId`.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBridge.SheafBilinearMap

variable {S : Scheme.{u}} [IsAffine S] {M N P M' N' P' : S.Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent] [P'.IsQuasicoherent]
  (μ : SheafBilinearMap M N P) (μ' : SheafBilinearMap M' N' P')
  (φ : M ⟶ M') (ψ : N ⟶ N') (χ : P ⟶ P')

omit [M.IsQuasicoherent] in
/-- The compatibility on global sections propagates to a global section in the first variable
and an arbitrary local section in the second. -/
theorem map_app_res_eq_of_isAffine
    (h : ∀ (a : Γ(M, ⊤)) (b : Γ(N, ⊤)),
      χ.app ⊤ (μ.app ⊤ a b) = μ'.app ⊤ (φ.app ⊤ a) (ψ.app ⊤ b))
    (a : Γ(M, ⊤)) (U : S.Opens) (b : Γ(N, U)) :
    χ.app U (μ.app U (M.presheaf.map (homOfLE le_top).op a) b) =
      μ'.app U (M'.presheaf.map (homOfLE le_top).op (φ.app ⊤ a)) (ψ.app U b) := by
  let g₁ : N ⟶ P' := homOfSections
    (fun U b => χ.app U (μ.app U (M.presheaf.map (homOfLE le_top).op a) b))
    (fun U b b' => by rw [map_add, map_add])
    (fun U r b => by rw [μ.map_smul_right, Scheme.Modules.Hom.app_smul])
    (fun U V hUV b => by
      rw [Hom_app_presheaf_map, μ.naturality, presheaf_map_homOfLE_comp])
  let g₂ : N ⟶ P' := homOfSections
    (fun U b => μ'.app U (M'.presheaf.map (homOfLE le_top).op (φ.app ⊤ a)) (ψ.app U b))
    (fun U b b' => by rw [map_add, map_add])
    (fun U r b => by rw [Scheme.Modules.Hom.app_smul, μ'.map_smul_right])
    (fun U V hUV b => by
      rw [μ'.naturality, presheaf_map_homOfLE_comp, Hom_app_presheaf_map,
        Hom_app_presheaf_map ψ])
  have hid : ∀ (F : S.Modules) (x : Γ(F, ⊤)), F.presheaf.map (homOfLE le_top).op x = x :=
    fun F x => by
      rw [show (homOfLE (le_top : (⊤ : S.Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : S.Opens)) from rfl,
        F.presheaf.map_id]
      rfl
  have hg : g₁ = g₂ := hom_ext_of_app_top fun b => by
    simp only [g₁, g₂, homOfSections_app]
    rw [hid, hid]
    exact h a b
  have := congrArg (fun g : N ⟶ P' => g.app U b) hg
  simpa only [g₁, g₂, homOfSections_app] using this

/-- The compatibility on global sections propagates to the sections over a basic open: there the
sections of `M` are a localization of the global sections, and multiplication by a power of the
function is invertible on the sections of `P'`. -/
theorem map_app_basicOpen_eq_of_isAffine
    (h : ∀ (a : Γ(M, ⊤)) (b : Γ(N, ⊤)),
      χ.app ⊤ (μ.app ⊤ a b) = μ'.app ⊤ (φ.app ⊤ a) (ψ.app ⊤ b))
    (s : Γ(S, ⊤)) (a : Γ(M, S.basicOpen s)) (b : Γ(N, S.basicOpen s)) :
    χ.app _ (μ.app _ a b) = μ'.app _ (φ.app _ a) (ψ.app _ b) := by
  have hD : S.basicOpen s ≤ ⊤ := le_top
  let := moduleOfLE M hD
  let := moduleOfLE P' hD
  have hM : IsLocalizedModule.Away s (restrictₗ M hD) :=
    isLocalizedModule_restrictₗ M (isAffineOpen_top S) s rfl hD
  have hP : IsLocalizedModule.Away s (restrictₗ P' hD) :=
    isLocalizedModule_restrictₗ P' (isAffineOpen_top S) s rfl hD
  obtain ⟨⟨a₀, t⟩, ht⟩ := IsLocalizedModule.surj (Submonoid.powers s) (restrictₗ M hD) a
  have ht' : (S.presheaf.map (homOfLE hD).op).hom (t : Γ(S, ⊤)) • a =
      M.presheaf.map (homOfLE hD).op a₀ := ht
  have hinj : Function.Injective fun m : Γ(P', S.basicOpen s) =>
      (S.presheaf.map (homOfLE hD).op).hom (t : Γ(S, ⊤)) • m :=
    ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (restrictₗ P' hD) t)).injective
  apply hinj
  simp only
  rw [← Scheme.Modules.Hom.app_smul, ← μ.map_smul_left, ht',
    map_app_res_eq_of_isAffine μ μ' φ ψ χ h, Hom_app_presheaf_map φ, ← ht',
    Scheme.Modules.Hom.app_smul, μ'.map_smul_left]

/-- **Over an affine scheme, morphisms intertwining two bilinear maps on global sections intertwine
them on the sections over every open**, for quasi-coherent `M`, `N` and `P'`.

Over a basic open `D(s)` this is `map_app_basicOpen_eq_of_isAffine`; an arbitrary open is
covered by basic opens and `P'` is a sheaf. -/
theorem map_app_eq_of_isAffine
    (h : ∀ (a : Γ(M, ⊤)) (b : Γ(N, ⊤)),
      χ.app ⊤ (μ.app ⊤ a b) = μ'.app ⊤ (φ.app ⊤ a) (ψ.app ⊤ b))
    (U : S.Opens) (a : Γ(M, U)) (b : Γ(N, U)) :
    χ.app U (μ.app U a b) = μ'.app U (φ.app U a) (ψ.app U b) := by
  refine P'.isSheaf.section_ext (U := op U) ?_
  intro x hx
  obtain ⟨s, hsU, hxs⟩ := (isAffineOpen_top S).exists_basicOpen_le (V := U) ⟨x, hx⟩ trivial
  refine ⟨S.basicOpen s, hsU, hxs, ?_⟩
  rw [Hom_app_presheaf_map, μ.naturality, map_app_basicOpen_eq_of_isAffine μ μ' φ ψ χ h,
    μ'.naturality, Hom_app_presheaf_map φ, Hom_app_presheaf_map ψ]

end Stacks.AlgebraicGeometry.RelativeProjBridge.SheafBilinearMap

namespace Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (section_eq_zero_of_isZero)

variable {S : Scheme.{u}} {A B C : SheafGradedAlgebra S}

/-! ### Identity and global sections -/

/-- The identity homomorphism of a sheaf-level graded algebra: the identity in each degree. -/
def id (A : SheafGradedAlgebra S) : SheafGradedAlgebraHom A A where
  app _ := 𝟙 _
  app_mul _ _ _ _ _ := rfl
  app_one _ := rfl

/-- The components of the identity homomorphism are identities. -/
@[simp]
theorem id_app (A : SheafGradedAlgebra S) (n : ℤ) : (id A).app n = 𝟙 _ := rfl

/-- The `Γ(S, ⊤)`-linear map induced on the global sections of the degree-`n` pieces. -/
def globalSectionsMap (γ : SheafGradedAlgebraHom A B) (n : ℕ) :
    Γ(A.piece n, ⊤) →ₗ[Γ(S, ⊤)] Γ(B.piece n, ⊤) where
  toFun := (γ.app n).app ⊤
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul _

/-- The map on global sections is the action of the degreewise morphism over `⊤`. -/
@[simp]
theorem globalSectionsMap_apply (γ : SheafGradedAlgebraHom A B) (n : ℕ) (a : Γ(A.piece n, ⊤)) :
    γ.globalSectionsMap n a = (γ.app n).app ⊤ a := rfl

/-- The maps on global sections are multiplicative. -/
theorem globalSectionsMap_mul (γ : SheafGradedAlgebraHom A B) (i j : ℕ) (a : Γ(A.piece i, ⊤))
    (b : Γ(A.piece j, ⊤)) :
    γ.globalSectionsMap (i + j) ((A.mul i j).app ⊤ a b) =
      (B.mul i j).app ⊤ (γ.globalSectionsMap i a) (γ.globalSectionsMap j b) :=
  γ.app_mul i j ⊤ a b

/-- The map on global sections in degree `0` preserves the unit. -/
theorem globalSectionsMap_one (γ : SheafGradedAlgebraHom A B) :
    γ.globalSectionsMap 0 (A.one ⊤) = B.one ⊤ :=
  γ.app_one ⊤

/-- The identity homomorphism induces the identity on global sections. -/
@[simp]
theorem globalSectionsMap_id (A : SheafGradedAlgebra S) (n : ℕ) :
    (id A).globalSectionsMap n = LinearMap.id := rfl

/-- A composite homomorphism induces the composite on global sections. -/
@[simp]
theorem globalSectionsMap_comp (ψ : SheafGradedAlgebraHom B C) (φ : SheafGradedAlgebraHom A B)
    (n : ℕ) : (ψ.comp φ).globalSectionsMap n = ψ.globalSectionsMap n ∘ₗ φ.globalSectionsMap n :=
  rfl

/-- In negative degrees any two homomorphisms agree: the source piece is zero. -/
theorem app_eq_of_neg (γ γ' : SheafGradedAlgebraHom A B) {n : ℤ} (hn : n < 0) :
    γ.app n = γ'.app n :=
  (A.negative_isZero n hn).eq_of_src _ _

/-! ### Inverses -/

/-- The inverse of a homomorphism of graded algebras which is an isomorphism in every degree:
the inverse morphism in each degree. -/
def invOfIsIso (γ : SheafGradedAlgebraHom A B) (hγ : ∀ n : ℤ, IsIso (γ.app n)) :
    SheafGradedAlgebraHom B A where
  app n := inv (γ.app n)
  app_mul i j U a b := by
    apply (ConcreteCategory.bijective_of_isIso ((γ.app (i + j)).app U)).injective
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, IsIso.inv_hom_id,
      γ.app_mul, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Scheme.Modules.Hom.comp_app, ← Scheme.Modules.Hom.comp_app, IsIso.inv_hom_id,
      IsIso.inv_hom_id]
    rfl
  app_one U := by
    apply (ConcreteCategory.bijective_of_isIso ((γ.app 0).app U)).injective
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, IsIso.inv_hom_id,
      γ.app_one]
    rfl

/-- The components of `invOfIsIso` are the inverses of the components. -/
@[simp]
theorem invOfIsIso_app (γ : SheafGradedAlgebraHom A B) (hγ : ∀ n : ℤ, IsIso (γ.app n)) (n : ℤ) :
    (γ.invOfIsIso hγ).app n = inv (γ.app n) := rfl

/-- `invOfIsIso` is a right inverse. -/
theorem comp_invOfIsIso (γ : SheafGradedAlgebraHom A B) (hγ : ∀ n : ℤ, IsIso (γ.app n)) :
    γ.comp (γ.invOfIsIso hγ) = id B :=
  SheafGradedAlgebraHom.ext fun n => IsIso.inv_hom_id (γ.app n)

/-- `invOfIsIso` is a left inverse. -/
theorem invOfIsIso_comp (γ : SheafGradedAlgebraHom A B) (hγ : ∀ n : ℤ, IsIso (γ.app n)) :
    (γ.invOfIsIso hγ).comp γ = id A :=
  SheafGradedAlgebraHom.ext fun n => IsIso.hom_inv_id (γ.app n)

/-! ### Over an affine base -/

section Affine

variable [IsAffine S]

/-- **Over an affine scheme a homomorphism of graded algebras is determined by its action on
global sections in nonnegative degrees.** -/
theorem ext_of_isAffine {γ γ' : SheafGradedAlgebraHom A B}
    (h : ∀ (n : ℕ) (a : Γ(A.piece n, ⊤)), (γ.app n).app ⊤ a = (γ'.app n).app ⊤ a) :
    γ = γ' := by
  refine SheafGradedAlgebraHom.ext fun
    | .ofNat m => hom_ext_of_app_top (h m)
    | .negSucc m => app_eq_of_neg γ γ' (Int.negSucc_lt_zero m)

/-- The degreewise morphisms of `ofGlobalSections`: in degree `n ≥ 0` the unique morphism of
quasi-coherent modules inducing `f n` on global sections, and zero in negative degrees. -/
def pieceHomOfGlobalSections (f : ∀ n : ℕ, Γ(A.piece n, ⊤) →ₗ[Γ(S, ⊤)] Γ(B.piece n, ⊤)) :
    ∀ n : ℤ, A.piece n ⟶ B.piece n
  | .ofNat n => (exists_hom_app_top_eq (f n)).choose
  | .negSucc _ => 0

/-- The degreewise morphisms of `ofGlobalSections` act on global sections by the given maps. -/
theorem pieceHomOfGlobalSections_app_top
    (f : ∀ n : ℕ, Γ(A.piece n, ⊤) →ₗ[Γ(S, ⊤)] Γ(B.piece n, ⊤)) (n : ℕ) (a : Γ(A.piece n, ⊤)) :
    (pieceHomOfGlobalSections f n).app ⊤ a = f n a :=
  (exists_hom_app_top_eq (f n)).choose_spec a

/-- The degreewise morphisms of `ofGlobalSections` are multiplicative on every open. -/
theorem pieceHomOfGlobalSections_mul
    (f : ∀ n : ℕ, Γ(A.piece n, ⊤) →ₗ[Γ(S, ⊤)] Γ(B.piece n, ⊤))
    (hmul : ∀ (i j : ℕ) (a : Γ(A.piece i, ⊤)) (b : Γ(A.piece j, ⊤)),
      f (i + j) ((A.mul i j).app ⊤ a b) = (B.mul i j).app ⊤ (f i a) (f j b))
    (i j : ℤ) (U : S.Opens) (a : Γ(A.piece i, U)) (b : Γ(A.piece j, U)) :
    (pieceHomOfGlobalSections f (i + j)).app U ((A.mul i j).app U a b) =
      (B.mul i j).app U ((pieceHomOfGlobalSections f i).app U a)
        ((pieceHomOfGlobalSections f j).app U b) := by
  rcases i with i | i
  · rcases j with j | j
    · refine SheafBilinearMap.map_app_eq_of_isAffine (A.mul i j) (B.mul i j) _ _ _
        (fun a b => ?_) U a b
      exact (pieceHomOfGlobalSections_app_top f (i + j) _).trans ((hmul i j a b).trans
        (congrArg₂ (fun x y => (B.mul i j).app ⊤ x y) (pieceHomOfGlobalSections_app_top f i a).symm
          (pieceHomOfGlobalSections_app_top f j b).symm))
    · obtain rfl := section_eq_zero_of_isZero (A.negative_isZero _ (Int.negSucc_lt_zero j)) U b
      simp only [map_zero]
  · obtain rfl := section_eq_zero_of_isZero (A.negative_isZero _ (Int.negSucc_lt_zero i)) U a
    simp only [map_zero, AddMonoidHom.zero_apply]

/-- The degreewise morphisms of `ofGlobalSections` preserve the unit on every open. -/
theorem pieceHomOfGlobalSections_one
    (f : ∀ n : ℕ, Γ(A.piece n, ⊤) →ₗ[Γ(S, ⊤)] Γ(B.piece n, ⊤)) (hone : f 0 (A.one ⊤) = B.one ⊤)
    (U : S.Opens) : (pieceHomOfGlobalSections f 0).app U (A.one U) = B.one U := by
  rw [← A.one_res (le_top : U ≤ ⊤), ← B.one_res (le_top : U ≤ ⊤), ← Hom_app_presheaf_map]
  exact congrArg _ ((pieceHomOfGlobalSections_app_top f 0 _).trans hone)

/-- **A homomorphism of graded algebras over an affine scheme from a homomorphism of their
graded rings of global sections**: a family of `Γ(S, ⊤)`-linear maps in nonnegative degrees,
multiplicative and unital. -/
def ofGlobalSections (f : ∀ n : ℕ, Γ(A.piece n, ⊤) →ₗ[Γ(S, ⊤)] Γ(B.piece n, ⊤))
    (hmul : ∀ (i j : ℕ) (a : Γ(A.piece i, ⊤)) (b : Γ(A.piece j, ⊤)),
      f (i + j) ((A.mul i j).app ⊤ a b) = (B.mul i j).app ⊤ (f i a) (f j b))
    (hone : f 0 (A.one ⊤) = B.one ⊤) : SheafGradedAlgebraHom A B where
  app := pieceHomOfGlobalSections f
  app_mul := pieceHomOfGlobalSections_mul f hmul
  app_one := pieceHomOfGlobalSections_one f hone

/-- **`ofGlobalSections f` acts on global sections in degree `n ≥ 0` by `f n`.** -/
@[simp]
theorem ofGlobalSections_app_app_top
    (f : ∀ n : ℕ, Γ(A.piece n, ⊤) →ₗ[Γ(S, ⊤)] Γ(B.piece n, ⊤))
    (hmul : ∀ (i j : ℕ) (a : Γ(A.piece i, ⊤)) (b : Γ(A.piece j, ⊤)),
      f (i + j) ((A.mul i j).app ⊤ a b) = (B.mul i j).app ⊤ (f i a) (f j b))
    (hone : f 0 (A.one ⊤) = B.one ⊤) (n : ℕ) (a : Γ(A.piece n, ⊤)) :
    ((ofGlobalSections f hmul hone).app n).app ⊤ a = f n a :=
  pieceHomOfGlobalSections_app_top f n a

/-- The maps on global sections of `ofGlobalSections f` are the members of `f`. -/
@[simp]
theorem globalSectionsMap_ofGlobalSections
    (f : ∀ n : ℕ, Γ(A.piece n, ⊤) →ₗ[Γ(S, ⊤)] Γ(B.piece n, ⊤))
    (hmul : ∀ (i j : ℕ) (a : Γ(A.piece i, ⊤)) (b : Γ(A.piece j, ⊤)),
      f (i + j) ((A.mul i j).app ⊤ a b) = (B.mul i j).app ⊤ (f i a) (f j b))
    (hone : f 0 (A.one ⊤) = B.one ⊤) (n : ℕ) :
    (ofGlobalSections f hmul hone).globalSectionsMap n = f n :=
  LinearMap.ext (pieceHomOfGlobalSections_app_top f n)

/-- **Over an affine scheme, homomorphisms of quasi-coherent graded algebras are homomorphisms of
their graded rings of global sections**, given degreewise as multiplicative and unital
`Γ(S, ⊤)`-linear maps. -/
def globalSectionsEquiv :
    SheafGradedAlgebraHom A B ≃
      {f : ∀ n : ℕ, Γ(A.piece n, ⊤) →ₗ[Γ(S, ⊤)] Γ(B.piece n, ⊤) //
        (∀ (i j : ℕ) (a : Γ(A.piece i, ⊤)) (b : Γ(A.piece j, ⊤)),
          f (i + j) ((A.mul i j).app ⊤ a b) = (B.mul i j).app ⊤ (f i a) (f j b)) ∧
        f 0 (A.one ⊤) = B.one ⊤} where
  toFun γ := ⟨γ.globalSectionsMap, γ.globalSectionsMap_mul, γ.globalSectionsMap_one⟩
  invFun f := ofGlobalSections f.1 f.2.1 f.2.2
  left_inv _ := ext_of_isAffine fun n a => ofGlobalSections_app_app_top _ _ _ n a
  right_inv _ := Subtype.ext (funext fun n => globalSectionsMap_ofGlobalSections _ _ _ n)

/-- `globalSectionsEquiv` sends a homomorphism to its family of maps of global sections. -/
@[simp]
theorem globalSectionsEquiv_apply_coe (γ : SheafGradedAlgebraHom A B) :
    (globalSectionsEquiv γ).1 = γ.globalSectionsMap := rfl

/-- The inverse of `globalSectionsEquiv` is `ofGlobalSections`. -/
theorem globalSectionsEquiv_symm_apply
    (f : {f : ∀ n : ℕ, Γ(A.piece n, ⊤) →ₗ[Γ(S, ⊤)] Γ(B.piece n, ⊤) //
        (∀ (i j : ℕ) (a : Γ(A.piece i, ⊤)) (b : Γ(A.piece j, ⊤)),
          f (i + j) ((A.mul i j).app ⊤ a b) = (B.mul i j).app ⊤ (f i a) (f j b)) ∧
        f 0 (A.one ⊤) = B.one ⊤}) :
    globalSectionsEquiv.symm f = ofGlobalSections f.1 f.2.1 f.2.2 := rfl

/-- `globalSectionsEquiv` sends the identity to the family of identities. -/
@[simp]
theorem globalSectionsEquiv_id : (globalSectionsEquiv (id A)).1 = fun _ => LinearMap.id := rfl

/-- `globalSectionsEquiv` sends a composite to the degreewise composite. -/
@[simp]
theorem globalSectionsEquiv_comp (ψ : SheafGradedAlgebraHom B C) (φ : SheafGradedAlgebraHom A B) :
    (globalSectionsEquiv (ψ.comp φ)).1 =
      fun n => (globalSectionsEquiv ψ).1 n ∘ₗ (globalSectionsEquiv φ).1 n := rfl

/-- **Over an affine scheme a homomorphism of quasi-coherent graded algebras is an isomorphism in
degree `n` if and only if it is bijective on global sections in degree `n`.** -/
theorem isIso_app_iff_bijective (γ : SheafGradedAlgebraHom A B) (n : ℕ) :
    IsIso (γ.app n) ↔ Function.Bijective (γ.globalSectionsMap n) := by
  constructor
  · intro _
    exact ConcreteCategory.bijective_of_isIso ((γ.app n).app ⊤)
  · intro h
    exact Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _
      ((ConcreteCategory.isIso_iff_bijective _).mpr h)

/-- **Isomorphisms correspond.** Over an affine scheme a homomorphism of quasi-coherent graded
algebras is an isomorphism in every degree if and only if the corresponding family of maps of
global sections is bijective in every nonnegative degree. -/
theorem forall_isIso_app_iff (γ : SheafGradedAlgebraHom A B) :
    (∀ n : ℤ, IsIso (γ.app n)) ↔ ∀ n : ℕ, Function.Bijective ((globalSectionsEquiv γ).1 n) := by
  refine ⟨fun h n => (isIso_app_iff_bijective γ n).mp (h n), fun h => ?_⟩
  rintro (m | m)
  · exact (isIso_app_iff_bijective γ m).mpr (h m)
  · have hn := Int.negSucc_lt_zero m
    exact ⟨⟨0, (A.negative_isZero _ hn).eq_of_src _ _, (B.negative_isZero _ hn).eq_of_src _ _⟩⟩

/-- The homomorphism attached to a family of maps of global sections is an isomorphism in every
degree if and only if every member of the family is bijective. -/
theorem forall_isIso_app_globalSectionsEquiv_symm_iff
    (f : {f : ∀ n : ℕ, Γ(A.piece n, ⊤) →ₗ[Γ(S, ⊤)] Γ(B.piece n, ⊤) //
        (∀ (i j : ℕ) (a : Γ(A.piece i, ⊤)) (b : Γ(A.piece j, ⊤)),
          f (i + j) ((A.mul i j).app ⊤ a b) = (B.mul i j).app ⊤ (f i a) (f j b)) ∧
        f 0 (A.one ⊤) = B.one ⊤}) :
    (∀ n : ℤ, IsIso ((globalSectionsEquiv.symm f).app n)) ↔
      ∀ n : ℕ, Function.Bijective (f.1 n) := by
  rw [forall_isIso_app_iff, Equiv.apply_symm_apply]

end Affine

/-! ### The inverse image along the identity -/

section PullbackId

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (restrictPullbackUnitalHom
  restrictPullbackUnitalHom_app)

variable (A : SheafGradedAlgebra S)

/-- The degree-`n` component of `pullbackIdHom`: the inverse of the canonical isomorphism
`restriction ≅ inverse image` along the open immersion `𝟙 S`, followed by the identification of
the restriction along the identity with the module itself. -/
def pullbackIdPieceIso (n : ℤ) : (A.pullback (𝟙 S)).piece n ≅ A.piece n :=
  ((Scheme.Modules.restrictFunctorIsoPullback (𝟙 S)).app (A.piece n)).symm ≪≫
    Scheme.Modules.restrictFunctorId.app (A.piece n)

/-- `pullbackIdPieceIso` on sections over `U`: the comparison `restrictPullbackUnitalHom` of
graded algebras, landing in the sections of `A` over `(𝟙 S) ''ᵁ U ⊇ U`, followed by restriction
to `U`. -/
theorem pullbackIdPieceIso_hom_app_apply (n : ℤ) (U : S.Opens) (hU : U ≤ (𝟙 S) ''ᵁ U)
    (x : Γ((A.pullback (𝟙 S)).piece n, U)) :
    (pullbackIdPieceIso A n).hom.app U x =
      (A.piece n).presheaf.map (homOfLE hU).op
        (((restrictPullbackUnitalHom A (𝟙 S)).app n).val.app (op U) x) := by
  have h := restrictPullbackUnitalHom_app A (𝟙 S) n
  rw [h]
  rfl

/-- **The canonical homomorphism from the inverse image of `A` along the identity to `A`**,
with components the homomorphisms of `pullbackIdPieceIso`. It is multiplicative because the
comparison of the inverse image with the restriction is (`restrictPullbackUnitalHom_app`), and the
multiplication of `A` commutes with restriction. -/
def pullbackIdHom : SheafGradedAlgebraHom (A.pullback (𝟙 S)) A where
  app n := (pullbackIdPieceIso A n).hom
  app_mul i j U a b := by
    have hU : U ≤ (𝟙 S) ''ᵁ U := (show U = (𝟙 S) ''ᵁ U by simp).le
    rw [pullbackIdPieceIso_hom_app_apply A _ U hU, pullbackIdPieceIso_hom_app_apply A _ U hU,
      pullbackIdPieceIso_hom_app_apply A _ U hU]
    have hmul := (restrictPullbackUnitalHom A (𝟙 S)).map_mul i j (op U) a b
    refine (congrArg _ hmul).trans ?_
    exact (A.mul i j).naturality hU _ _
  app_one U := by
    have hU : U ≤ (𝟙 S) ''ᵁ U := (show U = (𝟙 S) ''ᵁ U by simp).le
    rw [pullbackIdPieceIso_hom_app_apply A _ U hU]
    have hone := (restrictPullbackUnitalHom A (𝟙 S)).map_one (op U)
    refine (congrArg _ hone).trans ?_
    exact A.one_res hU

/-- The components of `pullbackIdHom` are the isomorphisms `pullbackIdPieceIso`. -/
@[simp]
theorem pullbackIdHom_app (n : ℤ) : (pullbackIdHom A).app n = (pullbackIdPieceIso A n).hom :=
  rfl

/-- Every degreewise component of `pullbackIdHom` is an isomorphism. -/
instance isIso_pullbackIdHom_app (n : ℤ) : IsIso ((pullbackIdHom A).app n) :=
  (pullbackIdPieceIso A n).isIso_hom

/-- **The global sections of the inverse image of `A` along the identity are those of `A`**:
in each degree a `Γ(S, ⊤)`-linear bijection, induced by `pullbackIdHom`, so compatible with the
multiplication (`pullbackIdGlobalSectionsEquiv_mul`) and the unit
(`pullbackIdGlobalSectionsEquiv_one`). -/
def pullbackIdGlobalSectionsEquiv (n : ℕ) :
    Γ((A.pullback (𝟙 S)).piece n, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(A.piece n, ⊤) :=
  LinearEquiv.ofBijective ((pullbackIdHom A).globalSectionsMap n)
    (ConcreteCategory.bijective_of_isIso (((pullbackIdHom A).app n).app ⊤))

/-- `pullbackIdGlobalSectionsEquiv` is the action of `pullbackIdHom` on global sections. -/
@[simp]
theorem pullbackIdGlobalSectionsEquiv_apply (n : ℕ) (a : Γ((A.pullback (𝟙 S)).piece n, ⊤)) :
    pullbackIdGlobalSectionsEquiv A n a = ((pullbackIdHom A).app n).app ⊤ a := rfl

/-- `pullbackIdGlobalSectionsEquiv`, as a linear map, is the map on global sections induced by
`pullbackIdHom`; so it corresponds to `pullbackIdHom` under `globalSectionsEquiv`. -/
theorem pullbackIdGlobalSectionsEquiv_toLinearMap (n : ℕ) :
    (pullbackIdGlobalSectionsEquiv A n).toLinearMap = (pullbackIdHom A).globalSectionsMap n :=
  rfl

/-- The identification of global sections of `pullbackIdGlobalSectionsEquiv` is
multiplicative. -/
theorem pullbackIdGlobalSectionsEquiv_mul (i j : ℕ) (a : Γ((A.pullback (𝟙 S)).piece i, ⊤))
    (b : Γ((A.pullback (𝟙 S)).piece j, ⊤)) :
    pullbackIdGlobalSectionsEquiv A (i + j) (((A.pullback (𝟙 S)).mul i j).app ⊤ a b) =
      (A.mul i j).app ⊤ (pullbackIdGlobalSectionsEquiv A i a)
        (pullbackIdGlobalSectionsEquiv A j b) :=
  (pullbackIdHom A).globalSectionsMap_mul i j a b

/-- The identification of global sections of `pullbackIdGlobalSectionsEquiv` preserves the
unit. -/
theorem pullbackIdGlobalSectionsEquiv_one :
    pullbackIdGlobalSectionsEquiv A 0 ((A.pullback (𝟙 S)).one ⊤) = A.one ⊤ :=
  (pullbackIdHom A).globalSectionsMap_one

end PullbackId

end Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom

end
