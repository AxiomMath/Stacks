module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSiteCanonical
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.CategoryTheory.PullbackCancelMono

/-!
# Infinitesimal neighbourhoods of a representable thickening of fppf sheaves

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an fppf sheaf over `S` and let
`i : Z ⟶ X` be a representable thickening, for instance the inclusion of the reduction of a
formal algebraic space. For a section `ξ` of `X` over an object `T` of the site the base change
of `i` along `ξ` is a closed subscheme of `T`; write `I_ξ` for its ideal sheaf. The `n`th
infinitesimal neighbourhood `X_n ⊂ X` of `Z` is the subfunctor of the sections `ξ` with
`I_ξ ^ (n + 1) = 0`. This is the subfunctor of the proof of Stacks 0GHM, there indexed from one.

## Main definitions

* `AlgebraicGeometry.FormalSpace.pullbackIdeal`: the ideal sheaf `I_ξ`.
* `AlgebraicGeometry.FormalSpace.neighbourhood`: the subfunctor `X_n`, and
  `AlgebraicGeometry.FormalSpace.neighbourhoodSheaf`,
  `AlgebraicGeometry.FormalSpace.neighbourhoodι` the fppf sheaf it is and its inclusion into `X`.
* `AlgebraicGeometry.FormalSpace.neighbourhoodDiagram`: the system `X_0 ⟶ X_1 ⟶ ⋯`.

## Main results

* `AlgebraicGeometry.FormalSpace.ker_eq_comap_pullbackIdeal`: the ideal sheaf of a represented
  base change of `i` along a restriction of `ξ` is the inverse image of `I_ξ`.
* `AlgebraicGeometry.FormalSpace.isSheaf_neighbourhood`: `X_n` is an fppf sheaf.
* `AlgebraicGeometry.FormalSpace.isPullback_neighbourhood`: the base change of `X_n ⊂ X` along
  `ξ` is the closed subscheme of `T` cut out by `I_ξ ^ (n + 1)`.
* `AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_neighbourhoodι`: `X_n ⊂ X` is a
  representable thickening.
* `AlgebraicGeometry.FormalSpace.hasSchemePropertyULift_isNthOrderThickening_neighbourhoodDiagram`:
  each `X_n ⊂ X_m` is representable, and an `m`th-order thickening on every represented base
  change.
* `AlgebraicGeometry.FormalSpace.ker_pow_eq_ker_neighbourhoodDiagram`: on every represented base
  change of `X_m`, the ideal sheaf of `X_n` is the `(n + 1)`st power of the ideal sheaf of `X_0`.
* `AlgebraicGeometry.FormalSpace.neighbourhood_zero_eq_range`: `X_0` is the image of `i`, and
  `AlgebraicGeometry.FormalSpace.IsReduction.neighbourhoodι_zero`: if `i` is a reduction of `X`
  then so is `X_0 ⊂ X`.

## Implementation notes

Everything is reduced to one computation,
`AlgebraicGeometry.FormalSpace.ker_eq_comap_pullbackIdeal`: two cartesian squares over `i`
paste, the universe-lifted Yoneda embedding reflects the resulting cartesian square of
representables, the forgetful functor to schemes preserves it, and Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.ker_fst_of_isClosedImmersion` identifies the kernel of a
base change of a closed immersion. Together with the Galois connection between inverse and direct
image of ideal sheaves this makes membership in `X_n` of a restriction `ξ ∘ g` the inequality
`I_ξ ^ (n + 1) ≤ ker g`, which is factorization of `g` through the closed subscheme
`V(I_ξ ^ (n + 1))`.

That subscheme is an object of the site (`AlgebraicGeometry.FormalSpace.siteSubscheme`), a closed
immersion not increasing the size of a scheme; the sheaf property of `X_n` is then the statement
that a monomorphism of objects through which every member of a covering sieve factors is an
isomorphism, the representable sheaves being sheaves.

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Closed subschemes of objects of the site -/

section SiteSubscheme

variable (T : BigFppfOver B S hS) (J : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData)

/-- A closed subscheme of the underlying scheme of an object of the big fppf site is contained
in the site, a closed immersion not increasing the size of a scheme. -/
theorem contains_subscheme : B.Contains J.subscheme :=
  Scheme.size_lt_of_isClosedImmersion J.subschemeι T.left.property

/-- The closed immersion cutting out a closed subscheme of an object of the site, read in the
site's category of schemes. -/
def siteSubschemeHom : B.obj (contains_subscheme T J) ⟶ T.left :=
  B.inclusion.preimage
    (show B.inclusion.obj (B.obj (contains_subscheme T J)) ⟶ B.inclusion.obj T.left from
      J.subschemeι)

/-- The closed subscheme `V(J)` of an object `T` of the big fppf site, as an object of the site
with the structure morphism inherited from `T`. -/
def siteSubscheme : BigFppfOver B S hS :=
  Over.mk (siteSubschemeHom T J ≫ T.hom)

/-- The inclusion of the closed subscheme `V(J)` into `T`, as a morphism of the site. -/
def siteSubschemeι : siteSubscheme T J ⟶ T :=
  Over.homMk (siteSubschemeHom T J)

/-- The underlying morphism of schemes of the inclusion of `V(J)` into `T` is `J.subschemeι`. -/
@[simp]
theorem toScheme_map_siteSubschemeι :
    (BigFppfOver.toScheme B S hS).map (siteSubschemeι T J) = J.subschemeι :=
  B.inclusion.map_preimage _

/-- The image of `siteSubschemeHom T J` in the category of schemes is `J.subschemeι`. -/
theorem inclusion_map_siteSubschemeHom :
    B.inclusion.map (siteSubschemeHom T J) = J.subschemeι :=
  B.inclusion.map_preimage _

/-- The underlying morphism of schemes of the inclusion of `V(J)` into `T` is a closed
immersion. -/
instance : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (siteSubschemeι T J)) := by
  have h : IsClosedImmersion J.subschemeι := inferInstance
  rw [toScheme_map_siteSubschemeι]
  exact h

/-- The inclusion of `V(J)` into `T` is a monomorphism of the site. -/
instance : Mono (siteSubschemeι T J) :=
  (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance

/-- The kernel of the inclusion of `V(J)` into `T` is `J`. -/
theorem ker_toScheme_map_siteSubschemeι :
    ((BigFppfOver.toScheme B S hS).map (siteSubschemeι T J)).ker = J := by
  rw [toScheme_map_siteSubschemeι]
  exact J.ker_subschemeι

variable {T J}

/-- The underlying morphism of schemes of the factorization through `V(J)` of a morphism into
`T` whose kernel contains `J`. -/
def siteSubschemeLiftHom {U : BigFppfOver B S hS} (g : U ⟶ T)
    (hg : J ≤ ((BigFppfOver.toScheme B S hS).map g).ker) :
    U.left ⟶ B.obj (contains_subscheme T J) :=
  B.inclusion.preimage (X := U.left) (Y := B.obj (contains_subscheme T J))
    (IsClosedImmersion.lift J.subschemeι ((BigFppfOver.toScheme B S hS).map g)
      (by rwa [Scheme.IdealSheafData.ker_subschemeι]))

/-- The factorization `siteSubschemeLiftHom g hg` composed with the inclusion of `V(J)` is the
underlying morphism of `g`. -/
theorem siteSubschemeLiftHom_comp {U : BigFppfOver B S hS} (g : U ⟶ T)
    (hg : J ≤ ((BigFppfOver.toScheme B S hS).map g).ker) :
    siteSubschemeLiftHom g hg ≫ siteSubschemeHom T J = g.left := by
  apply B.inclusion.map_injective
  rw [CategoryTheory.Functor.map_comp, siteSubschemeLiftHom, CategoryTheory.Functor.map_preimage,
    inclusion_map_siteSubschemeHom]
  exact IsClosedImmersion.lift_fac _ _ _

/-- A morphism of the site into `T` whose kernel contains `J` factors through `V(J)`. -/
def siteSubschemeLift {U : BigFppfOver B S hS} (g : U ⟶ T)
    (hg : J ≤ ((BigFppfOver.toScheme B S hS).map g).ker) : U ⟶ siteSubscheme T J :=
  Over.homMk (siteSubschemeLiftHom g hg) (by
    change siteSubschemeLiftHom g hg ≫ siteSubschemeHom T J ≫ T.hom = U.hom
    rw [← Category.assoc, siteSubschemeLiftHom_comp, Over.w g])

/-- The factorization `siteSubschemeLift g hg` composed with the inclusion of `V(J)` is `g`. -/
@[reassoc (attr := simp)]
theorem siteSubschemeLift_ι {U : BigFppfOver B S hS} (g : U ⟶ T)
    (hg : J ≤ ((BigFppfOver.toScheme B S hS).map g).ker) :
    siteSubschemeLift g hg ≫ siteSubschemeι T J = g := by
  ext1
  exact siteSubschemeLiftHom_comp g hg

/-- A morphism of the site into `T` factors through `V(J)` exactly when its kernel contains
`J`. -/
theorem exists_comp_siteSubschemeι_iff {U : BigFppfOver B S hS} (g : U ⟶ T) :
    (∃ h : U ⟶ siteSubscheme T J, h ≫ siteSubschemeι T J = g) ↔
      J ≤ ((BigFppfOver.toScheme B S hS).map g).ker := by
  refine ⟨?_, fun hg ↦ ⟨siteSubschemeLift g hg, siteSubschemeLift_ι g hg⟩⟩
  rintro ⟨h, rfl⟩
  rw [CategoryTheory.Functor.map_comp]
  refine le_trans ?_ (Scheme.Hom.le_ker_comp _ _)
  rw [ker_toScheme_map_siteSubschemeι]

/-- **An ideal sheaf killed by every member of a covering sieve vanishes.** If every member of a
covering sieve of `T` has kernel containing `J`, then `J = 0`: the monomorphism `V(J) ⟶ T` is
locally surjective on represented sheaves, hence an isomorphism. -/
theorem eq_bot_of_le_ker_of_mem {R : Sieve T} (hR : R ∈ BigFppfOver.topology B S hS T)
    (hJ : ∀ ⦃U : BigFppfOver B S hS⦄ (g : U ⟶ T), R g →
      J ≤ ((BigFppfOver.toScheme B S hS).map g).ker) : J = ⊥ := by
  let JT := BigFppfOver.topology B S hS
  let Y := GrothendieckTopology.uliftYoneda.{u + 1} JT
  let m := siteSubschemeι T J
  have : Mono (Y.map m) := by
    apply (sheafToPresheaf JT (Type (u + 1))).mono_of_mono_map
    show Mono (uliftYoneda.{u + 1}.map m)
    infer_instance
  have hs : Presheaf.IsLocallySurjective JT (uliftYoneda.{u + 1}.map m) := by
    constructor
    intro V h
    refine JT.superset_covering ?_ (JT.pullback_stable h.down hR)
    intro W f hf
    refine ⟨ULift.up (siteSubschemeLift (f ≫ h.down) (hJ _ hf)), ?_⟩
    show ULift.up (siteSubschemeLift (f ≫ h.down) (hJ _ hf) ≫ m) = ULift.up (f ≫ h.down)
    rw [siteSubschemeLift_ι]
  have : Sheaf.IsLocallySurjective (Y.map m) := hs
  have : Epi (Y.map m) := inferInstance
  have : IsIso (Y.map m) := isIso_of_mono_of_epi _
  have : IsIso m := isIso_of_reflects_iso _ Y
  have hiso : IsIso ((BigFppfOver.toScheme B S hS).map m) :=
    CategoryTheory.Functor.map_isIso _ _
  rw [toScheme_map_siteSubschemeι] at hiso
  exact (Scheme.isIso_subschemeι_iff_eq_bot J).mp hiso

end SiteSubscheme

/-! ### Cartesian squares of subfunctors -/

/-- A commuting square whose right edge is the inclusion of a subfunctor and whose left edge is
a monomorphism is cartesian as soon as every section of the lower left corner that is sent into
the subfunctor comes from the upper left corner. -/
theorem isPullback_subfunctorι_of_forall {C : Type*} [Category C] {F U V : C ⥤ Type (u + 1)}
    (G : Subfunctor F) (r : U ⟶ V) (hr : Mono r) (c : V ⟶ F) (l : U ⟶ G.toFunctor)
    (hl : l ≫ G.ι = r ≫ c)
    (h : ∀ (T : C) (y : V.obj T), c.app T y ∈ G.obj T → ∃ x, r.app T x = y) :
    IsPullback l r G.ι c := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk (f := G.ι) (g := c) l r hl) ?_
  apply evaluationJointlyReflectsLimits
  intro T
  refine (PullbackCone.isLimitMapConeEquiv _ ((evaluation _ _).obj T)).symm ?_
  refine ((Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩).isLimit
  · exact congr_app hl T
  · rintro a b ⟨-, hab⟩
    exact ((NatTrans.mono_iff_mono_app r).1 hr T |> (mono_iff_injective _).1) hab
  · intro x y hxy
    have hy : c.app T y ∈ G.obj T := by
      have : (G.ι.app T) x = c.app T y := hxy
      rw [← this]
      exact x.2
    obtain ⟨z, hz⟩ := h T y hy
    refine ⟨z, ?_, hz⟩
    apply Subtype.ext
    show (l ≫ G.ι).app T z = x.1
    rw [hl]
    show c.app T (r.app T z) = x.1
    rw [hz]
    exact hxy.symm

/-- `CategoryTheory.isPullback_comp_mono` with the composite right edge named. -/
theorem isPullback_comp_mono_of_eq {C : Type*} [Category C] {P X Y Z Z' : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (i : Z ⟶ Z') [Mono i]
    {f' : X ⟶ Z'} (e : f ≫ i = f') : IsPullback fst snd f' (g ≫ i) :=
  e ▸ isPullback_comp_mono h i

/-- `CategoryTheory.isPullback_of_comp_mono` with the composite right edge named. -/
theorem isPullback_of_comp_mono_of_eq {C : Type*} [Category C] {P A A' Z W : C} {f : P ⟶ A}
    {g : P ⟶ A'} {x : A ⟶ W} {y : A' ⟶ W} (m : W ⟶ Z) [Mono m] {x' : A ⟶ Z}
    (e : x ≫ m = x') (hsq : IsPullback f g x' (y ≫ m)) : IsPullback f g x y :=
  isPullback_of_comp_mono m (e ▸ hsq)

/-! ### The ideal sheaf of a base change of a representable thickening -/

section Neighbourhood

variable {X : FppfSheaf B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {i : Z ⟶ X.obj}
  (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i)

/-- The ideal sheaf on `T` of the base change of the representable thickening `i` along a section
`ξ` of `X` over `T`: the kernel of the represented base change of `i` along `ξ`. -/
def pullbackIdeal {T : BigFppfOver B S hS} (ξ : X.obj.obj (op T)) :
    ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData :=
  ((BigFppfOver.toScheme B S hS).map (hi.rep.snd (uliftYonedaEquiv.{u + 1}.symm ξ))).ker

/-- The scheme map of the represented base change of `i` along a section is a thickening. -/
theorem isThickening_rep_snd {T : BigFppfOver B S hS}
    (g : uliftYoneda.{u + 1}.obj T ⟶ X.obj) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)) :=
  hi.property g _ _ (hi.rep.isPullback g)

/-- The scheme map of the represented base change of `i` along a section is a closed immersion. -/
instance isClosedImmersion_rep_snd {T : BigFppfOver B S hS}
    (g : uliftYoneda.{u + 1}.obj T ⟶ X.obj) :
    IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)) :=
  (isThickening_rep_snd hi g).1

/-- **The ideal sheaf of a base change along a restriction.** For a section `ξ` of `X` over `T`,
a morphism `g : T' ⟶ T` and any cartesian square exhibiting `snd : b ⟶ T'` as the base change of
`i` along the restriction of `ξ` to `T'`, the kernel of `snd` is the inverse image of `I_ξ`. -/
theorem ker_eq_comap_pullbackIdeal {T T' : BigFppfOver B S hS} (ξ : X.obj.obj (op T))
    (g : T' ⟶ T) {k : uliftYoneda.{u + 1}.obj T' ⟶ X.obj}
    (hk : k = uliftYoneda.{u + 1}.map g ≫ uliftYonedaEquiv.{u + 1}.symm ξ)
    {b : BigFppfOver B S hS} {fst : uliftYoneda.{u + 1}.obj b ⟶ Z} {snd : b ⟶ T'}
    (sq : IsPullback fst (uliftYoneda.{u + 1}.map snd) i k) :
    ((BigFppfOver.toScheme B S hS).map snd).ker =
      (pullbackIdeal hi ξ).comap ((BigFppfOver.toScheme B S hS).map g) := by
  subst hk
  let ξ' := uliftYonedaEquiv.{u + 1}.symm ξ
  let G := BigFppfOver.toScheme B S hS
  have := isClosedImmersion_rep_snd hi ξ'
  have sq0 := hi.rep.isPullback ξ'
  let l := sq0.lift fst (uliftYoneda.{u + 1}.map snd ≫ uliftYoneda.{u + 1}.map g)
    (by rw [sq.w, Category.assoc])
  have hl1 : l ≫ hi.rep.fst ξ' = fst := sq0.lift_fst _ _ _
  have hl2 : l ≫ uliftYoneda.{u + 1}.map (hi.rep.snd ξ') =
      uliftYoneda.{u + 1}.map snd ≫ uliftYoneda.{u + 1}.map g := sq0.lift_snd _ _ _
  have hleft : IsPullback l (uliftYoneda.{u + 1}.map snd)
      (uliftYoneda.{u + 1}.map (hi.rep.snd ξ')) (uliftYoneda.{u + 1}.map g) :=
    IsPullback.of_right (by rwa [hl1]) hl2 sq0
  let l' : b ⟶ hi.rep.pullback ξ' := uliftYoneda.{u + 1}.preimage l
  have hl' : uliftYoneda.{u + 1}.map l' = l := uliftYoneda.{u + 1}.map_preimage l
  rw [← hl'] at hleft
  have hsite : IsPullback l' snd (hi.rep.snd ξ') g :=
    IsPullback.of_map_of_faithful uliftYoneda.{u + 1} hleft
  rw [← (hsite.map G).flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rfl

/-- The ideal sheaf of a base change along a restriction of a section is the inverse image of
the ideal sheaf of the base change along the section. -/
theorem pullbackIdeal_map {T T' : BigFppfOver B S hS} (ξ : X.obj.obj (op T)) (g : T' ⟶ T) :
    pullbackIdeal hi (X.obj.map g.op ξ) =
      (pullbackIdeal hi ξ).comap ((BigFppfOver.toScheme B S hS).map g) :=
  ker_eq_comap_pullbackIdeal hi ξ g (uliftYonedaEquiv_symm_map g.op ξ)
    (hi.rep.isPullback (uliftYonedaEquiv.{u + 1}.symm (X.obj.map g.op ξ)))

/-- Any represented base change of `i` along a section `ξ` has kernel `I_ξ`. -/
theorem ker_eq_pullbackIdeal {T : BigFppfOver B S hS} (ξ : X.obj.obj (op T))
    {b : BigFppfOver B S hS} {fst : uliftYoneda.{u + 1}.obj b ⟶ Z} {snd : b ⟶ T}
    (sq : IsPullback fst (uliftYoneda.{u + 1}.map snd) i
      (uliftYonedaEquiv.{u + 1}.symm ξ)) :
    ((BigFppfOver.toScheme B S hS).map snd).ker = pullbackIdeal hi ξ := by
  rw [ker_eq_comap_pullbackIdeal hi ξ (𝟙 T)
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp]) sq,
    CategoryTheory.Functor.map_id, Scheme.IdealSheafData.comap_id]

/-! ### The infinitesimal neighbourhoods -/

/-- **The `n`th infinitesimal neighbourhood of `Z` in `X`**: the sections `ξ` of `X` whose ideal
sheaf `I_ξ` has vanishing `(n + 1)`st power. -/
def neighbourhood (n : ℕ) : Subfunctor X.obj where
  obj T := {ξ | pullbackIdeal hi ξ ^ (n + 1) = ⊥}
  map {T T'} g ξ hξ := by
    change pullbackIdeal hi (X.obj.map g.unop.op ξ) ^ (n + 1) = ⊥
    rw [pullbackIdeal_map hi ξ g.unop, ← Stacks.IdealSheaf.comap_pow]
    rw [hξ, Scheme.IdealSheafData.comap_bot]

/-- A section `ξ` lies in `X_n` exactly when `I_ξ ^ (n + 1) = 0`. -/
theorem mem_neighbourhood_iff {n : ℕ} {T : BigFppfOver B S hS} (ξ : X.obj.obj (op T)) :
    ξ ∈ (neighbourhood hi n).obj (op T) ↔ pullbackIdeal hi ξ ^ (n + 1) = ⊥ := Iff.rfl

/-- A restriction `ξ ∘ g` of a section lies in `X_n` exactly when the kernel of `g` contains
`I_ξ ^ (n + 1)`. -/
theorem map_mem_neighbourhood_iff {n : ℕ} {T T' : BigFppfOver B S hS} (ξ : X.obj.obj (op T))
    (g : T' ⟶ T) :
    X.obj.map g.op ξ ∈ (neighbourhood hi n).obj (op T') ↔
      pullbackIdeal hi ξ ^ (n + 1) ≤ ((BigFppfOver.toScheme B S hS).map g).ker := by
  rw [mem_neighbourhood_iff, pullbackIdeal_map, ← Stacks.IdealSheaf.comap_pow, ← le_bot_iff,
    ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_bot]

/-- If a power of an ideal sheaf vanishes, so does every higher power. -/
private theorem pow_eq_bot_of_le {Y : Scheme.{u}} {I : Y.IdealSheafData} {a b : ℕ} (h : a ≤ b)
    (hI : I ^ a = ⊥) : I ^ b = ⊥ :=
  le_bot_iff.mp (hI ▸ pow_le_pow_of_le_one bot_le le_top h)

/-- The infinitesimal neighbourhoods increase with `n`: `X_n ⊆ X_m` for `n ≤ m`. -/
theorem neighbourhood_mono {n m : ℕ} (h : n ≤ m) : neighbourhood hi n ≤ neighbourhood hi m :=
  fun _ _ hξ ↦ pow_eq_bot_of_le (Nat.succ_le_succ h) hξ

/-- The `n`th infinitesimal neighbourhood is an fppf sheaf. -/
theorem isSheaf_neighbourhood (n : ℕ) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS) (neighbourhood hi n).toFunctor := by
  have hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X.obj :=
    (isSheaf_iff_isSheaf_of_type _ X.obj).1 X.property
  exact ((neighbourhood hi n).isSheaf_iff hX).2 fun U s hs ↦
    eq_bot_of_le_ker_of_mem hs fun V g hg ↦ (map_mem_neighbourhood_iff hi s g).1 hg

/-- The `n`th infinitesimal neighbourhood, as an fppf sheaf. -/
def neighbourhoodSheaf (n : ℕ) : FppfSheaf B S hS :=
  ⟨(neighbourhood hi n).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_neighbourhood hi n)⟩

/-- The inclusion of the `n`th infinitesimal neighbourhood into `X`. -/
def neighbourhoodι (n : ℕ) : neighbourhoodSheaf hi n ⟶ X := ⟨(neighbourhood hi n).ι⟩

/-- The inclusion of `X_n` into `X` is a monomorphism of presheaves. -/
theorem mono_neighbourhoodι_hom (n : ℕ) : Mono (neighbourhoodι hi n).hom :=
  inferInstanceAs (Mono (neighbourhood hi n).ι)

/-- The inclusion of `X_n` into `X` is a monomorphism of fppf sheaves. -/
theorem mono_neighbourhoodι (n : ℕ) : Mono (neighbourhoodι hi n) :=
  (sheafToPresheaf _ _).mono_of_mono_map (mono_neighbourhoodι_hom hi n)

/-- The lift into `X_n` of the restriction of a section `ξ` to `V(I_ξ ^ (n + 1))`. -/
def neighbourhoodLift (n : ℕ) {T : BigFppfOver B S hS} (ξ : X.obj.obj (op T)) :
    uliftYoneda.{u + 1}.obj (siteSubscheme T (pullbackIdeal hi ξ ^ (n + 1))) ⟶
      (neighbourhood hi n).toFunctor :=
  Subfunctor.lift
    (uliftYoneda.{u + 1}.map (siteSubschemeι T _) ≫ uliftYonedaEquiv.{u + 1}.symm ξ) (by
      rintro V _ ⟨h, rfl⟩
      change X.obj.map (h.down ≫ siteSubschemeι T (pullbackIdeal hi ξ ^ (n + 1))).op ξ ∈ _
      rw [map_mem_neighbourhood_iff, CategoryTheory.Functor.map_comp]
      refine le_trans ?_ (Scheme.Hom.le_ker_comp _ _)
      rw [ker_toScheme_map_siteSubschemeι])

/-- **The base change of `X_n ⊂ X` along a section `ξ` is `V(I_ξ ^ (n + 1)) ⊂ T`.** -/
theorem isPullback_neighbourhood (n : ℕ) {T : BigFppfOver B S hS} (ξ : X.obj.obj (op T)) :
    IsPullback (neighbourhoodLift hi n ξ)
      (uliftYoneda.{u + 1}.map (siteSubschemeι T (pullbackIdeal hi ξ ^ (n + 1))))
      (neighbourhood hi n).ι (uliftYonedaEquiv.{u + 1}.symm ξ) := by
  refine isPullback_subfunctorι_of_forall _ _ inferInstance _ _ (Subfunctor.lift_ι _ _) ?_
  intro V y hy
  have hy' := (map_mem_neighbourhood_iff hi ξ y.down).1 hy
  exact ⟨ULift.up (siteSubschemeLift y.down hy'),
    congrArg ULift.up (siteSubschemeLift_ι y.down hy')⟩

/-- The inclusion of `X_n` into `X` is representable. -/
theorem relativelyRepresentable_neighbourhoodι (n : ℕ) :
    (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable
      (neighbourhoodι hi n).hom := by
  intro T g
  refine ⟨siteSubscheme T (pullbackIdeal hi (uliftYonedaEquiv.{u + 1} g) ^ (n + 1)),
    siteSubschemeι _ _, neighbourhoodLift hi n (uliftYonedaEquiv.{u + 1} g), ?_⟩
  have := isPullback_neighbourhood hi n (uliftYonedaEquiv.{u + 1} g)
  rwa [Equiv.symm_apply_apply] at this

/-- Every represented base change of `X_n ⊂ X` along a section `ξ` is a closed immersion with
kernel `I_ξ ^ (n + 1)`. -/
theorem isClosedImmersion_and_ker_of_isPullback_neighbourhoodι (n : ℕ)
    {a b : BigFppfOver B S hS} (g : uliftYoneda.{u + 1}.obj a ⟶ X.obj)
    (fst : uliftYoneda.{u + 1}.obj b ⟶ (neighbourhoodSheaf hi n).obj) (snd : b ⟶ a)
    (sq : IsPullback fst (uliftYoneda.{u + 1}.map snd) (neighbourhoodι hi n).hom g) :
    IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd) ∧
      ((BigFppfOver.toScheme B S hS).map snd).ker =
        pullbackIdeal hi (uliftYonedaEquiv.{u + 1} g) ^ (n + 1) := by
  have sq0 := isPullback_neighbourhood hi n (uliftYonedaEquiv.{u + 1} g)
  rw [Equiv.symm_apply_apply] at sq0
  let e := sq.isoIsPullback _ _ sq0
  let e' := uliftYoneda.{u + 1}.preimageIso e
  have he' : e'.hom ≫ siteSubschemeι a _ = snd := by
    apply uliftYoneda.{u + 1}.map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.preimageIso_hom,
      CategoryTheory.Functor.map_preimage]
    exact sq.isoIsPullback_hom_snd _ _ sq0
  rw [← he', CategoryTheory.Functor.map_comp]
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.Hom.ker_comp_of_isIso, ker_toScheme_map_siteSubschemeι]

/-- The kernel ideal sheaf `I_ξ` defines a closed subscheme of `T` mapping onto `T`. -/
theorem support_pullbackIdeal {T : BigFppfOver B S hS} (ξ : X.obj.obj (op T)) :
    ((pullbackIdeal hi ξ).support : Set ((BigFppfOver.toScheme B S hS).obj T)) = Set.univ := by
  have hc := isThickening_rep_snd hi (uliftYonedaEquiv.{u + 1}.symm ξ)
  have := hc.1
  unfold pullbackIdeal
  rw [Scheme.Hom.support_ker, Scheme.Hom.isClosedEmbedding _ |>.isClosed_range.closure_eq]
  exact Set.range_eq_univ.mpr hc.2

/-- **The inclusion of `X_n` into `X` is a representable thickening.** -/
theorem isRepresentableThickeningULift_neighbourhoodι (n : ℕ) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (neighbourhoodι hi n).hom := by
  refine ⟨relativelyRepresentable_neighbourhoodι hi n, ?_⟩
  intro a b g fst snd sq
  obtain ⟨hc, hker⟩ := isClosedImmersion_and_ker_of_isPullback_neighbourhoodι hi n g fst snd sq
  refine ⟨hc, ?_⟩
  rw [← Set.range_eq_univ,
    ← ((BigFppfOver.toScheme B S hS).map snd).isClosedEmbedding.isClosed_range.closure_eq,
    ← Scheme.Hom.support_ker, hker, Scheme.IdealSheafData.support_pow_succ]
  exact support_pullbackIdeal hi _

/-! ### The system of neighbourhoods -/

/-- The system `X_0 ⟶ X_1 ⟶ X_2 ⟶ ⋯` of infinitesimal neighbourhoods of `Z` in `X`. -/
def neighbourhoodDiagram : ℕ ⥤ FppfSheaf B S hS where
  obj n := neighbourhoodSheaf hi n
  map {n m} f := ⟨Subfunctor.homOfLe (neighbourhood_mono hi (leOfHom f))⟩
  map_id n := by ext; rfl
  map_comp f g := by ext; rfl

/-- The transition morphism `X_n ⟶ X_m` composed with the inclusion of `X_m` into `X` is the
inclusion of `X_n` into `X`. -/
theorem neighbourhoodDiagram_map_comp_ι {n m : ℕ} (f : n ⟶ m) :
    (neighbourhoodDiagram hi).map f ≫ neighbourhoodι hi m = neighbourhoodι hi n := by
  ext; rfl

/-- The inclusions of the infinitesimal neighbourhoods into `X`, as a cocone. -/
def neighbourhoodCocone : Cocone (neighbourhoodDiagram hi) where
  pt := X
  ι := { app n := neighbourhoodι hi n
         naturality _ _ f :=
           (neighbourhoodDiagram_map_comp_ι hi f).trans (Category.comp_id _).symm }

/-- A base change of a transition morphism `X_n ⟶ X_m` along a section of `X_m` is a base change
of `X_n ⊂ X`. -/
theorem isPullback_ι_of_isPullback_neighbourhoodDiagram {n m : ℕ} (f : n ⟶ m)
    {a b : BigFppfOver B S hS} (g : uliftYoneda.{u + 1}.obj a ⟶ (neighbourhoodSheaf hi m).obj)
    {fst : uliftYoneda.{u + 1}.obj b ⟶ (neighbourhoodSheaf hi n).obj} {snd : b ⟶ a}
    (sq : IsPullback fst (uliftYoneda.{u + 1}.map snd) ((neighbourhoodDiagram hi).map f).hom g) :
    IsPullback fst (uliftYoneda.{u + 1}.map snd) (neighbourhoodι hi n).hom
      (g ≫ (neighbourhoodι hi m).hom) :=
  @isPullback_comp_mono_of_eq _ _ _ _ _ _ _ _ _ _ _ sq (neighbourhoodι hi m).hom
    (mono_neighbourhoodι_hom hi m) _ (Subfunctor.homOfLe_ι (neighbourhood_mono hi (leOfHom f)))

/-- **Each transition morphism `X_n ⟶ X_m` is representable, and an `m`th-order thickening on
every represented base change.** -/
theorem hasSchemePropertyULift_isNthOrderThickening_neighbourhoodDiagram {n m : ℕ} (f : n ⟶ m) :
    Space.HasSchemePropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ Stacks.Thickenings.IsNthOrderThickening m k)
      ((neighbourhoodDiagram hi).map f).hom := by
  refine ⟨?_, ?_⟩
  · intro a g
    obtain ⟨b, snd, fst, sq⟩ :=
      relativelyRepresentable_neighbourhoodι hi n (g ≫ (neighbourhoodι hi m).hom)
    exact ⟨b, snd, fst, @isPullback_of_comp_mono_of_eq _ _ _ _ _ _ _ _ _ _ _
      (neighbourhoodι hi m).hom (mono_neighbourhoodι_hom hi m) _
      (Subfunctor.homOfLe_ι (neighbourhood_mono hi (leOfHom f))) sq⟩
  · intro a b g fst snd sq
    have sq' := isPullback_ι_of_isPullback_neighbourhoodDiagram hi f g sq
    obtain ⟨hc, hker⟩ :=
      isClosedImmersion_and_ker_of_isPullback_neighbourhoodι hi n _ fst snd sq'
    refine ⟨hc, ?_⟩
    have hmem : uliftYonedaEquiv.{u + 1} (g ≫ (neighbourhoodι hi m).hom) ∈
        (neighbourhood hi m).obj (op a) := by
      have : uliftYonedaEquiv.{u + 1} (g ≫ (neighbourhoodι hi m).hom) =
          (neighbourhoodι hi m).hom.app (op a) (uliftYonedaEquiv.{u + 1} g) :=
        uliftYonedaEquiv_comp g (neighbourhoodι hi m).hom
      rw [this]
      exact (uliftYonedaEquiv.{u + 1} g).2
    rw [hker, ← pow_mul]
    exact pow_eq_bot_of_le (Nat.le_mul_of_pos_left _ (Nat.succ_pos n)) hmem

/-- **`X_n` is the `n`th infinitesimal neighbourhood of `X_0` in `X_m`.** On every represented
base change along a section of `X_m`, the ideal sheaf of `X_n` is the `(n + 1)`st power of the
ideal sheaf of `X_0`. -/
theorem ker_pow_eq_ker_neighbourhoodDiagram (n m : ℕ) (hnm : n ≤ m)
    {a b c : BigFppfOver B S hS} (g : uliftYoneda.{u + 1}.obj a ⟶ (neighbourhoodSheaf hi m).obj)
    {fst₀ : uliftYoneda.{u + 1}.obj b ⟶ (neighbourhoodSheaf hi 0).obj} {snd₀ : b ⟶ a}
    (sq₀ : IsPullback fst₀ (uliftYoneda.{u + 1}.map snd₀)
      ((neighbourhoodDiagram hi).map (homOfLE (Nat.zero_le m))).hom g)
    {fstₙ : uliftYoneda.{u + 1}.obj c ⟶ (neighbourhoodSheaf hi n).obj} {sndₙ : c ⟶ a}
    (sqₙ : IsPullback fstₙ (uliftYoneda.{u + 1}.map sndₙ)
      ((neighbourhoodDiagram hi).map (homOfLE hnm)).hom g) :
    ((BigFppfOver.toScheme B S hS).map snd₀).ker ^ (n + 1) =
      ((BigFppfOver.toScheme B S hS).map sndₙ).ker := by
  rw [(isClosedImmersion_and_ker_of_isPullback_neighbourhoodι hi 0 _ _ _
      (isPullback_ι_of_isPullback_neighbourhoodDiagram hi _ g sq₀)).2,
    (isClosedImmersion_and_ker_of_isPullback_neighbourhoodι hi n _ _ _
      (isPullback_ι_of_isPullback_neighbourhoodDiagram hi _ g sqₙ)).2, zero_add, pow_one]

/-! ### The zeroth neighbourhood -/

/-- **`X_0` is the image of `i`.** A section lies in the image of the monomorphism `i` exactly
when the base change of `i` along it is an isomorphism, that is when `I_ξ = 0`. -/
theorem neighbourhood_zero_eq_range : neighbourhood hi 0 = Subfunctor.range i := by
  have : Mono i := mono_of_isRepresentableThickeningULift B S hS hi
  ext T ξ
  induction T using Opposite.rec with | _ T =>
  rw [mem_neighbourhood_iff, zero_add, pow_one]
  constructor
  · intro hξ
    let ξ' := uliftYonedaEquiv.{u + 1}.symm ξ
    have := isClosedImmersion_rep_snd hi ξ'
    have : IsIso ((BigFppfOver.toScheme B S hS).map (hi.rep.snd ξ')) :=
      IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hξ
    have : IsIso (hi.rep.snd ξ') := isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
    refine ⟨uliftYonedaEquiv.{u + 1} (inv (uliftYoneda.{u + 1}.map (hi.rep.snd ξ')) ≫
      hi.rep.fst ξ'), ?_⟩
    rw [← uliftYonedaEquiv_comp, Category.assoc, (hi.rep.isPullback ξ').w,
      IsIso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  · rintro ⟨z, rfl⟩
    let z' := uliftYonedaEquiv.{u + 1}.symm z
    have sq : IsPullback z' (uliftYoneda.{u + 1}.map (𝟙 T)) i
        (uliftYonedaEquiv.{u + 1}.symm (i.app (op T) z)) := by
      rw [CategoryTheory.Functor.map_id, ← uliftYonedaEquiv_symm_comp]
      have := isPullback_comp_mono (IsPullback.of_id_snd (f := z')) i
      rwa [Category.id_comp] at this
    rw [← ker_eq_pullbackIdeal hi _ sq, CategoryTheory.Functor.map_id]
    exact Scheme.Hom.ker_eq_bot_of_isIso _

end Neighbourhood

section Reduction

variable {X Z : FppfSheaf B S hS} {i : Z ⟶ X}
  (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)

/-- `Z` is isomorphic to `X_0`, compatibly with the inclusions into `X`. -/
def isoNeighbourhoodSheafZero : Z ≅ neighbourhoodSheaf hi 0 := by
  haveI : Mono i.hom := mono_of_isRepresentableThickeningULift B S hS hi
  refine ObjectProperty.isoMk _ (asIso (Subfunctor.toRange i.hom) ≪≫ ?_)
  exact { hom := Subfunctor.homOfLe (neighbourhood_zero_eq_range hi).ge
          inv := Subfunctor.homOfLe (neighbourhood_zero_eq_range hi).le }

/-- The isomorphism `Z ≅ X_0` composed with the inclusion of `X_0` into `X` is `i`. -/
theorem isoNeighbourhoodSheafZero_hom_ι :
    (isoNeighbourhoodSheafZero hi).hom ≫ neighbourhoodι hi 0 = i := by
  ext1
  rfl

/-- **If `i` is a reduction of `X`, so is the inclusion of `X_0`.** -/
theorem IsReduction.neighbourhoodι_zero (hred : IsReduction B S hS X Z i) :
    IsReduction B S hS X (neighbourhoodSheaf hi 0) (neighbourhoodι hi 0) := by
  have h := hred.precomp_iso (isoNeighbourhoodSheafZero hi).symm
  have he : (isoNeighbourhoodSheafZero hi).symm.hom ≫ i = neighbourhoodι hi 0 := by
    rw [Iso.symm_hom, Iso.inv_comp_eq, isoNeighbourhoodSheafZero_hom_ι]
  rwa [he] at h

end Reduction

end AlgebraicGeometry.FormalSpace

end
