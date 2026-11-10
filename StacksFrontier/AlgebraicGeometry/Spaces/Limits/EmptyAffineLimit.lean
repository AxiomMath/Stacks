module

public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitCounterexample
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize

/-!
# A limit of nonempty affine schemes which is empty in the big fppf site

Let `B` be a big fppf site with cutoff `κ`, let `k` be a field with `Spec k` in `B`, and let `X`
be a set with `#X ≥ κ`. For finite subsets `s ⊆ X` the rational function fields
`K_s = k(x_j : j ∈ s)` are countable over `k`, so the schemes `Spec K_s` lie in the site, and
for `s ⊆ t` the morphisms `Spec K_t → Spec K_s` are morphisms of affine schemes, hence affine.
The limit of the representable sheaves `h_{Spec K_s}` over the directed set of finite subsets
of `X` is the *empty* algebraic space. Indeed a section over a nonempty scheme `T` of the site
is a compatible family of field embeddings `K_s → Γ(T, 𝒪_T)`; they send the variables `x_j`,
`j ∈ X`, to pairwise distinct global sections, while `T` has fewer than `κ` global sections.
The limit of the `Spec K_s` in the category of all schemes is `Spec k(x_j : j ∈ X)`, which is
nonempty and lies outside the site.

So in one fixed big fppf site the limit sheaf `lim X_i` can be an algebraic space and still
not be the limit Stacks has in mind, the one computed on affine charts by `lim U_i` (Stacks
07SF). The results of Stacks on limits of algebraic spaces fail for such a limit. For Stacks
07SK, take `Y_i = X_i` and `Z_i = ∅` over a stage: over the limit both become empty, hence
isomorphic, but no stage admits a morphism `X_j → ∅`. This is
`AlgebraicGeometry.Space.not_forall_exists_hom_after_baseChange_of_isAlgebraicSpace_limit`, the
negation of the fullness part of Stacks 07SK with the hypothesis that the limit is an algebraic
space in place of a bound on the index category.

## Main definitions

* `AlgebraicGeometry.Space.RationalFunctionFieldSystem.site`: the inverse system of the
  schemes `Spec k(x_j : j ∈ s)`, `s` a finite subset of `X`, in the big fppf site of `Spec k`.

## Main results

* `AlgebraicGeometry.Space.RationalFunctionFieldSystem.isEmpty_of_limit_obj`: for `#X` at
  least the cutoff, the limit has no sections over a nonempty object of the site.
* `AlgebraicGeometry.Space.RationalFunctionFieldSystem.limitIsoEmpty`: the limit is
  isomorphic to the empty scheme; in particular it is an algebraic space
  (`AlgebraicGeometry.Space.RationalFunctionFieldSystem.isAlgebraicSpace_limit_site_comp_yoneda`).
* `AlgebraicGeometry.Space.not_forall_exists_hom_after_baseChange_of_isAlgebraicSpace_limit`:
  in every big fppf site, fullness in Stacks 07SK fails for some cofiltered system of
  quasi-compact quasi-separated algebraic spaces with affine transition morphisms whose limit
  is an algebraic space.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 03FO](https://stacks.math.columbia.edu/tag/03FO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

namespace RationalFunctionFieldSystem

variable (k : Type u) [Field k] (X : Type u)

/-- The inclusion of polynomial rings `k[x_j : j ∈ s] → k[x_j : j ∈ t]` for `s ⊆ t`. -/
noncomputable abbrev polyMap {s t : Finset X} (h : s ≤ t) :
    MvPolynomial s k →+* MvPolynomial t k :=
  (MvPolynomial.rename fun j : s ↦ (⟨j.1, h j.2⟩ : t)).toRingHom

/-- The inclusion `k[x_j : j ∈ s] → k[x_j : j ∈ t]` is injective. -/
theorem polyMap_injective {s t : Finset X} (h : s ≤ t) : Function.Injective (polyMap k X h) :=
  MvPolynomial.rename_injective _ fun a b hab ↦ Subtype.ext (by injection hab)

/-- The rational function fields `k(x_j : j ∈ s)`, for `s` a finite subset of `X`, with the
field extensions induced by the inclusions of finite subsets. -/
noncomputable def field : Finset X ⥤ CommRingCat.{u} where
  obj s := .of (FractionRing (MvPolynomial s k))
  map h := CommRingCat.ofHom (IsFractionRing.map (polyMap_injective k X h.le))
  map_id s := by
    ext : 1
    refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial s k)) ?_
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_) <;>
      simp [IsFractionRing.map]
  map_comp {s _ _} f g := by
    ext : 1
    refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial s k)) ?_
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_) <;>
      simp [IsFractionRing.map, IsLocalization.map_eq]

/-- The variable `x_j` in `k(x_l : l ∈ s)`, for `j ∈ s`. -/
noncomputable def gen {s : Finset X} {j : X} (hj : j ∈ s) : (field k X).obj s :=
  (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)) (MvPolynomial.X ⟨j, hj⟩) :
    FractionRing (MvPolynomial s k))

/-- The field extension `k(x_l : l ∈ s) → k(x_l : l ∈ t)` sends the variable `x_j` to `x_j`. -/
theorem map_gen {s t : Finset X} (h : s ⟶ t) {j : X} (hj : j ∈ s) :
    (field k X).map h (gen k X hj) = gen k X (h.le hj) := by
  change (IsFractionRing.map (polyMap_injective k X h.le) : FractionRing (MvPolynomial s k) →+*
      FractionRing (MvPolynomial t k)) (algebraMap (MvPolynomial s k) _ (MvPolynomial.X ⟨j, hj⟩)) =
    algebraMap (MvPolynomial t k) _ (MvPolynomial.X ⟨j, h.le hj⟩)
  rw [IsFractionRing.map, IsLocalization.map_eq]
  simp

/-- Distinct elements of `s` give distinct variables in `k(x_l : l ∈ s)`. -/
theorem gen_injective {s : Finset X} {j l : X} (hj : j ∈ s) (hl : l ∈ s)
    (h : gen k X hj = gen k X hl) : j = l :=
  congrArg Subtype.val (MvPolynomial.X_injective (IsFractionRing.injective
    (MvPolynomial s k) (FractionRing (MvPolynomial s k)) h))

/-- The inclusion `k → k(x_j : j ∈ s)` of the constants. -/
noncomputable def constants (s : Finset X) : CommRingCat.of k ⟶ (field k X).obj s :=
  CommRingCat.ofHom ((algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k))).comp
    MvPolynomial.C)

/-- The field extensions `k(x_j : j ∈ s) → k(x_j : j ∈ t)` are compatible with the inclusions
of the constants `k`. -/
@[reassoc (attr := simp)]
theorem constants_comp_map {s t : Finset X} (h : s ⟶ t) :
    constants k X s ≫ (field k X).map h = constants k X t := by
  ext r
  change (IsFractionRing.map (polyMap_injective k X h.le) : FractionRing (MvPolynomial s k) →+*
      FractionRing (MvPolynomial t k)) (algebraMap (MvPolynomial s k) _ (MvPolynomial.C r)) =
    algebraMap (MvPolynomial t k) _ (MvPolynomial.C r)
  rw [IsFractionRing.map, IsLocalization.map_eq]
  simp

/-- The schemes `Spec k(x_j : j ∈ s)` as an inverse system over the finite subsets of `X`. -/
noncomputable abbrev scheme : (Finset X)ᵒᵖ ⥤ Scheme.{u} := (field k X).op ⋙ Scheme.Spec

variable {k X} in
/-- Every stage `Spec k(x_j : j ∈ s)` lies in a big fppf site containing `Spec k`. -/
theorem contains_scheme_obj (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (s : (Finset X)ᵒᵖ) : B.Contains ((scheme k X).obj s) := by
  refine Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hk ?_
  refine (Cardinal.mk_le_of_isLocalization (nonZeroDivisors (MvPolynomial ↥(unop s) k))
    (FractionRing (MvPolynomial ↥(unop s) k))).trans
    (max_le (le_max_left _ _) ?_)
  refine MvPolynomial.cardinalMk_le_max.trans (max_le (max_le (le_max_right _ _) ?_)
    (le_max_left _ _))
  exact (Cardinal.lt_aleph0_of_finite _).le.trans (le_max_left _ _)

variable (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- The inverse system of the schemes `Spec k(x_j : j ∈ s)`, `s ⊆ X` finite, in the big fppf
site of `Spec k`. -/
noncomputable def site : (Finset X)ᵒᵖ ⥤ BigFppfOver B (Spec (.of k)) hk :=
  ((schemeSizeBelow B.cutoff).lift (scheme k X) (contains_scheme_obj B hk)).toOver (B.obj hk)
    (fun s ↦ ObjectProperty.homMk (Spec.map (constants k X (unop s))))
    (fun {s t} h ↦ by
      ext : 1
      change Spec.map ((field k X).map h.unop) ≫ Spec.map (constants k X _) =
        Spec.map (constants k X _)
      rw [← Spec.map_comp, constants_comp_map])

/-- Every stage `Spec k(x_j : j ∈ s)` is affine. -/
instance isAffine_toScheme_site_obj (s : (Finset X)ᵒᵖ) :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj ((site k X B hk).obj s)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- Every stage `Spec k(x_j : j ∈ s)` is nonempty. -/
instance nonempty_toScheme_site_obj (s : (Finset X)ᵒᵖ) :
    Nonempty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj ((site k X B hk).obj s)) :=
  inferInstanceAs (Nonempty (Spec (.of (FractionRing (MvPolynomial ↥(unop s) k)))))

/-- Every stage of the system of representable presheaves is an algebraic space. -/
theorem isAlgebraicSpace_site_comp_yoneda_obj (s : (Finset X)ᵒᵖ) :
    IsAlgebraicSpace B (Spec (.of k)) hk ((site k X B hk ⋙ yoneda).obj s) :=
  isAlgebraicSpace_yoneda B _ hk _

/-- Every transition morphism of the system of representable presheaves is affine. -/
theorem isAffineHom_site_comp_yoneda_map {s t : (Finset X)ᵒᵖ} (h : s ⟶ t) :
    IsAffineHom B (Spec (.of k)) hk ((site k X B hk ⋙ yoneda).map h) :=
  isAffineHom_yoneda_map B _ hk _

/-- **The limit of the system is empty on every nonempty object of the site**, once `#X` is at
least the cutoff. A section over `T` is a compatible family of morphisms `T → Spec k(x_j : j ∈ s)`,
that is of field embeddings `k(x_j : j ∈ s) → Γ(T, 𝒪_T)`; these send the variables `x_j`,
`j ∈ X`, to pairwise distinct global sections, but `T` has fewer than the cutoff global
sections. -/
theorem isEmpty_of_limit_obj (hX : B.cutoff ≤ #X) (T : BigFppfOver B (Spec (.of k)) hk)
    (z : (limit (site k X B hk ⋙ yoneda)).obj (op T)) :
    IsEmpty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) := by
  classical
  let Tt := BigFppfOver.toScheme B (Spec (.of k)) hk
  let D := site k X B hk ⋙ yoneda
  let m : ∀ s, T ⟶ (site k X B hk).obj s := fun s ↦ (limit.π D s).app (op T) z
  have hm : ∀ {s t : (Finset X)ᵒᵖ} (h : s ⟶ t), m s ≫ (site k X B hk).map h = m t :=
    fun {s t} h ↦ by
      simpa [D, m] using ConcreteCategory.congr_hom (NatTrans.congr_app (limit.w D h) (op T)) z
  let m' : ∀ s : Finset X, Tt.obj T ⟶ Spec ((field k X).obj s) := fun s ↦ Tt.map (m (op s))
  have hm' : ∀ {s t : Finset X} (h : s ⟶ t), m' t ≫ Spec.map ((field k X).map h) = m' s :=
    fun {s t} h ↦ by
      have e := congrArg Tt.map (hm h.op)
      rw [Functor.map_comp] at e
      exact e
  let φ : ∀ s : Finset X, (field k X).obj s ⟶ Γ(Tt.obj T, ⊤) := fun s ↦
    (Scheme.ΓSpecIso _).inv ≫ (m' s).appTop
  have hφ : ∀ {s t : Finset X} (h : s ⟶ t), (field k X).map h ≫ φ t = φ s := by
    intro s t h
    simp only [φ, ← hm' h, Scheme.Hom.comp_appTop]
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  refine ⟨fun x ↦ ?_⟩
  have : Nontrivial Γ(Tt.obj T, ⊤) :=
    ((Tt.obj T).presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  let ψ : X → Γ(Tt.obj T, ⊤) := fun j ↦ φ {j} (gen k X (Finset.mem_singleton_self j))
  have key : ∀ (j : X) (s : Finset X) (hs : j ∈ s), ψ j = φ s (gen k X hs) := by
    intro j s hs
    simp only [ψ, ← hφ (homOfLE (Finset.singleton_subset_iff.2 hs))]
    rw [ConcreteCategory.comp_apply, map_gen]
  have hψ : Function.Injective ψ := by
    intro j l hjl
    have hj : j ∈ ({j, l} : Finset X) := by simp
    have hl : l ∈ ({j, l} : Finset X) := by simp
    exact gen_injective k X hj hl
      ((show FractionRing (MvPolynomial ({j, l} : Finset X) k) →+* Γ(Tt.obj T, ⊤) from
        (φ {j, l}).hom).injective ((key j _ hj).symm.trans (hjl.trans (key l _ hl))))
  have h₃ : 2 ^ (Tt.obj T).size < B.cutoff := B.cutoff_isStrongPrelimit T.left.property
  exact lt_irrefl _ ((hX.trans ((Cardinal.mk_le_of_injective hψ).trans
    ((Tt.obj T).mk_sections_le_two_pow_size ⊤))).trans_lt h₃)

/-! ### The limit is the empty algebraic space -/

variable {k X B hk}

/-- The morphism of the site out of an object with empty underlying scheme. -/
noncomputable def homOfIsEmptyToScheme {V : BigFppfOver B (Spec (.of k)) hk}
    (hV : IsEmpty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj V))
    (W : BigFppfOver B (Spec (.of k)) hk) : V ⟶ W :=
  Over.homMk (ObjectProperty.homMk
      ((isInitialOfIsEmpty (X := (BigFppfOver.toScheme B (Spec (.of k)) hk).obj V)).to _))
    (by
      ext : 1
      exact (isInitialOfIsEmpty (X := (BigFppfOver.toScheme B (Spec (.of k)) hk).obj V)).hom_ext
        _ _)

/-- Any two morphisms of the site out of an object with empty underlying scheme are equal. -/
theorem hom_ext_of_isEmpty_toScheme {V W : BigFppfOver B (Spec (.of k)) hk}
    (hV : IsEmpty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj V)) (a b : V ⟶ W) : a = b :=
  (BigFppfOver.toScheme B (Spec (.of k)) hk).map_injective
    ((isInitialOfIsEmpty (X := (BigFppfOver.toScheme B (Spec (.of k)) hk).obj V)).hom_ext _ _)

variable (k B hk) in
/-- The empty scheme, as an object of the big fppf site of `Spec k`. -/
noncomputable abbrev emptyObj : BigFppfOver B (Spec (.of k)) hk :=
  siteObject B (Spec (.of k)) hk (B.contains_of_mono (Scheme.emptyTo _) hk)
    (Scheme.emptyTo (Spec (.of k)))

/-- The underlying scheme of the empty object is empty. -/
instance isEmpty_toScheme_emptyObj :
    IsEmpty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (emptyObj k B hk)) :=
  inferInstanceAs (IsEmpty (∅ : Scheme.{u}))

variable (hX : B.cutoff ≤ #X)

include hX in
/-- A section of the limit over `T` exists only when `T` is empty, and then it is the unique
morphism to the empty object. -/
noncomputable def limitToEmpty :
    limit (site k X B hk ⋙ yoneda) ⟶ yoneda.obj (emptyObj k B hk) where
  app T := TypeCat.ofHom fun z ↦
    homOfIsEmptyToScheme (isEmpty_of_limit_obj k X B hk hX T.unop z) _
  naturality T T' a := by
    ext z
    exact hom_ext_of_isEmpty_toScheme (isEmpty_of_limit_obj k X B hk hX T'.unop
      ((limit (site k X B hk ⋙ yoneda)).map a z)) _ _

/-- The cone of the morphisms out of the empty object. -/
noncomputable def emptyCone : Cone (site k X B hk ⋙ yoneda) where
  pt := yoneda.obj (emptyObj k B hk)
  π :=
    { app s := yoneda.map (homOfIsEmptyToScheme inferInstance _)
      naturality s t h := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Functor.comp_map, ← Functor.map_comp]
        exact congrArg yoneda.map (hom_ext_of_isEmpty_toScheme inferInstance _ _) }

include hX in
/-- **The limit of the system is the empty algebraic space.** -/
noncomputable def limitIsoEmpty :
    limit (site k X B hk ⋙ yoneda) ≅ yoneda.obj (emptyObj k B hk) where
  hom := limitToEmpty hX
  inv := limit.lift _ (emptyCone (k := k) (X := X) (B := B) (hk := hk))
  hom_inv_id := by
    refine limit.hom_ext fun s ↦ ?_
    ext T z
    exact hom_ext_of_isEmpty_toScheme (isEmpty_of_limit_obj k X B hk hX T.unop z) _ _
  inv_hom_id := by
    ext T z
    have : IsEmpty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T.unop) :=
      ⟨fun x ↦ isEmptyElim ((BigFppfOver.toScheme B (Spec (.of k)) hk).map z x)⟩
    exact hom_ext_of_isEmpty_toScheme this _ _

include hX in
/-- Once `#X` is at least the cutoff, the limit of the system is an algebraic space. -/
theorem isAlgebraicSpace_limit_site_comp_yoneda :
    IsAlgebraicSpace B (Spec (.of k)) hk (limit (site k X B hk ⋙ yoneda)) :=
  (isAlgebraicSpace_yoneda B _ hk _).of_iso (limitIsoEmpty hX).symm

/-! ### No stage sees the morphism to the empty object -/

/-- The empty object over the stage `Spec k(x_j : j ∈ s)`. -/
noncomputable abbrev emptyOver (s : (Finset X)ᵒᵖ) : Over ((site k X B hk ⋙ yoneda).obj s) :=
  Over.mk (yoneda.map (homOfIsEmptyToScheme (isEmpty_toScheme_emptyObj (k := k) (B := B)
    (hk := hk)) ((site k X B hk).obj s)))

/-- **After base change along a transition morphism, a stage `Spec k(x_j : j ∈ t)` still admits no
morphism to the empty object**, since it is nonempty. -/
theorem isEmpty_hom_pullback_emptyOver {s t : (Finset X)ᵒᵖ} (e : t ⟶ s) :
    IsEmpty ((Over.pullback ((site k X B hk ⋙ yoneda).map e)).obj (Over.mk (𝟙 _)) ⟶
      (Over.pullback ((site k X B hk ⋙ yoneda).map e)).obj (emptyOver s)) := by
  refine ⟨fun g ↦ ?_⟩
  let D := site k X B hk ⋙ yoneda
  let a : D.obj t ⟶ pullback (𝟙 (D.obj s)) (D.map e) :=
    pullback.lift (D.map e) (𝟙 _) (by simp)
  let b : yoneda.obj ((site k X B hk).obj t) ⟶ yoneda.obj (emptyObj k B hk) :=
    a ≫ g.left ≫ pullback.fst _ _
  obtain ⟨x⟩ := (nonempty_toScheme_site_obj k X B hk t)
  exact isEmptyElim ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (yoneda.preimage b) x)

include hX in
/-- **Over the limit the stage and the empty object become isomorphic**: the limit is empty, so
the base change of `𝟙` admits a morphism to the base change of the empty object. -/
noncomputable def homPullbackLimit (s : (Finset X)ᵒᵖ) :
    (Over.pullback (limit.π (site k X B hk ⋙ yoneda) s)).obj (Over.mk (𝟙 _)) ⟶
      (Over.pullback (limit.π (site k X B hk ⋙ yoneda) s)).obj (emptyOver s) :=
  Over.homMk (pullback.lift (pullback.snd _ _ ≫ limitToEmpty hX) (pullback.snd _ _) (by
    rw [Category.assoc]
    congr 1
    ext T z
    exact hom_ext_of_isEmpty_toScheme (isEmpty_of_limit_obj k X B hk hX T.unop z) _ _))
    (pullback.lift_snd _ _ _)

end RationalFunctionFieldSystem

/-- **Stacks 07SK (fullness) fails for a limit which is an algebraic space, without a size bound
on the index category.** For every big fppf site `B` the statement

> for every cofiltered system `(X_i)` of quasi-compact, quasi-separated algebraic spaces over `S`
> with affine transition morphisms whose limit `X = lim X_i` is an algebraic space, and for
> algebraic spaces `Y_i, Z_i` of finite presentation over some `X_i`, every morphism
> `X ×_{X_i} Y_i → X ×_{X_i} Z_i` over `X` comes from a morphism over some `X_j`, `j ≥ i`

is false. The system is `Spec k(x_j : j ∈ s)` over the finite subsets `s` of a set of
cardinality the cutoff (`AlgebraicGeometry.Space.RationalFunctionFieldSystem.site`), whose limit
in the site is empty although no stage is; `Y_i = X_i` and `Z_i = ∅`. -/
theorem not_forall_exists_hom_after_baseChange_of_isAlgebraicSpace_limit
    (B : BigFppfSite.{u}) :
    ¬ ∀ (S : Scheme.{u}) (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (I : Type u)
      [Category.{u} I] [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
      (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) →
      (∀ i, IsQuasiCompactSpace B S hS (D.obj i)) →
      (∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) →
      IsAlgebraicSpace B S hS (limit D) →
      ∀ (i : I) (Yᵢ Zᵢ : Over (D.obj i)), IsAlgebraicSpace B S hS Yᵢ.left →
        IsAlgebraicSpace B S hS Zᵢ.left → IsFinitePresentation B S hS Yᵢ.hom →
        IsFinitePresentation B S hS Zᵢ.hom →
        ∀ (_ : (Over.pullback (limit.π D i)).obj Yᵢ ⟶ (Over.pullback (limit.π D i)).obj Zᵢ),
          ∃ (j : I) (e : j ⟶ i),
            Nonempty ((Over.pullback (D.map e)).obj Yᵢ ⟶ (Over.pullback (D.map e)).obj Zᵢ) := by
  intro h
  let k := ULift.{u} ℚ
  have hk : B.Contains (Spec (.of k)) := by
    rw [BigFppfSite.Contains, Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff (by simpa [k, Cardinal.mk_uLift] using B.aleph0_lt_cutoff)
  let X := B.cutoff.out
  have hX : B.cutoff ≤ #X := (Cardinal.mk_out _).ge
  let T := BigFppfOver.toScheme B (Spec (.of k)) hk
  let D := RationalFunctionFieldSystem.site k X B hk ⋙ yoneda
  let i : (Finset X)ᵒᵖ := op ∅
  have hfp : ∀ {V W : BigFppfOver B (Spec (.of k)) hk} (p : V ⟶ W) {q : T.obj V ⟶ T.obj W},
      T.map p = q → [LocallyOfFinitePresentation q] → [QuasiCompact q] → [QuasiSeparated q] →
      IsFinitePresentation B _ hk (yoneda.map p) :=
    fun p q hq _ _ _ ↦ by
      subst hq
      exact isFinitePresentation_yoneda_map B _ hk p ⟨‹_›, ‹_›, ‹_›⟩
  have hempty : ∀ (W : BigFppfOver B (Spec (.of k)) hk)
      (p : RationalFunctionFieldSystem.emptyObj k B hk ⟶ W),
      T.map p = Scheme.emptyTo _ := fun W p ↦
    (isInitialOfIsEmpty (X := T.obj (RationalFunctionFieldSystem.emptyObj k B hk))).hom_ext _ _
  obtain ⟨j, e, ⟨g⟩⟩ := h _ hk B.contains_terminal _ D
    (RationalFunctionFieldSystem.isAlgebraicSpace_site_comp_yoneda_obj k X B hk)
    (RationalFunctionFieldSystem.isAffineHom_site_comp_yoneda_map k X B hk)
    (fun s ↦ isQuasiCompactSpace_yoneda_of_isAffine B _ hk _ inferInstance)
    (fun s ↦ isAbsolutelyQuasiSeparated_yoneda_obj B _ hk B.contains_terminal _ inferInstance)
    (RationalFunctionFieldSystem.isAlgebraicSpace_limit_site_comp_yoneda hX) i
    (Over.mk (𝟙 _)) (RationalFunctionFieldSystem.emptyOver i)
    (isAlgebraicSpace_yoneda B _ hk _) (isAlgebraicSpace_yoneda B _ hk _)
    (by
      change IsFinitePresentation B _ hk (𝟙 (D.obj i))
      rw [show 𝟙 (D.obj i) = yoneda.map (𝟙 _) from (yoneda.map_id _).symm]
      exact hfp _ (T.map_id _))
    (hfp _ (hempty _ _))
    (RationalFunctionFieldSystem.homPullbackLimit hX i)
  exact (RationalFunctionFieldSystem.isEmpty_hom_pullback_emptyOver e).false g

end AlgebraicGeometry.Space

end
