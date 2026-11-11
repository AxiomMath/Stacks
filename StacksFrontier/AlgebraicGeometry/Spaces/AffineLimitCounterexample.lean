module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# A limit of affine spaces which is not an algebraic space

Stacks 07SF reads: *let `S` be a scheme, `I` a directed set and `(X_i)` an inverse system over
`I` of algebraic spaces over `S` with affine transition morphisms; then the fppf sheaf
`X = lim X_i` is an algebraic space.* Algebraic spaces over `S` are sheaves on a fixed big fppf
site `(Sch/S)_fppf`, whose schemes all have size below a cutoff cardinal `κ`
(`AlgebraicGeometry.BigFppfSite.cutoff`). With no bound on `I` the statement is false in every
such site.

Let `R` be a nonzero ring with `Spec R` in the site and let `X` be a set of cardinality `κ`.
For finite subsets `s ⊆ X` the affine spaces `𝔸^s_R = Spec R[x_j : j ∈ s]` lie in the site, and
for `s ⊆ t` the projections `𝔸^t_R → 𝔸^s_R` are morphisms of affine schemes, hence affine. The
limit of this system over the directed set of finite subsets of `X` is the functor `𝔸^X_R` of
`X`-tuples of global functions. Suppose it had an atlas `U → 𝔸^X_R`, surjective and étale. For
every `p : X → {0, 1}` the `R`-point `p` of `𝔸^X_R` lifts, after the surjective base change of
the atlas to `Spec R`, to a point of `U`, and `p` can be read off from the images of that point
in the stages `𝔸^{j}_R`: the coordinate `x_j` vanishes there exactly when `p j = 0`. So `U` has
at least `2 ^ κ` points, while a scheme of size below `κ` has at most `2 ^ size U < κ` points,
`κ` being a strong limit cardinal.

The source's proof writes `U = lim U_i` for affine schemes `U_i` and asserts that `U` is a
scheme; the limit scheme exists, but not in `(Sch/S)_fppf` once `I` is large. Stacks 03FO
explains that the big site may be enlarged at will, which is the reading under which 07SF
holds; in one fixed site some bound on the system is needed. The form with the bound
`#I < cof κ` on the index category and its morphism types is
`AlgebraicGeometry.Space.isAlgebraicSpace_limit`.

## Main definitions

* `AlgebraicGeometry.Space.AffineSpaceSystem.site`: the inverse system of the affine spaces
  `𝔸^s_R`, `s` a finite subset of `X`, in the big fppf site of `Spec R`.

## Main results

* `AlgebraicGeometry.Space.AffineSpaceSystem.not_isAlgebraicSpace_limit`: for `#X` the cutoff,
  the limit of this system is not an algebraic space, although every stage is an algebraic
  space (`AlgebraicGeometry.Space.AffineSpaceSystem.isAlgebraicSpace_site_comp_yoneda_obj`) and
  every transition morphism is affine
  (`AlgebraicGeometry.Space.AffineSpaceSystem.isAffineHom_site_comp_yoneda_map`).
* `AlgebraicGeometry.Space.not_forall_isAlgebraicSpace_limit_of_isAffineHom`: the negation of
  Stacks 07SF, stated for an arbitrary scheme of the site and an arbitrary directed set, in
  every big fppf site.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 03FO](https://stacks.math.columbia.edu/tag/03FO)
* [Stacks Project, Section 000H](https://stacks.math.columbia.edu/tag/000H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

namespace AffineSpaceSystem

variable (R : Type u) [CommRing R] (X : Type u)

/-- The coordinate rings `R[x_j : j ∈ s]` of the affine spaces `𝔸^s_R`, for `s` a finite subset
of `X`, with the inclusions of polynomial rings induced by the inclusions of finite subsets. -/
noncomputable def ring : Finset X ⥤ CommRingCat.{u} where
  obj s := .of (MvPolynomial s R)
  map h := CommRingCat.ofHom
    (MvPolynomial.rename (fun j : (_ : Finset X) ↦ (⟨j.1, h.le j.2⟩ : (_ : Finset X)))).toRingHom
  map_id s := by
    ext : 1
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_) <;> simp
  map_comp f g := by
    ext : 1
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_) <;> simp

/-- The affine spaces `𝔸^s_R` as an inverse system of schemes over the finite subsets `s` of
`X`. -/
noncomputable abbrev scheme : (Finset X)ᵒᵖ ⥤ Scheme.{u} := (ring R X).op ⋙ Scheme.Spec

variable {R X} in
/-- Every affine space `𝔸^s_R` over a finite set of variables lies in a big fppf site containing
`Spec R`: its coordinate ring has cardinality at most `max ℵ₀ #R`. -/
theorem contains_scheme_obj (B : BigFppfSite.{u}) (hR : B.Contains (Spec (.of R)))
    (s : (Finset X)ᵒᵖ) : B.Contains ((scheme R X).obj s) := by
  refine Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hR ?_
  refine MvPolynomial.cardinalMk_le_max.trans (max_le (max_le (le_max_right _ _) ?_)
    (le_max_left _ _))
  exact (Cardinal.lt_aleph0_of_finite _).le.trans (le_max_left _ _)

variable (B : BigFppfSite.{u}) (hR : B.Contains (Spec (.of R)))

/-- The inclusion `R → R[x_j : j ∈ s]` of the constants. -/
noncomputable def constants (s : Finset X) : CommRingCat.of R ⟶ (ring R X).obj s :=
  CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial s R)

/-- The inclusions of constants are compatible with the transition maps: for `s ⊆ t`, composing
`R → R[x_j : j ∈ s]` with `R[x_j : j ∈ s] → R[x_j : j ∈ t]` gives `R → R[x_j : j ∈ t]`. -/
@[reassoc (attr := simp)]
theorem constants_comp_map {s t : Finset X} (h : s ⟶ t) :
    constants R X s ≫ (ring R X).map h = constants R X t := by
  ext r
  exact MvPolynomial.rename_C _ r

/-- The inverse system of the affine spaces `𝔸^s_R`, `s ⊆ X` finite, in the big fppf site of
`Spec R`, each over `Spec R` through the inclusion `R → R[x_j : j ∈ s]` of constants. -/
noncomputable def site : (Finset X)ᵒᵖ ⥤ BigFppfOver B (Spec (.of R)) hR :=
  ((schemeSizeBelow B.cutoff).lift (scheme R X) (contains_scheme_obj B hR)).toOver (B.obj hR)
    (fun s ↦ ObjectProperty.homMk (Spec.map (constants R X (unop s))))
    (fun {s t} h ↦ by
      ext : 1
      change Spec.map ((ring R X).map h.unop) ≫ Spec.map (constants R X _) =
        Spec.map (constants R X _)
      rw [← Spec.map_comp, constants_comp_map])

/-- Every stage `𝔸^s_R` of the system is affine. -/
instance isAffine_toScheme_site_obj (s : (Finset X)ᵒᵖ) :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj ((site R X B hR).obj s)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- Every stage of the system of representable presheaves is an algebraic space. -/
theorem isAlgebraicSpace_site_comp_yoneda_obj (s : (Finset X)ᵒᵖ) :
    IsAlgebraicSpace B (Spec (.of R)) hR ((site R X B hR ⋙ yoneda).obj s) :=
  isAlgebraicSpace_yoneda B _ hR _

/-- Every transition morphism of the system of representable presheaves is affine. -/
theorem isAffineHom_site_comp_yoneda_map {s t : (Finset X)ᵒᵖ} (h : s ⟶ t) :
    IsAffineHom B (Spec (.of R)) hR ((site R X B hR ⋙ yoneda).map h) :=
  isAffineHom_yoneda_map B _ hR _

/-! ### The `R`-points with coordinates `0` and `1` -/

variable {R X}

/-- Evaluation `R[x_j : j ∈ s] → R` at the point with coordinates `p j ∈ {0, 1}`. -/
noncomputable def evalAt (p : X → Bool) (s : Finset X) : (ring R X).obj s ⟶ CommRingCat.of R :=
  CommRingCat.ofHom (MvPolynomial.eval fun j : s ↦ if p j.1 then (1 : R) else 0)

/-- Evaluation at `p` is compatible with the transition maps: for `s ⊆ t`, restricting evaluation
on `R[x_j : j ∈ t]` to `R[x_j : j ∈ s]` is evaluation on `R[x_j : j ∈ s]`. -/
@[reassoc (attr := simp)]
theorem map_comp_evalAt (p : X → Bool) {s t : Finset X} (h : s ⟶ t) :
    (ring R X).map h ≫ evalAt p t = evalAt p s := by
  ext : 1
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_) <;> simp [evalAt, ring]

/-- Evaluation at `p` is a retraction of the inclusion of constants `R → R[x_j : j ∈ s]`. -/
@[reassoc (attr := simp)]
theorem constants_comp_evalAt (p : X → Bool) (s : Finset X) :
    constants R X s ≫ evalAt p s = 𝟙 _ := by
  ext r
  exact MvPolynomial.eval_C r

/-- `Spec R` itself, the terminal object of the big fppf site of `Spec R`. -/
noncomputable abbrev base : BigFppfOver B (Spec (.of R)) hR := Over.mk (𝟙 (B.obj hR))

/-- The `R`-point of `𝔸^s_R` with coordinates `p j ∈ {0, 1}`, as a morphism of the site. -/
noncomputable def point (p : X → Bool) (s : (Finset X)ᵒᵖ) :
    base B hR ⟶ (site R X B hR).obj s :=
  Over.homMk (ObjectProperty.homMk (Spec.map (evalAt p (unop s)))) (by
    ext : 1
    change Spec.map (evalAt p (unop s)) ≫ Spec.map (constants R X _) = 𝟙 _
    rw [← Spec.map_comp, constants_comp_evalAt, Spec.map_id])

/-- The underlying morphism of schemes of `point p s` is `Spec` of evaluation at `p`. -/
theorem toScheme_map_point (p : X → Bool) (s : (Finset X)ᵒᵖ) :
    (BigFppfOver.toScheme B (Spec (.of R)) hR).map (point B hR p s) =
      Spec.map (evalAt p (unop s)) :=
  rfl

/-- The compatible family of the points `point p s`: the `R`-point of the limit `𝔸^X_R` with
coordinates `p`. -/
noncomputable def pointCone (p : X → Bool) : Cone (site R X B hR) where
  pt := base B hR
  π :=
    { app := point B hR p
      naturality := fun s t h ↦ by
        apply (BigFppfOver.toScheme B (Spec (.of R)) hR).map_injective
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Functor.map_comp, toScheme_map_point]
        change Spec.map (evalAt p (unop t)) =
          Spec.map (evalAt p (unop s)) ≫ Spec.map ((ring R X).map h.unop)
        rw [← Spec.map_comp, map_comp_evalAt] }

/-- The `j`-th coordinate of a point `y` of `𝔸^s_R`, read off as whether `x_j` is a unit at `y`
(it is never `0` and `1` at once). On the `R`-points `point p s` it returns `p j`. -/
noncomputable def coord {s : Finset X} (y : Spec ((ring R X).obj s)) {j : X} (hj : j ∈ s) :
    Bool :=
  haveI := Classical.dec
  decide ((MvPolynomial.X ⟨j, hj⟩ : MvPolynomial s R) ∉ y.asIdeal)

/-- The `j`-th coordinate of the image of any point of `Spec R` under the `R`-point with
coordinates `p` is `p j`. -/
theorem coord_point (p : X → Bool) (s : Finset X) (z : Spec (.of R)) {j : X} (hj : j ∈ s) :
    coord ((Spec.map (evalAt p s)) z) hj = p j := by
  have hX : (MvPolynomial.X ⟨j, hj⟩ : MvPolynomial s R) ∈
      ((Spec.map (evalAt p s)) z).asIdeal ↔ (if p j then (1 : R) else 0) ∈ z.asIdeal := by
    have e : (evalAt p s).hom (MvPolynomial.X ⟨j, hj⟩) = if p j then (1 : R) else 0 :=
      MvPolynomial.eval_X _
    exact (show _ ↔ (evalAt p s).hom (MvPolynomial.X ⟨j, hj⟩) ∈ z.asIdeal from Iff.rfl).trans
      (by rw [e])
  rw [Bool.eq_iff_iff]
  simp only [coord, decide_eq_true_eq, hX]
  cases p j
  · simp [z.asIdeal.zero_mem]
  · simp [(Ideal.ne_top_iff_one _).1 z.isPrime.ne_top]

/-! ### The cardinality obstruction -/

/-- **An atlas of the limit sees every `{0, 1}`-point.** If the limit `𝔸^X_R` of the system
`site R X B hR` were an algebraic space, an atlas `U` of it would have at least `2 ^ #X` points:
the `R`-point with coordinates `p : X → Bool` lifts, after the surjective base change of the
atlas, to a point of `U`, and `p` is read off from that point through the projections to the
stages `𝔸^{j}_R`. -/
theorem two_pow_mk_le_of_isAlgebraicSpace [Nontrivial R]
    (h : IsAlgebraicSpace B (Spec (.of R)) hR (limit (site R X B hR ⋙ yoneda))) :
    ∃ U : BigFppfOver B (Spec (.of R)) hR,
      2 ^ #X ≤ #((BigFppfOver.toScheme B (Spec (.of R)) hR).obj U) := by
  obtain ⟨U, f, hsurj, -⟩ := h.exists_atlas
  refine ⟨U, ?_⟩
  let T := BigFppfOver.toScheme B (Spec (.of R)) hR
  let φ : ∀ j : X, U ⟶ (site R X B hR).obj (op {j}) := fun j ↦
    yoneda.preimage (f ≫ limit.π (site R X B hR ⋙ yoneda) (op {j}))
  let Φ : T.obj U → X → Bool := fun u j ↦
    coord (T.map (φ j) u) (Finset.mem_singleton_self j)
  have hΦ : Function.Surjective Φ := by
    intro p
    let g : yoneda.obj (base B hR) ⟶ limit (site R X B hR ⋙ yoneda) :=
      limit.lift _ (yoneda.mapCone (pointCone B hR p))
    have hrep := hsurj.rep
    have hsnd : Surjective (T.map (hrep.snd g)) := hsurj.property_snd g
    obtain ⟨v, hv⟩ := hsnd.surj (Nonempty.some inferInstance : Spec (.of R))
    refine ⟨T.map (hrep.fst' g) v, funext fun j ↦ ?_⟩
    have hsq : hrep.fst' g ≫ φ j = hrep.snd g ≫ point B hR p (op {j}) := by
      apply yoneda.map_injective
      simp only [Functor.map_comp, φ, Functor.map_preimage, hrep.map_fst']
      rw [hrep.w_assoc]
      simp [g, pointCone]
    have hpt : T.map (φ j) (T.map (hrep.fst' g) v) =
        Spec.map (evalAt p {j}) (Nonempty.some inferInstance : Spec (.of R)) := by
      rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hsq, Functor.map_comp,
        Scheme.Hom.comp_apply, hv]
      rfl
    exact (congrArg (fun y : Spec ((ring R X).obj {j}) ↦ coord y (Finset.mem_singleton_self j))
      hpt).trans (coord_point p {j} _ _)
  calc (2 : Cardinal) ^ #X = #(X → Bool) := by simp
    _ ≤ #(T.obj U) := Cardinal.mk_le_of_surjective hΦ

variable (R) in
/-- **The limit of the affine spaces `𝔸^s_R` over the finite subsets `s` of a set of cardinality
the cutoff is not an algebraic space.** Here `R` is any nonzero ring with `Spec R` in the big
fppf site `B`. Every stage is an affine scheme of the site
(`AlgebraicGeometry.Space.AffineSpaceSystem.isAlgebraicSpace_site_comp_yoneda_obj`) and every
transition morphism is affine
(`AlgebraicGeometry.Space.AffineSpaceSystem.isAffineHom_site_comp_yoneda_map`). An atlas `U` of
the limit would have at least `2 ^ κ` points, `κ` the cutoff of `B`, while a scheme of the site
has at most `2 ^ size U < κ` points. -/
theorem not_isAlgebraicSpace_limit [Nontrivial R] :
    ¬ IsAlgebraicSpace B (Spec (.of R)) hR (limit (site R B.cutoff.out B hR ⋙ yoneda)) := by
  intro h
  obtain ⟨U, hU⟩ := two_pow_mk_le_of_isAlgebraicSpace B hR h
  have h₁ := Scheme.mk_le_two_pow_size ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj U)
  have h₂ : 2 ^ ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj U).size < B.cutoff :=
    B.cutoff_isStrongPrelimit U.left.property
  rw [Cardinal.mk_out] at hU
  exact lt_irrefl _ (((cantor B.cutoff).trans_le (hU.trans h₁)).trans h₂)

end AffineSpaceSystem

/-- **Stacks 07SF, read in one fixed big fppf site, is false.** For every big fppf site `B`
the statement

> for every scheme `S` of `B`, every directed set `I` and every inverse system `(X_i)` over `I`
> of algebraic spaces over `S` with affine transition morphisms, the fppf sheaf `lim X_i` is an
> algebraic space over `S`

fails, already for `S = Spec ℤ`, `I` the finite subsets of a set of cardinality the cutoff of
`B`, and `X_s = 𝔸^s_ℤ`; see `AlgebraicGeometry.Space.AffineSpaceSystem.not_isAlgebraicSpace_limit`.
-/
theorem not_forall_isAlgebraicSpace_limit_of_isAffineHom (B : BigFppfSite.{u}) :
    ¬ ∀ (S : Scheme.{u}) (hS : B.Contains S) (I : Type u) [PartialOrder I]
      [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
      (∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) →
      IsAlgebraicSpace B S hS (limit D) := by
  intro h
  have hR : B.Contains (Spec (.of (ULift.{u} ℤ))) := by
    rw [BigFppfSite.Contains, Scheme.size_Spec]
    refine max_lt B.aleph0_lt_cutoff ?_
    have hℤ : #(CommRingCat.of (ULift.{u} ℤ)) = ℵ₀ := by simp
    rw [hℤ]
    exact B.aleph0_lt_cutoff
  exact AffineSpaceSystem.not_isAlgebraicSpace_limit (ULift.{u} ℤ) B hR
    (h _ hR (Finset B.cutoff.out) _
      (AffineSpaceSystem.isAlgebraicSpace_site_comp_yoneda_obj _ _ B hR)
      (AffineSpaceSystem.isAffineHom_site_comp_yoneda_map _ _ B hR))

end AlgebraicGeometry.Space

end
