module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.BaseChangeJointApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ElementaryNeighborhoodTruncation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkQuotientBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The truncated local rings of two base changes with identified truncated bases

Let `p : Y ⟶ T` be a morphism of schemes, let `t` be a point of `T` and let `D₁`, `D₂` be local
rings with local homomorphisms `σ₁ : 𝒪_{T, t} → D₁` and `σ₂ : 𝒪_{T, t} → D₂`, giving two
morphisms `b₁ : Spec D₁ ⟶ T` and `b₂ : Spec D₂ ⟶ T` through `Spec 𝒪_{T, t} ⟶ T`. Suppose an
isomorphism

```
ε : D₁ / 𝔪₁ ^ N  ≅  D₂ / 𝔪₂ ^ N
```

identifies the two truncated bases compatibly with `σ₁` and `σ₂`. **Then the two base changes of
`p` have the same truncated local rings**: for every point `y₁` of `Y ×_{T, b₁} Spec D₁` lying
over a point `y` of `Y` and over the closed point of `Spec D₁` there are a point `y₂` of
`Y ×_{T, b₂} Spec D₂` lying over the same `y` and over the closed point of `Spec D₂`, and a ring
isomorphism

```
𝒪_{Y ×_{T, b₁} Spec D₁, y₁} / 𝔪_{y₁} ^ N  ≅  𝒪_{Y ×_{T, b₂} Spec D₂, y₂} / 𝔪_{y₂} ^ N
```

compatible with the two maps out of `𝒪_{Y, y}` **and with the two structure maps of the base**:
elements of `D₁` and of `D₂` that `ε` identifies have germs at `y₁` and at `y₂` with the same
class.

This is **the `Y`-level half of the bridge that clause (5) of Stacks Tag 0CAW cites by name**.
That clause compares a map into `𝒪^∧_{Y_σ, y_σ}`, for `Y_σ` the base change of `Y ⟶ T` along the
map `𝒪_{T, t} → 𝒪^∧_{S, s}` named `σ`, with a map into `𝒪_{Y ×_{T, τ} V, (y, v)}`, and justifies
the comparison by saying that "`Y_σ` and `Y ×_{T, τ} V` are canonically isomorphic over
`𝒪_{V, v}/𝔪_v ^ N = 𝒪_{S, s}/𝔪_s ^ N` by parts (2) and (3)". The identification of the two
*bases* that this sentence appeals to is
`AlgebraicGeometry.EtaleNeighborhood.completedTruncationEquiv` together with clause (3); the
identification of the two *base changes* that it concludes is what is proved here, with the base
identification as the hypothesis `ε`.

## Main results

* `StacksDraft.ArtinApproximation.exists_truncationEquiv_stalk_pullback_fromSpecStalk`: the
  statement displayed above.
* `StacksDraft.ArtinApproximation.exists_point_ringEquiv_stalk_pullback_fromSpecStalk_comp`: the
  replacement of a scheme by the spectrum of one of its local rings in a base change. For
  `g : Y ⟶ T` and `τ : V ⟶ T` and a point `v` of `V`, a point of
  `Y ×_{T} Spec 𝒪_{V, v}` over a point `y` of `Y` and over the closed point determines a point
  `(y, v)` of `Y ×_{T, τ} V` with the *same local ring*, compatibly with the two maps out of
  `𝒪_{Y, y}`. This is what lets the statement above — which speaks of base changes along the
  spectra of local rings — be read at `Y ×_{T, τ} V`, where clause (5) of Tag 0CAW needs it.
* `StacksDraft.ArtinApproximation.exists_truncationEquiv_stalk_relativeBaseChange`: the two
  previous results composed, at Tag 0CAW's own data. For `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}`, an
  elementary étale neighbourhood `(V, v)` of `(S, s)` and `τ : V ⟶ T` satisfying clause (3),
  every point `y_σ` of `Y_σ` over `y` and over the closed point gives a point `(y, v)` of
  `Y ×_{T, τ} V` and an isomorphism
  `𝒪_{Y_σ, y_σ}/𝔪^N ≅ 𝒪_{Y ×_{T, τ} V, (y, v)}/𝔪^N` compatible with the two maps out of
  `𝒪_{Y, y}` and with the two structure maps of the base, the latter read through the truncation
  isomorphism of clause (2). This is the whole of the identification clause (5) of Tag 0CAW
  cites.

## Implementation notes

*How the two sides are compared.* Not directly: both are compared with a third base change.
Writing `Λ` for `D₂ / 𝔪₂ ^ N`, the hypothesis on `ε` says exactly that the two surjections
`D₁ → Λ` (through `ε`) and `D₂ → Λ` carry `σ₁` and `σ₂` to one and the same homomorphism
`𝒪_{T, t} → Λ`, so the two composites `Spec Λ ⟶ Spec D_i ⟶ T` are the same morphism and the two
schemes `(Y ×_{T, b_i} Spec D_i) ×_{Spec D_i} Spec Λ` are both `Y ×_T Spec Λ`. Each of them has
the same truncated local rings as its `Y ×_{T, b_i} Spec D_i`, by
`AlgebraicGeometry.exists_ringEquiv_quotient_maximalIdeal_pow_stalk_pullback_of_surjective`: the
kernel of `D_i → Λ` is `𝔪_i ^ N`, which the structure map carries into `𝔪_{y_i} ^ N` because
`y_i` lies over the closed point of `Spec D_i`.

*Why the second point is produced rather than taken.* A point of `Y ×_{T, b₂} Spec D₂` over `y`
and over the closed point is in fact unique, the residue fields of `𝒪_{T, t}`, `D₁` and `D₂` all
agreeing; but that uniqueness is not needed and is not proved here. The point produced is the
image of `y₁` under the chain of identifications, which is what makes the comparison of local
rings canonical.

*What pins the isomorphism down.* Two compatibilities, not one. Besides the compatibility with
the two maps out of `𝒪_{Y, y}` the statement carries the **base-side** one: `d₁ : D₁` and
`d₂ : D₂` that `ε` identifies have germs at `y₁` and at `y₂` with the same class. The two
together determine the isomorphism on the images of `𝒪_{Y, y}` and of the base, which generate
the local ring of a base change, and both are what clause (5) of Tag 0CAW appeals to when it
calls the identification canonical. The base-side clause is read on the germs of the global
sections that elements of `D_i` determine, not on the local ring of `Spec D_i` at its closed
point, so no identification of that local ring with `D_i` is needed.

*What this does not do.* It is the input to clauses (4) and (5) of Tag 0CAW, not those clauses.
Those two clauses are *not* established by this file; a correct formalisation of them has to
produce `V`, `τ`, `W` and `f` jointly from `σ` and `φ`, because a stage-1 choice of `V` and `τ`
made without reference to `φ` can make clause (5) unsatisfiable. Note in particular that the
identification proved here is of *truncated* local rings, as clause (5) needs; it does not give
a map `𝒪_{X, x} → 𝒪^∧_{Y ×_{T, τ} V, (y, v)}` out of the given
`φ : 𝒪_{X, x} → 𝒪^∧_{Y_σ, y_σ}`, so it does not reduce clauses (4) and (5) to
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_relativeApproximation`, whose
hypothesis is such a map.

## References

* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace StacksDraft.ArtinApproximation

/-- The map on local rings read out of a morphism at a point of its source is the map on local
rings, when the equation locating the image is `rfl`. -/
private theorem stalkHomAt_rfl {X Z : Scheme.{u}} {x : X} (m : X ⟶ Z) :
    m.stalkHomAt (rfl : m x = m x) = (m.stalkMap x).hom := by
  simp [Scheme.Hom.stalkHomAt]

/-- Equal morphisms induce the same map on local rings at a point. -/
private theorem stalkHomAt_congr {X Z : Scheme.{u}} {x : X} {z : Z} (m m' : X ⟶ Z)
    (hmm' : m = m') (h : m x = z) (h' : m' x = z) :
    m.stalkHomAt h = m'.stalkHomAt h' := by
  subst hmm'
  rfl

/-- The map on local rings of a morphism `m`, followed by the map on local rings of `f`, is the map
on local rings of any morphism equal to `m ≫ f`. -/
private theorem stalkMap_comp_stalkHomAt {X Y Z : Scheme.{u}} {x : X} {z : Z} (m : X ⟶ Y)
    (f : Y ⟶ Z) (f' : X ⟶ Z) (hf : m ≫ f = f') (h : f (m x) = z) (h' : f' x = z) :
    (m.stalkMap x).hom.comp (f.stalkHomAt h) = f'.stalkHomAt h' := by
  subst hf
  rw [Scheme.Hom.stalkHomAt_comp m f rfl h, stalkHomAt_rfl]

/-- The comparison isomorphism of two pullbacks over the same morphism along equal legs is
compatible with both projections. -/
private theorem congrHom_hom_comp {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Z)
    {g₁ g₂ : Y ⟶ Z} [HasPullback f g₁] [HasPullback f g₂] (h : g₁ = g₂) :
    ((pullback.congrHom (rfl : f = f) h).hom ≫ pullback.fst f g₂ = pullback.fst f g₁) ∧
      ((pullback.congrHom (rfl : f = f) h).hom ≫ pullback.snd f g₂ = pullback.snd f g₁) := by
  constructor
  · simp [pullback.congrHom, pullback.map, pullback.lift_fst]
  · simp [pullback.congrHom, pullback.map, pullback.lift_snd]

/-- **The two iterated base changes along equal composites agree.** For `p : Y ⟶ T` and two
morphisms `b_i : A_i ⟶ T` equipped with `g_i : B ⟶ A_i` whose composites `g_i ≫ b_i` agree, the
schemes `(Y ×_{T, b_i} A_i) ×_{A_i} B` are canonically isomorphic, compatibly with the projection
to `Y` and with the projection to `B`. Both are the base change of `p` along the common
composite, by `CategoryTheory.Limits.pullbackLeftPullbackSndIso`. -/
@[ega "I 3.3.11" "more general"]
private theorem exists_iso_pullback_snd_of_comp_eq {Y T A₁ A₂ B : Scheme.{u}}
    (p : Y ⟶ T) (b₁ : A₁ ⟶ T) (b₂ : A₂ ⟶ T) (g₁ : B ⟶ A₁) (g₂ : B ⟶ A₂)
    (hgb : g₁ ≫ b₁ = g₂ ≫ b₂) :
    ∃ Φ : (pullback (pullback.snd p b₁) g₁ : Scheme.{u}) ≅
        (pullback (pullback.snd p b₂) g₂ : Scheme.{u}),
      Φ.hom ≫ pullback.fst (pullback.snd p b₂) g₂ ≫ pullback.fst p b₂ =
          pullback.fst (pullback.snd p b₁) g₁ ≫ pullback.fst p b₁ ∧
        Φ.hom ≫ pullback.snd (pullback.snd p b₂) g₂ =
          pullback.snd (pullback.snd p b₁) g₁ := by
  obtain ⟨hκfst, hκsnd⟩ := congrHom_hom_comp p hgb
  refine ⟨(pullbackLeftPullbackSndIso p b₁ g₁).trans
    ((pullback.congrHom (rfl : p = p) hgb).trans
      (pullbackLeftPullbackSndIso p b₂ g₂).symm), ?_, ?_⟩
  · have h2 : (pullbackLeftPullbackSndIso p b₂ g₂).inv ≫
        pullback.fst (pullback.snd p b₂) g₂ ≫ pullback.fst p b₂ =
        pullback.fst p (g₂ ≫ b₂) := by
      rw [← pullbackLeftPullbackSndIso_hom_fst p b₂ g₂, Iso.inv_hom_id_assoc]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [h2, hκfst]
    exact pullbackLeftPullbackSndIso_hom_fst p b₁ g₁
  · have h2 : (pullbackLeftPullbackSndIso p b₂ g₂).inv ≫
        pullback.snd (pullback.snd p b₂) g₂ = pullback.snd p (g₂ ≫ b₂) := by
      rw [← pullbackLeftPullbackSndIso_hom_snd p b₂ g₂, Iso.inv_hom_id_assoc]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [h2, hκsnd]
    exact pullbackLeftPullbackSndIso_hom_snd p b₁ g₁

/-- **Two equal composite morphisms induce the same map of local rings, read factor by
factor.** If `Φ ≫ q₂ ≫ r₂ = q₁ ≫ r₁` as morphisms `W₁ ⟶ Z`, then the two induced maps
`𝒪_{Z, z} → 𝒪_{W₁, w₁}` agree. -/
private theorem stalkMap_comp_eq_of_comp_eq {W₁ W₂ Y₁ Y₂ Z : Scheme.{u}}
    (Φ : W₁ ⟶ W₂) (q₁ : W₁ ⟶ Y₁) (q₂ : W₂ ⟶ Y₂) (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z)
    {w₁ : W₁} {z : Z} (h₁ : r₁ (q₁ w₁) = z) (h₂ : r₂ (q₂ (Φ w₁)) = z)
    (heq : Φ ≫ q₂ ≫ r₂ = q₁ ≫ r₁) (a : Z.presheaf.stalk z) :
    (Φ.stalkMap w₁).hom ((q₂.stalkMap (Φ w₁)).hom (r₂.stalkHomAt h₂ a)) =
      (q₁.stalkMap w₁).hom (r₁.stalkHomAt h₁ a) := by
  have hm : (q₁ ≫ r₁) w₁ = z := h₁
  have h₃ := stalkMap_comp_stalkHomAt q₂ r₂ _ rfl h₂ h₂
  have h₄ := stalkMap_comp_stalkHomAt Φ (q₂ ≫ r₂) _ heq h₂ hm
  rw [← h₃] at h₄
  exact (RingHom.congr_fun h₄ a).trans
    (RingHom.congr_fun (stalkMap_comp_stalkHomAt q₁ r₁ _ rfl h₁ hm) a).symm

/-- **Transport of a comparison of truncated local rings along an isomorphism of the two
comparison schemes.** Given `Φ : W₁ ≅ W₂` over `Y`, and isomorphisms identifying the truncated
local rings of `Y₁` at `q₁ w₁` and of `Y₂` at `q₂ (Φ w₁)` with those of `W₁` at `w₁` and of `W₂`
at `Φ w₁` through `q₁` and `q₂`, the truncated local rings of `Y₁` and `Y₂` are isomorphic
compatibly with the two maps out of `𝒪_{Y, y}`.

The isomorphism is pinned down by more than that: *any* two germs `c₁` and `c₂` with the same
image in `𝒪_{W₁, w₁}` — one read through `q₁`, the other through `q₂` and `Φ` — have the same
class under it. That is the first conclusion, and the compatibility with `𝒪_{Y, y}` is its
instance at `c_i = r_i^♯ a`, by
`StacksDraft.ArtinApproximation.stalkMap_comp_eq_of_comp_eq`. The base-side compatibility that
clause (5) of Stacks Tag 0CAW needs is the instance at the two structure maps of the base. -/
private theorem exists_truncationEquiv_of_iso {Y₁ Y₂ W₁ W₂ Y : Scheme.{u}} (N : ℕ)
    (q₁ : W₁ ⟶ Y₁) (q₂ : W₂ ⟶ Y₂) (r₁ : Y₁ ⟶ Y) (r₂ : Y₂ ⟶ Y) (Φ : W₁ ≅ W₂)
    (w₁ : W₁) {y : Y} (h₁ : r₁ (q₁ w₁) = y) (h₂ : r₂ (q₂ (Φ.hom w₁)) = y)
    (heq : Φ.hom ≫ q₂ ≫ r₂ = q₁ ≫ r₁)
    (e₁ : (Y₁.presheaf.stalk (q₁ w₁) ⧸ maximalIdeal (Y₁.presheaf.stalk (q₁ w₁)) ^ N) ≃+*
      (W₁.presheaf.stalk w₁ ⧸ maximalIdeal (W₁.presheaf.stalk w₁) ^ N))
    (he₁ : ∀ b : Y₁.presheaf.stalk (q₁ w₁),
      e₁ (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ ((q₁.stalkMap w₁).hom b))
    (e₂ : (Y₂.presheaf.stalk (q₂ (Φ.hom w₁)) ⧸
        maximalIdeal (Y₂.presheaf.stalk (q₂ (Φ.hom w₁))) ^ N) ≃+*
      (W₂.presheaf.stalk (Φ.hom w₁) ⧸ maximalIdeal (W₂.presheaf.stalk (Φ.hom w₁)) ^ N))
    (he₂ : ∀ b : Y₂.presheaf.stalk (q₂ (Φ.hom w₁)),
      e₂ (Ideal.Quotient.mk _ b) =
        Ideal.Quotient.mk _ ((q₂.stalkMap (Φ.hom w₁)).hom b)) :
    ∃ e : (Y₁.presheaf.stalk (q₁ w₁) ⧸ maximalIdeal (Y₁.presheaf.stalk (q₁ w₁)) ^ N) ≃+*
        (Y₂.presheaf.stalk (q₂ (Φ.hom w₁)) ⧸
          maximalIdeal (Y₂.presheaf.stalk (q₂ (Φ.hom w₁))) ^ N),
      (∀ (c₁ : Y₁.presheaf.stalk (q₁ w₁)) (c₂ : Y₂.presheaf.stalk (q₂ (Φ.hom w₁))),
          (q₁.stalkMap w₁).hom c₁ =
              (Φ.hom.stalkMap w₁).hom ((q₂.stalkMap (Φ.hom w₁)).hom c₂) →
            e (Ideal.Quotient.mk _ c₁) = Ideal.Quotient.mk _ c₂) ∧
        ∀ a : Y.presheaf.stalk y,
          e (Ideal.Quotient.mk _ (r₁.stalkHomAt h₁ a)) =
            Ideal.Quotient.mk _ (r₂.stalkHomAt h₂ a) := by
  have : IsIso (Φ.hom.stalkMap w₁) := isIso_stalkMap_of_flat_isPreimmersion Φ.hom w₁
  let θ : W₂.presheaf.stalk (Φ.hom w₁) ≃+* W₁.presheaf.stalk w₁ :=
    (asIso (Φ.hom.stalkMap w₁)).commRingCatIsoToRingEquiv
  have hθapp : ∀ z, θ z = (Φ.hom.stalkMap w₁).hom z := fun _ => rfl
  have hme : (maximalIdeal (W₂.presheaf.stalk (Φ.hom w₁))).map
      (θ : W₂.presheaf.stalk (Φ.hom w₁) →+* W₁.presheaf.stalk w₁) =
      maximalIdeal (W₁.presheaf.stalk w₁) :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (θ : W₂.presheaf.stalk (Φ.hom w₁) →+* W₁.presheaf.stalk w₁) θ.surjective
  have hpow : maximalIdeal (W₁.presheaf.stalk w₁) ^ N =
      ((maximalIdeal (W₂.presheaf.stalk (Φ.hom w₁))) ^ N).map
        (θ : W₂.presheaf.stalk (Φ.hom w₁) →+* W₁.presheaf.stalk w₁) := by
    rw [Ideal.map_pow, hme]
  let θt : (W₂.presheaf.stalk (Φ.hom w₁) ⧸
        maximalIdeal (W₂.presheaf.stalk (Φ.hom w₁)) ^ N) ≃+*
      (W₁.presheaf.stalk w₁ ⧸ maximalIdeal (W₁.presheaf.stalk w₁) ^ N) :=
    Ideal.quotientEquiv _ _ θ hpow
  have hθtmk : ∀ x : W₂.presheaf.stalk (Φ.hom w₁),
      θt (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (θ x) := fun _ => rfl
  have hgen : ∀ (c₁ : Y₁.presheaf.stalk (q₁ w₁)) (c₂ : Y₂.presheaf.stalk (q₂ (Φ.hom w₁))),
      (q₁.stalkMap w₁).hom c₁ = (Φ.hom.stalkMap w₁).hom ((q₂.stalkMap (Φ.hom w₁)).hom c₂) →
      (e₁.trans (θt.symm.trans e₂.symm)) (Ideal.Quotient.mk _ c₁) =
        Ideal.Quotient.mk _ c₂ := by
    intro c₁ c₂ hc
    have hgoal : θt (e₂ (Ideal.Quotient.mk _ c₂)) = e₁ (Ideal.Quotient.mk _ c₁) := by
      rw [he₂, he₁, hθtmk, hθapp]
      exact congrArg (Ideal.Quotient.mk _) hc.symm
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, ← hgoal, RingEquiv.symm_apply_apply,
      RingEquiv.symm_apply_apply]
  exact ⟨e₁.trans (θt.symm.trans e₂.symm), hgen, fun a => hgen _ _
    (stalkMap_comp_eq_of_comp_eq Φ.hom q₁ q₂ r₁ r₂ h₁ h₂ heq a).symm⟩

/-- **The structure map of a scheme over `Spec R` is natural in the scheme.** For `m : Z' ⟶ Z`
and `f : Z ⟶ Spec R`, the germ at `m z'` of the global section that `r : R` determines on `Z`,
carried into the local ring of `Z'` at `z'` by the stalk map of `m`, is the germ at `z'` of the
global section that `r` determines on `Z'` through `m ≫ f`. -/
private theorem stalkMap_germ_appTop {R : CommRingCat.{u}} {Z Z' : Scheme.{u}}
    (f : Z ⟶ Spec R) (m : Z' ⟶ Z) (z' : Z') (r : R) :
    (m.stalkMap z').hom
        (((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ Z.presheaf.germ ⊤ (m z') trivial).hom r) =
      ((Scheme.ΓSpecIso R).inv ≫ (m ≫ f).appTop ≫
        Z'.presheaf.germ ⊤ z' trivial).hom r := by
  have key : ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ Z.presheaf.germ ⊤ (m z') trivial) ≫
        m.stalkMap z' =
      (Scheme.ΓSpecIso R).inv ≫ (m ≫ f).appTop ≫ Z'.presheaf.germ ⊤ z' trivial := by
    simp only [Category.assoc]
    rw [Scheme.Hom.germ_stalkMap m ⊤ z' trivial]
    simp only [Scheme.Hom.preimage_top]
    rw [← Scheme.Hom.comp_appTop_assoc]
  exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp key) r

/-- **The structure map of a base change along `Spec Λ ⟶ Spec D`, read through the first
projection.** Let `f : Z ⟶ Spec D`, let `ρ : D → Λ` be a ring map and form the base change
`Z ×_{Spec D} Spec Λ`. The germ of the global section that `d : D` determines on `Z`, carried
into the local ring of the base change at `w` by the first projection, is the germ of the global
section that `ρ d` determines on the base change through its second projection.

This is `StacksDraft.ArtinApproximation.stalkMap_germ_appTop` for the first projection, after
`pullback.condition` replaces the leg through `f` by the leg through `g`;
`Scheme.ΓSpecIso_inv_naturality` then turns `Spec ρ` on global sections back into `ρ`. -/
private theorem stalkMap_fst_germ_appTop {D Λ : Type u} [CommRing D] [CommRing Λ]
    (ρ : D →+* Λ) {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of D))
    (g : Spec (CommRingCat.of Λ) ⟶ Spec (CommRingCat.of D))
    (hg : g = Spec.map (CommRingCat.ofHom ρ)) (w : (pullback f g : Scheme.{u})) (d : D) :
    ((pullback.fst f g).stalkMap w).hom
        (((Scheme.ΓSpecIso (CommRingCat.of D)).inv ≫ f.appTop ≫
          Z.presheaf.germ ⊤ (pullback.fst f g w) trivial).hom d) =
      ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ (pullback.snd f g).appTop ≫
        (pullback f g : Scheme.{u}).presheaf.germ ⊤ w trivial).hom (ρ d) := by
  subst hg
  rw [stalkMap_germ_appTop f (pullback.fst f _) w d, pullback.condition,
    Scheme.Hom.comp_appTop, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- **Two base changes along two surjections onto one and the same `Λ` carry base elements with
the same image in `Λ` to the same germ.** Let `f_i : Z_i ⟶ Spec D_i`, let `Λ` be a `D₁`- and a
`D₂`-algebra, and let `Φ` identify the two schemes `Z_i ×_{Spec D_i} Spec Λ` compatibly with
their projections to `Spec Λ`. If `d₁ : D₁` and `d₂ : D₂` have the same image in `Λ`, then the
germ of the global section that `d₁` determines on `Z₁`, read through the first projection, and
the germ of the one that `d₂` determines on `Z₂`, read through the first projection and then
`Φ`, agree in the local ring of `Z₁ ×_{Spec D₁} Spec Λ` at `w₁`.

This is the hypothesis of
`StacksDraft.ArtinApproximation.exists_truncationEquiv_of_iso`'s first conclusion at the two
structure maps of the base, i.e. the base-side compatibility that clause (5) of Stacks Tag 0CAW
needs. Both sides are the germ at `w₁` of the global section that the common image in `Λ`
determines on `Z₁ ×_{Spec D₁} Spec Λ`. -/
private theorem stalkMap_fst_germ_appTop_eq_of_algebraMap_eq
    {D₁ D₂ Λ : Type u} [CommRing D₁] [CommRing D₂] [CommRing Λ] [Algebra D₁ Λ] [Algebra D₂ Λ]
    {Z₁ Z₂ : Scheme.{u}} (f₁ : Z₁ ⟶ Spec (CommRingCat.of D₁))
    (f₂ : Z₂ ⟶ Spec (CommRingCat.of D₂))
    (g₁ : Spec (CommRingCat.of Λ) ⟶ Spec (CommRingCat.of D₁))
    (hg₁ : g₁ = Spec.map (CommRingCat.ofHom (algebraMap D₁ Λ)))
    (g₂ : Spec (CommRingCat.of Λ) ⟶ Spec (CommRingCat.of D₂))
    (hg₂ : g₂ = Spec.map (CommRingCat.ofHom (algebraMap D₂ Λ)))
    (Φ : (pullback f₁ g₁ : Scheme.{u}) ≅ (pullback f₂ g₂ : Scheme.{u}))
    (hsndΦ : Φ.hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁)
    (w₁ : (pullback f₁ g₁ : Scheme.{u})) (d₁ : D₁) (d₂ : D₂)
    (hd : algebraMap D₁ Λ d₁ = algebraMap D₂ Λ d₂) :
    ((pullback.fst f₁ g₁).stalkMap w₁).hom
        (((Scheme.ΓSpecIso (CommRingCat.of D₁)).inv ≫ f₁.appTop ≫
          Z₁.presheaf.germ ⊤ (pullback.fst f₁ g₁ w₁) trivial).hom d₁) =
      (Φ.hom.stalkMap w₁).hom
        (((pullback.fst f₂ g₂).stalkMap (Φ.hom w₁)).hom
          (((Scheme.ΓSpecIso (CommRingCat.of D₂)).inv ≫ f₂.appTop ≫
            Z₂.presheaf.germ ⊤ (pullback.fst f₂ g₂ (Φ.hom w₁)) trivial).hom d₂)) := by
  rw [stalkMap_fst_germ_appTop (algebraMap D₁ Λ) f₁ g₁ hg₁ w₁ d₁,
    stalkMap_fst_germ_appTop (algebraMap D₂ Λ) f₂ g₂ hg₂ (Φ.hom w₁) d₂,
    stalkMap_germ_appTop (pullback.snd f₂ g₂) Φ.hom w₁ _, hsndΦ, hd]
/-- **The map of local rings of the canonical morphism `Spec 𝒪_{X, x} ⟶ X`, read at the closed
point, is the canonical map `𝒪_{X, x} → 𝒪_{Spec 𝒪_{X, x}, closed point}`** — the germ at the
closed point of the global section that an element of `𝒪_{X, x}` determines.

This is `StacksDraft.ArtinApproximation.stalkHomAt_specMap_fromSpecStalk` at `ρ = 𝟙`, together
with Mathlib's `AlgebraicGeometry.ΓSpecIso_hom_stalkClosedPointIso_inv`, which identifies
`(stalkClosedPointIso R).inv` with the germ of `(AlgebraicGeometry.Scheme.ΓSpecIso R).inv`. -/
private theorem stalkHomAt_fromSpecStalk {X : Scheme.{u}} (x : X) :
    (X.fromSpecStalk x).stalkHomAt (Scheme.fromSpecStalk_closedPoint (X := X) (x := x)) =
      ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
        (Spec (X.presheaf.stalk x)).presheaf.germ ⊤
          (IsLocalRing.closedPoint (X.presheaf.stalk x)) trivial).hom := by
  have hid : X.fromSpecStalk x = Spec.map (𝟙 (X.presheaf.stalk x)) ≫ X.fromSpecStalk x := by
    rw [Spec.map_id, Category.id_comp]
  have hpt : (Spec.map (𝟙 (X.presheaf.stalk x)) ≫ X.fromSpecStalk x)
      (IsLocalRing.closedPoint (X.presheaf.stalk x)) = x := by
    rw [← hid]
    exact Scheme.fromSpecStalk_closedPoint
  have hloc : IsLocalHom (CommRingCat.Hom.hom (𝟙 (X.presheaf.stalk x))) := by
    rw [CommRingCat.hom_id]
    infer_instance
  have hinv : (stalkClosedPointIso (X.presheaf.stalk x)).inv =
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
        (Spec (X.presheaf.stalk x)).presheaf.germ ⊤
          (IsLocalRing.closedPoint (X.presheaf.stalk x)) trivial := by
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv, Iso.inv_hom_id_assoc]
  rw [stalkHomAt_congr (X.fromSpecStalk x) (Spec.map (𝟙 (X.presheaf.stalk x)) ≫ X.fromSpecStalk x)
      hid (Scheme.fromSpecStalk_closedPoint (X := X) (x := x)) hpt,
    stalkHomAt_specMap_fromSpecStalk (𝟙 (X.presheaf.stalk x)) hloc hpt, hinv,
    CommRingCat.hom_id, RingHom.comp_id]

/-- **The structure map `R → 𝒪_{Z, z}` of a scheme over `Spec R` at a point over the closed
point factors through the map of local rings of `Spec R ⟶ X`,** for `R = 𝒪_{X, x}`: the germ at
`z` of the global section that `d` determines is the image of `d` under the map of local rings of
`Spec 𝒪_{X, x} ⟶ X` followed by that of `q`. -/
private theorem stalkHomAt_stalkHomAt_fromSpecStalk {X Z : Scheme.{u}} {x : X}
    (q : Z ⟶ Spec (X.presheaf.stalk x)) (z : Z)
    (hq : q z = IsLocalRing.closedPoint (X.presheaf.stalk x)) (d : X.presheaf.stalk x) :
    (q.stalkHomAt hq)
        ((X.fromSpecStalk x).stalkHomAt
          (Scheme.fromSpecStalk_closedPoint (X := X) (x := x)) d) =
      ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫ q.appTop ≫
        Z.presheaf.germ ⊤ z trivial).hom d := by
  have hgerm : ∀ (a b : Spec (X.presheaf.stalk x)) (hab : a = b)
      (hu : a ∈ (⊤ : (Spec (X.presheaf.stalk x)).Opens)),
      (Spec (X.presheaf.stalk x)).presheaf.germ ⊤ a hu ≫
          ((Spec (X.presheaf.stalk x)).presheaf.stalkCongr (.of_eq hab)).hom =
        (Spec (X.presheaf.stalk x)).presheaf.germ ⊤ b (hab ▸ hu) := by
    rintro a _ rfl hu
    simp
  have key : ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
        (Spec (X.presheaf.stalk x)).presheaf.germ ⊤
          (IsLocalRing.closedPoint (X.presheaf.stalk x)) trivial) ≫
      ((Spec (X.presheaf.stalk x)).presheaf.stalkCongr (.of_eq hq.symm)).hom ≫
        q.stalkMap z =
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫ q.appTop ≫
        Z.presheaf.germ ⊤ z trivial := by
    rw [Category.assoc, ← Category.assoc ((Spec (X.presheaf.stalk x)).presheaf.germ ⊤
        (IsLocalRing.closedPoint (X.presheaf.stalk x)) trivial),
      hgerm _ _ hq.symm trivial, Scheme.Hom.germ_stalkMap q ⊤ z trivial]
    simp only [Scheme.Hom.preimage_top]
  rw [stalkHomAt_fromSpecStalk]
  exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp key) d

/-- **A base change along a morphism out of a scheme is a base change along the spectrum of one
of its local rings, after one further base change.** Let `g : Y ⟶ T` and `τ : V ⟶ T`, let `v` be
a point of `V` and write `c = V.fromSpecStalk v` for the canonical morphism
`Spec 𝒪_{V, v} ⟶ V`. Every point `z` of `Y ×_{T, c ≫ τ} Spec 𝒪_{V, v}` lying over a point `y`
of `Y` and over the closed point of `Spec 𝒪_{V, v}` determines a point `(y, v)` of
`Y ×_{T, τ} V` lying over `y` and over `v`, at which the two schemes have *isomorphic local
rings*, compatibly with the two maps out of `𝒪_{Y, y}`.

This is the replacement of `V` by `Spec 𝒪_{V, v}` which lets
`StacksDraft.ArtinApproximation.exists_truncationEquiv_stalk_pullback_fromSpecStalk` — stated for
base changes along the spectra of two *local rings* — be read at `Y ×_{T, τ} V`.

The proof is the pasting isomorphism
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`, which identifies
`Y ×_{T, c ≫ τ} Spec 𝒪_{V, v}` with `(Y ×_{T, τ} V) ×_V Spec 𝒪_{V, v}`, followed by
`AlgebraicGeometry.isIso_stalkMap_of_flat_isPreimmersion`: the first projection of the latter is
a base change of the flat preimmersion `c`, hence an isomorphism on every local ring. -/
theorem exists_point_ringEquiv_stalk_pullback_fromSpecStalk_comp
    {T Y V : Scheme.{u}} (g : Y ⟶ T) (τ : V ⟶ T) (v : V) (y : Y)
    (z : (pullback g (V.fromSpecStalk v ≫ τ) : Scheme.{u}))
    (hy : pullback.fst g (V.fromSpecStalk v ≫ τ) z = y)
    (hv : pullback.snd g (V.fromSpecStalk v ≫ τ) z =
      IsLocalRing.closedPoint (V.presheaf.stalk v)) :
    ∃ (yτ : (pullback g τ : Scheme.{u})) (hyτ : pullback.fst g τ yτ = y)
      (hsnd : pullback.snd g τ yτ = v),
      ∃ e : ((pullback g (V.fromSpecStalk v ≫ τ) : Scheme.{u}).presheaf.stalk z) ≃+*
          ((pullback g τ : Scheme.{u}).presheaf.stalk yτ),
        (∀ d : V.presheaf.stalk v,
            e (((Scheme.ΓSpecIso (V.presheaf.stalk v)).inv ≫
                (pullback.snd g (V.fromSpecStalk v ≫ τ)).appTop ≫
                  (pullback g (V.fromSpecStalk v ≫ τ) : Scheme.{u}).presheaf.germ ⊤ z
                    trivial).hom d) =
              (pullback.snd g τ).stalkHomAt hsnd d) ∧
        ∀ a : Y.presheaf.stalk y,
          e ((pullback.fst g (V.fromSpecStalk v ≫ τ)).stalkHomAt hy a) =
            (pullback.fst g τ).stalkHomAt hyτ a := by
  -- The pasting isomorphism identifies `Y ×_{T, c ≫ τ} Spec 𝒪_{V, v}` with
  -- `(Y ×_{T, τ} V) ×_V Spec 𝒪_{V, v}`; let `m` be the resulting morphism to `Y ×_{T, τ} V`.
  obtain ⟨m, hm⟩ : ∃ m : (pullback g (V.fromSpecStalk v ≫ τ) : Scheme.{u}) ⟶
      (pullback g τ : Scheme.{u}),
      m = (pullbackLeftPullbackSndIso g τ (V.fromSpecStalk v)).inv ≫
        pullback.fst (pullback.snd g τ) (V.fromSpecStalk v) := ⟨_, rfl⟩
  have hsq : IsPullback (pullback.snd (pullback.snd g τ) (V.fromSpecStalk v))
      (pullback.fst (pullback.snd g τ) (V.fromSpecStalk v))
      (V.fromSpecStalk v) (pullback.snd g τ) :=
    (IsPullback.of_hasPullback (pullback.snd g τ) (V.fromSpecStalk v)).flip
  have : Flat (V.fromSpecStalk v) := flat_fromSpecStalk V v
  have : Flat (pullback.fst (pullback.snd g τ) (V.fromSpecStalk v)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : IsPreimmersion (pullback.fst (pullback.snd g τ) (V.fromSpecStalk v)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : Flat m := by
    rw [hm]
    infer_instance
  have : IsPreimmersion m := by
    rw [hm]
    infer_instance
  -- composed with the projection to `Y` it is the projection to `Y` of the outer base change
  have hmfst : m ≫ pullback.fst g τ = pullback.fst g (V.fromSpecStalk v ≫ τ) := by
    rw [hm, Category.assoc]
    exact pullbackLeftPullbackSndIso_inv_fst g τ (V.fromSpecStalk v)
  -- and composed with the projection to `V` it is the projection to `Spec 𝒪_{V, v}` followed
  -- by the canonical morphism `Spec 𝒪_{V, v} ⟶ V`
  have hmsnd : m ≫ pullback.snd g τ =
      pullback.snd g (V.fromSpecStalk v ≫ τ) ≫ V.fromSpecStalk v := by
    have hcond : pullback.fst (pullback.snd g τ) (V.fromSpecStalk v) ≫ pullback.snd g τ =
        pullback.snd (pullback.snd g τ) (V.fromSpecStalk v) ≫ V.fromSpecStalk v :=
      pullback.condition
    rw [hm, Category.assoc, hcond, ← Category.assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd g τ (V.fromSpecStalk v)]
  have hyτ : pullback.fst g τ (m z) = y := by rwa [← Scheme.Hom.comp_apply, hmfst]
  have hsnd : pullback.snd g τ (m z) = v := by
    rw [← Scheme.Hom.comp_apply, hmsnd, Scheme.Hom.comp_apply, hv]
    exact Scheme.fromSpecStalk_closedPoint
  have : IsIso (m.stalkMap z) := isIso_stalkMap_of_flat_isPreimmersion m z
  have hbij : Function.Bijective (m.stalkMap z).hom :=
    ConcreteCategory.bijective_of_isIso (m.stalkMap z)
  -- the two maps of local rings that `m` carries, read factor by factor
  have key := stalkMap_comp_stalkHomAt m (pullback.fst g τ) _ hmfst hyτ hy
  have key₂ := (stalkMap_comp_stalkHomAt m (pullback.snd g τ) _ hmsnd hsnd
    (by rw [← hmsnd]; exact hsnd)).trans (Scheme.Hom.stalkHomAt_comp _ _ hv
      (Scheme.fromSpecStalk_closedPoint (X := V) (x := v)))
  refine ⟨m z, hyτ, hsnd, (RingEquiv.ofBijective _ hbij).symm, fun d => ?_, fun a => ?_⟩
  · -- the base-side compatibility: both sides are the germ at `z` of the global section of
    -- `Y ×_{T, c ≫ τ} Spec 𝒪_{V, v}` that `d` determines
    rw [RingEquiv.symm_apply_eq]
    exact ((RingHom.congr_fun key₂ d).trans
      (stalkHomAt_stalkHomAt_fromSpecStalk
        (pullback.snd g (V.fromSpecStalk v ≫ τ)) z hv d)).symm
  · rw [RingEquiv.symm_apply_eq]
    exact (RingHom.congr_fun key a).symm

/-- **One side's comparison of truncated local rings with the base change along `Spec Λ`.** Let
`f : Z ⟶ Spec D` with `D` local, let `D → Λ` be surjective with kernel `𝔪_D ^ N`, and let `w` be
a point of `Z ×_{Spec D} Spec Λ` whose image in `Z` lies over the closed point of `Spec D`. Then
the truncated local ring of `Z` at that image and the truncated local ring of the base change at
`w` are isomorphic, by the map on local rings induced by the first projection.

This is `AlgebraicGeometry.exists_ringEquiv_quotient_maximalIdeal_pow_stalk_pullback_of_surjective`
with its hypothesis on the extended kernel discharged: the structure map `D → 𝒪_{Z, p}` is local
by `AlgebraicGeometry.isLocalHom_algebraMap_stalk_of_eq_closedPoint`, so it carries `𝔪_D ^ N`
into `𝔪_p ^ N`. -/
private theorem exists_truncationEquiv_stalk_pullback_of_ker_eq
    (D Λ : Type u) [CommRing D] [CommRing Λ] [Algebra D Λ] [IsLocalRing D] (N : ℕ) (hN : 1 ≤ N)
    (hsurj : Function.Surjective (algebraMap D Λ))
    (hker : RingHom.ker (algebraMap D Λ) = maximalIdeal D ^ N)
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of D))
    (g : Spec (CommRingCat.of Λ) ⟶ Spec (CommRingCat.of D))
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap D Λ)))
    (w : (pullback f g : Scheme.{u}))
    (hcp : f (pullback.fst f g w) = IsLocalRing.closedPoint D) :
    ∃ e : (Z.presheaf.stalk (pullback.fst f g w) ⧸
          maximalIdeal (Z.presheaf.stalk (pullback.fst f g w)) ^ N) ≃+*
        ((pullback f g : Scheme.{u}).presheaf.stalk w ⧸
          maximalIdeal ((pullback f g : Scheme.{u}).presheaf.stalk w) ^ N),
      ∀ b : Z.presheaf.stalk (pullback.fst f g w),
        e (Ideal.Quotient.mk _ b) =
          Ideal.Quotient.mk _ (((pullback.fst f g).stalkMap w).hom b) :=
  exists_ringEquiv_quotient_maximalIdeal_pow_stalk_pullback_of_surjective D Λ hsurj Z f g hg w
    N hN (by
      let := isLocalHom_algebraMap_stalk_of_eq_closedPoint D Z f (pullback.fst f g w) hcp
      rw [hker, Ideal.map_pow]
      exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) N)

/-- **Two base changes along two surjections onto one and the same truncated base have the same
truncated local rings.** Let `p : Y ⟶ T`, let `D₁`, `D₂` be local rings with morphisms
`b_i : Spec D_i ⟶ T`, and let `Λ` be a local ring that is a quotient of both `D₁` and `D₂` with
kernel the `N`-th power of the maximal ideal, in such a way that the two composites
`Spec Λ ⟶ Spec D_i ⟶ T` agree. Then every point `y₁` of `Y ×_{T, b₁} Spec D₁` over `y` and over
the closed point of `Spec D₁` gives a point `y₂` of `Y ×_{T, b₂} Spec D₂` over `y` and over the
closed point of `Spec D₂`, and an isomorphism of the two truncated local rings compatible both
with the two maps out of `𝒪_{Y, y}` and with the two structure maps of the base.

Both sides are compared with the base change of `p` along `Spec Λ ⟶ T`, which the agreement of
the two composites makes a base change of *both*; the comparison of each side with it is
`StacksDraft.ArtinApproximation.exists_truncationEquiv_stalk_pullback_of_ker_eq`, and the two are
transported onto one another by
`StacksDraft.ArtinApproximation.exists_truncationEquiv_of_iso`. -/
private theorem exists_truncationEquiv_stalk_pullback_of_surjections
    {T Y : Scheme.{u}} (p : Y ⟶ T) (N : ℕ) (hN : 1 ≤ N)
    (D₁ D₂ Λ : Type u) [CommRing D₁] [CommRing D₂] [CommRing Λ]
    [IsLocalRing D₁] [IsLocalRing D₂] [IsLocalRing Λ] [Algebra D₁ Λ] [Algebra D₂ Λ]
    (hs₁ : Function.Surjective (algebraMap D₁ Λ))
    (hs₂ : Function.Surjective (algebraMap D₂ Λ))
    (hker₁ : RingHom.ker (algebraMap D₁ Λ) = maximalIdeal D₁ ^ N)
    (hker₂ : RingHom.ker (algebraMap D₂ Λ) = maximalIdeal D₂ ^ N)
    (b₁ : Spec (CommRingCat.of D₁) ⟶ T) (b₂ : Spec (CommRingCat.of D₂) ⟶ T)
    (g₁ : Spec (CommRingCat.of Λ) ⟶ Spec (CommRingCat.of D₁))
    (hg₁ : g₁ = Spec.map (CommRingCat.ofHom (algebraMap D₁ Λ)))
    (g₂ : Spec (CommRingCat.of Λ) ⟶ Spec (CommRingCat.of D₂))
    (hg₂ : g₂ = Spec.map (CommRingCat.ofHom (algebraMap D₂ Λ)))
    (hgb : g₁ ≫ b₁ = g₂ ≫ b₂)
    (y : Y) (y₁ : (pullback p b₁ : Scheme.{u}))
    (hy₁ : pullback.fst p b₁ y₁ = y)
    (hv₁ : pullback.snd p b₁ y₁ = IsLocalRing.closedPoint D₁) :
    ∃ (y₂ : (pullback p b₂ : Scheme.{u})) (hy₂ : pullback.fst p b₂ y₂ = y),
      pullback.snd p b₂ y₂ = IsLocalRing.closedPoint D₂ ∧
      ∃ e : ((pullback p b₁ : Scheme.{u}).presheaf.stalk y₁ ⧸
            maximalIdeal ((pullback p b₁ : Scheme.{u}).presheaf.stalk y₁) ^ N) ≃+*
          ((pullback p b₂ : Scheme.{u}).presheaf.stalk y₂ ⧸
            maximalIdeal ((pullback p b₂ : Scheme.{u}).presheaf.stalk y₂) ^ N),
        (∀ (d₁ : D₁) (d₂ : D₂),
            algebraMap D₁ Λ d₁ = algebraMap D₂ Λ d₂ →
            e (Ideal.Quotient.mk _ (((Scheme.ΓSpecIso (CommRingCat.of D₁)).inv ≫
                (pullback.snd p b₁).appTop ≫
                  (pullback p b₁ : Scheme.{u}).presheaf.germ ⊤ y₁ trivial).hom d₁)) =
              Ideal.Quotient.mk _ (((Scheme.ΓSpecIso (CommRingCat.of D₂)).inv ≫
                (pullback.snd p b₂).appTop ≫
                  (pullback p b₂ : Scheme.{u}).presheaf.germ ⊤ y₂ trivial).hom d₂)) ∧
        ∀ a : Y.presheaf.stalk y,
          e (Ideal.Quotient.mk _ ((pullback.fst p b₁).stalkHomAt hy₁ a)) =
            Ideal.Quotient.mk _ ((pullback.fst p b₂).stalkHomAt hy₂ a) := by
  let : IsLocalHom (algebraMap D₁ Λ) := IsLocalHom.of_surjective _ hs₁
  let : IsLocalHom (algebraMap D₂ Λ) := IsLocalHom.of_surjective _ hs₂
  -- The two identifications with the common base change `Y ×_T Spec Λ`.
  obtain ⟨Φ, hfstΦ, hsndΦ⟩ := exists_iso_pullback_snd_of_comp_eq p b₁ b₂ g₁ g₂ hgb
  -- A point of the common base change over `y₁`.
  have hg₁cp : g₁ (IsLocalRing.closedPoint Λ) = IsLocalRing.closedPoint D₁ := by
    rw [hg₁]
    exact IsLocalRing.comap_closedPoint (algebraMap D₁ Λ)
  have hg₂cp : g₂ (IsLocalRing.closedPoint Λ) = IsLocalRing.closedPoint D₂ := by
    rw [hg₂]
    exact IsLocalRing.comap_closedPoint (algebraMap D₂ Λ)
  obtain ⟨w₁, hw₁fst, hw₁snd⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd p b₁) (g := g₁) y₁ (IsLocalRing.closedPoint Λ) (hv₁.trans hg₁cp.symm)
  subst hw₁fst
  -- the corresponding point on the other side
  have hsnd₂ : pullback.snd (pullback.snd p b₂) g₂ (Φ.hom w₁) = IsLocalRing.closedPoint Λ := by
    rw [← Scheme.Hom.comp_apply, hsndΦ]
    exact hw₁snd
  have hfst₂ : pullback.fst p b₂ (pullback.fst (pullback.snd p b₂) g₂ (Φ.hom w₁)) = y := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hfstΦ, Scheme.Hom.comp_apply]
    exact hy₁
  have hv₂ : pullback.snd p b₂ (pullback.fst (pullback.snd p b₂) g₂ (Φ.hom w₁)) =
      IsLocalRing.closedPoint D₂ := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hsnd₂]
    exact hg₂cp
  -- the two comparisons of truncated local rings with the common base change
  obtain ⟨e₁, he₁⟩ := exists_truncationEquiv_stalk_pullback_of_ker_eq
    D₁ Λ N hN hs₁ hker₁ (pullback.snd p b₁) g₁ hg₁ w₁ hv₁
  obtain ⟨e₂, he₂⟩ := exists_truncationEquiv_stalk_pullback_of_ker_eq
    D₂ Λ N hN hs₂ hker₂ (pullback.snd p b₂) g₂ hg₂ (Φ.hom w₁) hv₂
  -- transport the two comparisons along the isomorphism of the two common base changes
  obtain ⟨e, hgen, ha⟩ :=
    exists_truncationEquiv_of_iso N (pullback.fst (pullback.snd p b₁) g₁)
      (pullback.fst (pullback.snd p b₂) g₂) (pullback.fst p b₁) (pullback.fst p b₂)
      Φ w₁ hy₁ hfst₂ hfstΦ e₁ he₁ e₂ he₂
  -- The base-side compatibility: both structure maps land on the germ at `w₁` of the global
  -- section of the common base change that the common image in `Λ` determines.
  exact ⟨pullback.fst (pullback.snd p b₂) g₂ (Φ.hom w₁), hfst₂, hv₂, e,
    fun d₁ d₂ hd => hgen _ _ (stalkMap_fst_germ_appTop_eq_of_algebraMap_eq
      (pullback.snd p b₁) (pullback.snd p b₂) g₁ hg₁ g₂ hg₂ Φ hsndΦ w₁ d₁ d₂ hd), ha⟩

/-- **The `Y`-level half of the bridge that clause (5) of Stacks Tag 0CAW cites.** Let
`p : Y ⟶ T`, let `t` be a point of `T`, let `D₁` and `D₂` be local rings and
`σ₁ : 𝒪_{T, t} → D₁`, `σ₂ : 𝒪_{T, t} → D₂` local homomorphisms, with
`b_i : Spec D_i ⟶ T` the induced morphisms through `Spec 𝒪_{T, t} ⟶ T`. Let `N ≥ 1` and let
`ε : D₁ / 𝔪₁ ^ N ≅ D₂ / 𝔪₂ ^ N` be a ring isomorphism carrying the class of `σ₁ c` to the class
of `σ₂ c` for every `c`. Then for every point `y₁` of `Y ×_{T, b₁} Spec D₁` over a point `y` of
`Y` and over the closed point of `Spec D₁` there are a point `y₂` of `Y ×_{T, b₂} Spec D₂` over
the same `y` and over the closed point of `Spec D₂`, and a ring isomorphism of the two truncated
local rings compatible with the two maps out of `𝒪_{Y, y}` **and with the two structure maps of
the base**: elements `d₁` of `D₁` and `d₂` of `D₂` that `ε` identifies have germs at `y₁` and at
`y₂` with the same class.

Both sides are compared with the base change of `p` along `Spec (D₂ / 𝔪₂ ^ N) ⟶ T`, which the
hypothesis on `ε` makes a base change of *both*; the comparison is
`StacksDraft.ArtinApproximation.exists_truncationEquiv_stalk_pullback_of_surjections` at
`Λ = D₂ / 𝔪₂ ^ N`, whose two surjections are `ε` composed with the quotient map, and the quotient
map.

The base-side compatibility is what makes the isomorphism canonical enough for clause (5) of Tag
0CAW: together with the compatibility over `𝒪_{Y, y}` it pins the isomorphism down on the images
of `𝒪_{Y, y}` and of the base, which generate the local ring of a base change. -/
theorem exists_truncationEquiv_stalk_pullback_fromSpecStalk
    {T Y : Scheme.{u}} (p : Y ⟶ T) (t : T) (N : ℕ) (hN : 1 ≤ N)
    (D₁ D₂ : Type u) [CommRing D₁] [CommRing D₂] [IsLocalRing D₁] [IsLocalRing D₂]
    (σ₁ : T.presheaf.stalk t →+* D₁) (σ₂ : T.presheaf.stalk t →+* D₂)
    (b₁ : Spec (CommRingCat.of D₁) ⟶ T)
    (hb₁ : b₁ = Spec.map (CommRingCat.ofHom σ₁) ≫ T.fromSpecStalk t)
    (b₂ : Spec (CommRingCat.of D₂) ⟶ T)
    (hb₂ : b₂ = Spec.map (CommRingCat.ofHom σ₂) ≫ T.fromSpecStalk t)
    (ε : (D₁ ⧸ maximalIdeal D₁ ^ N) ≃+* (D₂ ⧸ maximalIdeal D₂ ^ N))
    (hε : ∀ c : T.presheaf.stalk t,
      ε (Ideal.Quotient.mk _ (σ₁ c)) = Ideal.Quotient.mk _ (σ₂ c))
    (y : Y) (y₁ : (pullback p b₁ : Scheme.{u}))
    (hy₁ : pullback.fst p b₁ y₁ = y)
    (hv₁ : pullback.snd p b₁ y₁ = IsLocalRing.closedPoint D₁) :
    ∃ (y₂ : (pullback p b₂ : Scheme.{u})) (hy₂ : pullback.fst p b₂ y₂ = y),
      pullback.snd p b₂ y₂ = IsLocalRing.closedPoint D₂ ∧
      ∃ e : ((pullback p b₁ : Scheme.{u}).presheaf.stalk y₁ ⧸
            maximalIdeal ((pullback p b₁ : Scheme.{u}).presheaf.stalk y₁) ^ N) ≃+*
          ((pullback p b₂ : Scheme.{u}).presheaf.stalk y₂ ⧸
            maximalIdeal ((pullback p b₂ : Scheme.{u}).presheaf.stalk y₂) ^ N),
        (∀ (d₁ : D₁) (d₂ : D₂),
            ε (Ideal.Quotient.mk _ d₁) = Ideal.Quotient.mk _ d₂ →
            e (Ideal.Quotient.mk _ (((Scheme.ΓSpecIso (CommRingCat.of D₁)).inv ≫
                (pullback.snd p b₁).appTop ≫
                  (pullback p b₁ : Scheme.{u}).presheaf.germ ⊤ y₁ trivial).hom d₁)) =
              Ideal.Quotient.mk _ (((Scheme.ΓSpecIso (CommRingCat.of D₂)).inv ≫
                (pullback.snd p b₂).appTop ≫
                  (pullback p b₂ : Scheme.{u}).presheaf.germ ⊤ y₂ trivial).hom d₂)) ∧
        ∀ a : Y.presheaf.stalk y,
          e (Ideal.Quotient.mk _ ((pullback.fst p b₁).stalkHomAt hy₁ a)) =
            Ideal.Quotient.mk _ ((pullback.fst p b₂).stalkHomAt hy₂ a) := by
  -- The common truncated base `Λ`, with the two surjections onto it.
  have hmax₂ : maximalIdeal D₂ ^ N ≠ ⊤ := by
    intro h
    exact (maximalIdeal.isMaximal D₂).ne_top
      (top_le_iff.mp (h ▸ Ideal.pow_le_self (n := N) (by omega)))
  have hntΛ : Nontrivial (D₂ ⧸ maximalIdeal D₂ ^ N) := Ideal.Quotient.nontrivial_iff.mpr hmax₂
  let : IsLocalRing (D₂ ⧸ maximalIdeal D₂ ^ N) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  let algD₁ : Algebra D₁ (D₂ ⧸ maximalIdeal D₂ ^ N) :=
    ((ε : (D₁ ⧸ maximalIdeal D₁ ^ N) →+* (D₂ ⧸ maximalIdeal D₂ ^ N)).comp
      (Ideal.Quotient.mk (maximalIdeal D₁ ^ N))).toAlgebra
  have hs₁ : Function.Surjective (algebraMap D₁ (D₂ ⧸ maximalIdeal D₂ ^ N)) :=
    ε.surjective.comp Ideal.Quotient.mk_surjective
  have hs₂ : Function.Surjective (algebraMap D₂ (D₂ ⧸ maximalIdeal D₂ ^ N)) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  have hker₁ : RingHom.ker (algebraMap D₁ (D₂ ⧸ maximalIdeal D₂ ^ N)) =
      maximalIdeal D₁ ^ N := by
    refine Ideal.ext fun x => ?_
    rw [RingHom.mem_ker]
    show ε (Ideal.Quotient.mk (maximalIdeal D₁ ^ N) x) = 0 ↔ _
    rw [map_eq_zero_iff _ ε.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hker₂ : RingHom.ker (algebraMap D₂ (D₂ ⧸ maximalIdeal D₂ ^ N)) =
      maximalIdeal D₂ ^ N := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  -- The two composites `Spec Λ ⟶ Spec D_i ⟶ T` agree, by the hypothesis on `ε`.
  have hcomp : (algebraMap D₁ (D₂ ⧸ maximalIdeal D₂ ^ N)).comp σ₁ =
      (algebraMap D₂ (D₂ ⧸ maximalIdeal D₂ ^ N)).comp σ₂ := by
    refine RingHom.ext fun c => ?_
    rw [Ideal.Quotient.algebraMap_eq]
    exact hε c
  have hgb : Spec.map (CommRingCat.ofHom (algebraMap D₁ (D₂ ⧸ maximalIdeal D₂ ^ N))) ≫ b₁ =
      Spec.map (CommRingCat.ofHom (algebraMap D₂ (D₂ ⧸ maximalIdeal D₂ ^ N))) ≫ b₂ := by
    rw [hb₁, hb₂, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp]
  obtain ⟨y₂, hy₂, hv₂, e, hbase, ha⟩ :=
    exists_truncationEquiv_stalk_pullback_of_surjections p N hN D₁ D₂
      (D₂ ⧸ maximalIdeal D₂ ^ N) hs₁ hs₂ hker₁ hker₂ b₁ b₂ _ rfl _ rfl hgb y y₁ hy₁ hv₁
  refine ⟨y₂, hy₂, hv₂, e, fun d₁ d₂ hd => hbase d₁ d₂ ?_, ha⟩
  rw [show algebraMap D₁ (D₂ ⧸ maximalIdeal D₂ ^ N) d₁ = ε (Ideal.Quotient.mk _ d₁) from rfl,
    hd, Ideal.Quotient.algebraMap_eq]

/-- The canonical morphism out of the spectrum of a local ring followed by a morphism of schemes
is the spectrum of the induced map of local rings followed by the canonical morphism at the
image point. This is `AlgebraicGeometry.Scheme.SpecMap_stalkMap_fromSpecStalk` with the image
point named. -/
private theorem fromSpecStalk_comp_eq {V T : Scheme.{u}} (τ : V ⟶ T) {v : V} {t : T}
    (hτ : τ v = t) :
    V.fromSpecStalk v ≫ τ =
      Spec.map (CommRingCat.ofHom (τ.stalkHomAt hτ)) ≫ T.fromSpecStalk t := by
  subst hτ
  rw [stalkHomAt_rfl, CommRingCat.ofHom_hom]
  exact (Scheme.SpecMap_stalkMap_fromSpecStalk τ).symm

/-- **Clause (3) of Stacks Tag 0CAW read as an identification of the truncated bases.** The
congruence modulo `𝔪_v ^ N` between `σ` and `τ^♯_v` says precisely that the isomorphism
`𝒪^∧_{S, s}/𝔪̂_s ^ N ≅ 𝒪_{V, v}/𝔪_v ^ N` of the elementary étale neighbourhood `(V, v)` carries
the class of `σ c` to the class of `τ^♯_v c`, for every germ `c` of `𝒪_{T, t}`. -/
private theorem completedTruncationEquiv_mk_sigma {S T : Scheme.{u}} [IsLocallyNoetherian S]
    {s : S} {t : T} (N : ℕ)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (V : EtaleNeighborhood S s) (hV : V.IsElementary)
    (τ : V.scheme ⟶ T) (hτ : τ V.point = t)
    (hcong : ∀ a : T.presheaf.stalk t,
      V.completionMap (σ a) -
          algebraMap (V.scheme.presheaf.stalk V.point)
            (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
              (V.scheme.presheaf.stalk V.point)) (τ.stalkHomAt hτ a) ∈
        Ideal.map
          (algebraMap (V.scheme.presheaf.stalk V.point)
            (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
              (V.scheme.presheaf.stalk V.point)))
          (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N)) (c : T.presheaf.stalk t) :
    EtaleNeighborhood.completedTruncationEquiv V hV N (Ideal.Quotient.mk _ (σ c)) =
      Ideal.Quotient.mk _ (τ.stalkHomAt hτ c) := by
  have : IsLocallyNoetherian V.scheme := LocallyOfFiniteType.isLocallyNoetherian V.toBase
  have hgen : EtaleNeighborhood.completedTruncationEquiv V hV N (Ideal.Quotient.mk _ (σ c)) =
      completionQuotientEquiv (V.scheme.presheaf.stalk V.point) N
        (Ideal.Quotient.mk _ (V.completionMap (σ c))) := by
    simp only [EtaleNeighborhood.completedTruncationEquiv, EtaleNeighborhood.truncationEquiv,
      RingEquiv.trans_apply, RingEquiv.symm_apply_apply, Ideal.quotientEquiv_mk,
      EtaleNeighborhood.completionRingEquiv_apply]
  have hpow : Ideal.map
        (algebraMap (V.scheme.presheaf.stalk V.point)
          (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
            (V.scheme.presheaf.stalk V.point)))
        (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N) =
      maximalIdeal (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
        (V.scheme.presheaf.stalk V.point)) ^ N := by
    rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map]
  have hmk : (Ideal.Quotient.mk
        (maximalIdeal (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
          (V.scheme.presheaf.stalk V.point)) ^ N) (V.completionMap (σ c))) =
      Ideal.Quotient.mk _ (algebraMap (V.scheme.presheaf.stalk V.point)
        (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
          (V.scheme.presheaf.stalk V.point)) (τ.stalkHomAt hτ c)) := by
    rw [Ideal.Quotient.eq, ← hpow]
    exact hcong c
  rw [hgen, hmk, completionQuotientEquiv_mk]

/-- **The bridge that clause (5) of Stacks Tag 0CAW cites, at Tag 0CAW's own data.** Let
`p : Y ⟶ T`, let `s` be a point of a locally Noetherian scheme `S`, let `t` be a point of `T`,
let `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a ring homomorphism, let `(V, v)` be an elementary étale
neighbourhood of `(S, s)` and `τ : V ⟶ T` a morphism carrying `v` to `t` such that the square
of clause (3) commutes modulo `𝔪_v ^ N`. Then for every point `y_σ` of
`Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}` lying over a point `y` of `Y` and over the closed point there
are a point `(y, v)` of `Y ×_{T, τ} V` lying over `y` and over `v`, and a ring isomorphism

```
𝒪_{Y_σ, y_σ}/𝔪_{y_σ} ^ N  ≅  𝒪_{Y ×_{T, τ} V, (y, v)}/𝔪_{(y, v)} ^ N
```

compatible with the two maps out of `𝒪_{Y, y}`. This is the sentence of clause (5) that "`Y_σ`
and `Y ×_{T, τ} V` are canonically isomorphic over
`𝒪_{V, v}/𝔪_v ^ N = 𝒪_{S, s}/𝔪_s ^ N` by parts (2) and (3)", with part (2) entering through
`AlgebraicGeometry.EtaleNeighborhood.completedTruncationEquiv` and part (3) as the hypothesis
`hcong`.

*What pins the isomorphism down.* As in
`StacksDraft.ArtinApproximation.exists_truncationEquiv_stalk_pullback_fromSpecStalk`, two
compatibilities: with the two maps out of `𝒪_{Y, y}`, and with the two structure maps of the
base — a germ `l` of `𝒪^∧_{S, s}` and a germ `d` of `𝒪_{V, v}` that the truncation isomorphism
of clause (2) identifies have germs at `y_σ` and at `(y, v)` with the same class. Since
`𝒪_{Y_σ, y_σ}` is generated by the images of `𝒪_{Y, y}` and of `𝒪^∧_{S, s}`, the two clauses
together are what makes the identification canonical, which is how clause (5) of Tag 0CAW uses
it.

*What this does not do.* It is the input clause (5) of Tag 0CAW cites, not clauses (4) and (5):
those have to produce `V`, `τ`, `W` and `f` jointly from `σ` and `φ`, because a choice of `V` and
`τ` made without reference to `φ` can make clause (5) unsatisfiable. -/
theorem exists_truncationEquiv_stalk_relativeBaseChange
    {S T Y : Scheme.{u}} [IsLocallyNoetherian S] (p : Y ⟶ T) {s : S} {t : T}
    (N : ℕ) (hN : 1 ≤ N)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (V : EtaleNeighborhood S s) (hV : V.IsElementary)
    (τ : V.scheme ⟶ T) (hτ : τ V.point = t)
    (hcong : ∀ a : T.presheaf.stalk t,
      V.completionMap (σ a) -
          algebraMap (V.scheme.presheaf.stalk V.point)
            (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
              (V.scheme.presheaf.stalk V.point)) (τ.stalkHomAt hτ a) ∈
        Ideal.map
          (algebraMap (V.scheme.presheaf.stalk V.point)
            (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
              (V.scheme.presheaf.stalk V.point)))
          (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N))
    (b : Spec (CommRingCat.of (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s))) ⟶ T)
    (hb : b = Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t)
    (y : Y) (yσ : (pullback p b : Scheme.{u}))
    (hyσ : pullback.fst p b yσ = y)
    (hvσ : pullback.snd p b yσ =
      IsLocalRing.closedPoint
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))) :
    ∃ (yτ : (pullback p τ : Scheme.{u})) (hyτ : pullback.fst p τ yτ = y)
      (hsndτ : pullback.snd p τ yτ = V.point),
      ∃ e : ((pullback p b : Scheme.{u}).presheaf.stalk yσ ⧸
            maximalIdeal ((pullback p b : Scheme.{u}).presheaf.stalk yσ) ^ N) ≃+*
          ((pullback p τ : Scheme.{u}).presheaf.stalk yτ ⧸
            maximalIdeal ((pullback p τ : Scheme.{u}).presheaf.stalk yτ) ^ N),
        (∀ (l : AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
            (d : V.scheme.presheaf.stalk V.point),
            EtaleNeighborhood.completedTruncationEquiv V hV N (Ideal.Quotient.mk _ l) =
                Ideal.Quotient.mk _ d →
            e (Ideal.Quotient.mk _ (((Scheme.ΓSpecIso (CommRingCat.of
                  (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                    (S.presheaf.stalk s)))).inv ≫ (pullback.snd p b).appTop ≫
                (pullback p b : Scheme.{u}).presheaf.germ ⊤ yσ trivial).hom l)) =
              Ideal.Quotient.mk _ ((pullback.snd p τ).stalkHomAt hsndτ d)) ∧
        ∀ a : Y.presheaf.stalk y,
          e (Ideal.Quotient.mk _ ((pullback.fst p b).stalkHomAt hyσ a)) =
            Ideal.Quotient.mk _ ((pullback.fst p τ).stalkHomAt hyτ a) := by
  -- Compare `Y_σ` with the base change along `Spec 𝒪_{V, v} ⟶ V ⟶ T`.
  obtain ⟨y₂, hy₂, hv₂, e₁, hbase₁, he₁⟩ :=
    exists_truncationEquiv_stalk_pullback_fromSpecStalk p t N hN
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
      (V.scheme.presheaf.stalk V.point) σ (τ.stalkHomAt hτ) b hb
      (V.scheme.fromSpecStalk V.point ≫ τ) (fromSpecStalk_comp_eq τ hτ)
      (EtaleNeighborhood.completedTruncationEquiv V hV N)
      (completedTruncationEquiv_mk_sigma N σ V hV τ hτ hcong) y yσ hyσ hvσ
  -- Replace `Spec 𝒪_{V, v}` by `V`.
  obtain ⟨yτ, hyτ, hsndτ, e₂, hbase₂, he₂⟩ :=
    exists_point_ringEquiv_stalk_pullback_fromSpecStalk_comp p τ V.point y y₂ hy₂ hv₂
  -- Descend the isomorphism of local rings to the two truncations.
  have hmaxpow : maximalIdeal ((pullback p τ : Scheme.{u}).presheaf.stalk yτ) ^ N =
      Ideal.map (e₂ : ((pullback p (V.scheme.fromSpecStalk V.point ≫ τ) :
            Scheme.{u}).presheaf.stalk y₂) →+*
          ((pullback p τ : Scheme.{u}).presheaf.stalk yτ))
        (maximalIdeal ((pullback p (V.scheme.fromSpecStalk V.point ≫ τ) :
          Scheme.{u}).presheaf.stalk y₂) ^ N) := by
    rw [Ideal.map_pow]
    congr 1
    exact (map_maximalIdeal_eq_ringEquiv e₂).symm
  refine ⟨yτ, hyτ, hsndτ, e₁.trans (Ideal.quotientEquiv _ _ e₂ hmaxpow),
    fun l d hld => ?_, fun a => ?_⟩
  · rw [RingEquiv.trans_apply, hbase₁ l d hld, Ideal.quotientEquiv_mk]
    exact congrArg (Ideal.Quotient.mk _) (hbase₂ d)
  · rw [RingEquiv.trans_apply, he₁, Ideal.quotientEquiv_mk, he₂]

end StacksDraft.ArtinApproximation

end
