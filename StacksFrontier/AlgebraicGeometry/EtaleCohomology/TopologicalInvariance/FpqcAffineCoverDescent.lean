module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineDescentFpqc
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcEffectivity
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.CanonicalFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridge
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleDescentIntegral

/-!
# The descent step of the affine case of topological invariance

Let `f : X ⟶ Y` be a universal homeomorphism and `w : W ⟶ Y` a surjective quasi-compact étale
morphism. Let `V` be étale and affine over `W` and `U` étale over `X`, with the same base change
to `W ×_Y X`. Then `U` is the base change along `f` of a scheme étale over `Y`. This is the
descent step of the last paragraph of the second proof of Stacks Project, Tag 04DZ, over a
genuine fpqc covering.

The scheme `V` carries a descent datum relative to `W ⟶ Y`, whose gluing isomorphism over
`W ×_Y W` fixes the `U`-coordinate of a point of `V`; it is effective by affine fpqc descent, and
the descended scheme is the required scheme étale over `Y`.

The affine case of topological invariance itself, the essential surjectivity half of the
correspondence displayed as Stacks Project, Tag 04E0, and the equivalence of Tag 04DZ are
`Stacks.Etale.essSurjAffineEtalePullback`, `Stacks.Etale.affineEtalePullback_isEquivalence` and
`Stacks.Etale.etalePullback_isEquivalence` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective`, where
both tags are registered; they are proved there by a different descent step, and this file
registers neither.  Fed into
`Stacks.Etale.essSurjAffineEtalePullback_of_etaleDescentAlongFpqcAffineCover`, the theorem
here gives the same affine case a second time.

## Main definitions

* `Stacks.Etale.FpqcDescent.Setup`: The data of the descent step.
* `Stacks.Etale.FpqcDescent.Setup.act`: The action of a point of `W` on a point of `V`.
* `Stacks.Etale.FpqcDescent.Setup.datum`: The descent datum of `V` relative to `W ⟶ Y`.

## Main results

* `Stacks.Etale.FpqcDescent.Setup.exists_descended`: `V` is the base change to `W` of a scheme
  étale over `Y`.
* `Stacks.Etale.FpqcDescent.Setup.exists_etale_pullback`: `U` is the base change along `f` of a
  scheme étale over `Y`.
* `Stacks.Etale.etaleDescentAlongFpqcAffineCover`: The statement
  `Stacks.Etale.EtaleDescentAlongFpqcAffineCover` holds.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale.FpqcDescent

open _root_.AlgebraicGeometry

/-- **The data of the descent step.** A universal homeomorphism `f : X ⟶ Y`, a surjective
quasi-compact étale `w : W ⟶ Y`, a presentation of `WX` as `W ×_Y X`, an étale `p : U ⟶ X`, an
étale affine `v : V ⟶ W`, and a scheme `T` presented simultaneously as `V ×_W WX` and as
`U ×_X WX` by squares sharing the projection `τ`. -/
structure Setup where
  /-- The source of the universal homeomorphism. -/
  X : Scheme.{u}
  /-- The target of the universal homeomorphism. -/
  Y : Scheme.{u}
  /-- The étale cover of the target. -/
  W : Scheme.{u}
  /-- The fibre product `W ×_Y X`. -/
  WX : Scheme.{u}
  /-- The étale scheme over `X` to be descended. -/
  U : Scheme.{u}
  /-- The étale affine scheme over `W` descending it over the cover. -/
  V : Scheme.{u}
  /-- The common base change of `U` and `V` to `W ×_Y X`. -/
  T : Scheme.{u}
  /-- The universal homeomorphism. -/
  f : X ⟶ Y
  /-- The étale cover of the target. -/
  w : W ⟶ Y
  /-- The projection of `W ×_Y X` to `W`. -/
  πW : WX ⟶ W
  /-- The projection of `W ×_Y X` to `X`. -/
  πX : WX ⟶ X
  /-- The structure morphism of `U`. -/
  p : U ⟶ X
  /-- The structure morphism of `V`. -/
  v : V ⟶ W
  /-- The projection of `T` to `V`. -/
  aV : T ⟶ V
  /-- The projection of `T` to `W ×_Y X`. -/
  τ : T ⟶ WX
  /-- The projection of `T` to `U`. -/
  bU : T ⟶ U
  /-- `f` is a universal homeomorphism. -/
  hf : UniversalHomeomorphism f
  /-- `w` is étale. -/
  hw : Etale w
  /-- `w` is surjective. -/
  hwsurj : Surjective w
  /-- `w` is quasi-compact. -/
  hwqc : QuasiCompact w
  /-- `p` is étale. -/
  hp : Etale p
  /-- `v` is étale. -/
  hv : Etale v
  /-- `v` is affine. -/
  hvaff : IsAffineHom v
  /-- `WX` is `W ×_Y X`. -/
  hWX : IsPullback πW πX w f
  /-- `T` is `V ×_W WX`. -/
  hV : IsPullback aV τ v πW
  /-- `T` is `U ×_X WX`. -/
  hU : IsPullback bU τ p πX

namespace Setup

variable (S : Setup.{u})

/-- `f` is a universal homeomorphism. -/
instance : UniversalHomeomorphism S.f := S.hf
/-- `w` is étale. -/
instance : Etale S.w := S.hw
/-- `w` is surjective. -/
instance : Surjective S.w := S.hwsurj
/-- `w` is quasi-compact. -/
instance : QuasiCompact S.w := S.hwqc
/-- `p` is étale. -/
instance : Etale S.p := S.hp
/-- `v` is étale. -/
instance : Etale S.v := S.hv
/-- `v` is affine. -/
instance : IsAffineHom S.v := S.hvaff

/-- `w` is flat. -/
instance : Flat S.w := inferInstance
/-- The composite `v ≫ w` is étale. -/
instance : Etale (S.v ≫ S.w) := inferInstance

/-! ### The two presentations of `T` over `Y` -/

/-- `T` is the fibre product of `V` and `X` over `Y`. -/
theorem isPullback_V : IsPullback S.aV (S.τ ≫ S.πX) (S.v ≫ S.w) S.f := S.hV.paste_vert S.hWX

/-- `T` is the fibre product of `U` and `W` over `Y`. -/
theorem isPullback_U : IsPullback S.bU (S.τ ≫ S.πW) (S.p ≫ S.f) S.w :=
  S.hU.paste_vert S.hWX.flip

/-- The structure morphism of `T` over `Y`, computed through `V`. -/
lemma aV_comp : S.aV ≫ S.v ≫ S.w = S.τ ≫ S.πX ≫ S.f := by
  rw [← Category.assoc, S.hV.w, Category.assoc, S.hWX.w]

/-! ### Base change along the universal homeomorphism -/

/-- The base change of `f` along a morphism `g : Z ⟶ Y` is a universal homeomorphism. -/
theorem universalHomeomorphism_pullbackFst {Z : Scheme.{u}} (g : Z ⟶ S.Y) :
    UniversalHomeomorphism (pullback.fst g S.f) :=
  universalHomeomorphism_of_isPullback (IsPullback.of_hasPullback g S.f)

/-- The base change of `f` along a morphism `g : Z ⟶ Y` is surjective on points. -/
theorem surjective_pullbackFst {Z : Scheme.{u}} (g : Z ⟶ S.Y) :
    Function.Surjective (pullback.fst g S.f).base :=
  have := S.universalHomeomorphism_pullbackFst g
  (surjective_of_universalHomeomorphism' (pullback.fst g S.f)).surj

/-- The base change of `f` along a morphism `g : Z ⟶ Y` is injective on points. -/
theorem injective_pullbackFst {Z : Scheme.{u}} (g : Z ⟶ S.Y) :
    Function.Injective (pullback.fst g S.f).base :=
  have := S.universalHomeomorphism_pullbackFst g
  (UniversalHomeomorphism.universally_isHomeomorph _ _ _ IsPullback.of_id_snd).injective

/-- The base change along `f` of a morphism of schemes over `Y`. -/
def baseMap {Z Z' : Scheme.{u}} (g : Z ⟶ S.Y) (k : Z' ⟶ Z) :
    (pullback (k ≫ g) S.f : Scheme.{u}) ⟶ (pullback g S.f : Scheme.{u}) :=
  pullback.lift (pullback.fst (k ≫ g) S.f ≫ k) (pullback.snd (k ≫ g) S.f)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The first projection of `baseMap g k` is `k` on the first factor. -/
@[simp]
lemma baseMap_comp_fst {Z Z' : Scheme.{u}} (g : Z ⟶ S.Y) (k : Z' ⟶ Z) :
    S.baseMap g k ≫ pullback.fst g S.f = pullback.fst (k ≫ g) S.f ≫ k :=
  pullback.lift_fst _ _ _

/-- `baseMap g k` commutes with the projections to `X`. -/
@[simp]
lemma baseMap_comp_snd {Z Z' : Scheme.{u}} (g : Z ⟶ S.Y) (k : Z' ⟶ Z) :
    S.baseMap g k ≫ pullback.snd g S.f = pullback.snd (k ≫ g) S.f :=
  pullback.lift_snd _ _ _

/-! ### The `U`-coordinate of a point of `V` -/

variable {Z Z' : Scheme.{u}}

/-- **The point of `T` named by a point of `V`.** Reading `T` as `V ×_Y X`, a point `a` of `V`
over `Z` and the canonical point of `X` on the base change `Z ×_Y X` name a point of `T`. -/
def tLift (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) :
    (pullback g S.f : Scheme.{u}) ⟶ S.T :=
  S.isPullback_V.lift (pullback.fst g S.f ≫ a) (pullback.snd g S.f)
    (by rw [Category.assoc, ha]; exact pullback.condition)

/-- The `V`-component of `tLift g a ha` is `a` read on `Z ×_Y X`. -/
@[simp]
lemma tLift_comp_aV (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) :
    S.tLift g a ha ≫ S.aV = pullback.fst g S.f ≫ a :=
  S.isPullback_V.lift_fst _ _ _

/-- The `X`-component of `tLift g a ha` is the canonical point of `X` on `Z ×_Y X`. -/
@[simp]
lemma tLift_comp_proj (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) :
    S.tLift g a ha ≫ (S.τ ≫ S.πX) = pullback.snd g S.f :=
  S.isPullback_V.lift_snd _ _ _

/-- **The `U`-coordinate of a point of `V`.** Reading `T` both as `V ×_Y X` and as `U ×_X W_X`,
a point of `V` over `Z` determines a point of `U` over the base change `Z ×_Y X`. -/
def uOf (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) :
    (pullback g S.f : Scheme.{u}) ⟶ S.U :=
  S.tLift g a ha ≫ S.bU

/-- The `U`-coordinate of a point of `V` lies over the canonical point of `X` on `Z ×_Y X`. -/
lemma uOf_comp_p (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) :
    S.uOf g a ha ≫ S.p = pullback.snd g S.f := by
  rw [uOf, Category.assoc, S.hU.w, tLift_comp_proj]

/-- The `T`-point named by a point of `V` is determined by its two coordinates. -/
lemma tLift_eq (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g)
    (t : (pullback g S.f : Scheme.{u}) ⟶ S.T) (ht₁ : t ≫ S.aV = pullback.fst g S.f ≫ a)
    (ht₂ : t ≫ (S.τ ≫ S.πX) = pullback.snd g S.f) : t = S.tLift g a ha :=
  S.isPullback_V.hom_ext (by rw [ht₁, tLift_comp_aV]) (by rw [ht₂, tLift_comp_proj])

/-- **A point of `V` is determined by its `U`-coordinate and the point of `W` it lies over.** -/
theorem hom_ext_of_uOf (g : Z ⟶ S.Y) (a a' : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g)
    (ha' : a' ≫ S.v ≫ S.w = g) (hu : S.uOf g a ha = S.uOf g a' ha')
    (hx : a ≫ S.v = a' ≫ S.v) : a = a' := by
  have hT : S.tLift g a ha = S.tLift g a' ha' := by
    refine S.isPullback_U.hom_ext hu ?_
    rw [← S.hV.w, ← Category.assoc, tLift_comp_aV, ← Category.assoc, tLift_comp_aV,
      Category.assoc, Category.assoc, hx]
  have hfst : pullback.fst g S.f ≫ a = pullback.fst g S.f ≫ a' := by
    rw [← S.tLift_comp_aV g a ha, ← S.tLift_comp_aV g a' ha', hT]
  exact hom_ext_of_surjective (pullback.fst g S.f) (S.surjective_pullbackFst g)
    (S.v ≫ S.w) a a' (ha.trans ha'.symm) hfst

/-! ### The transport of a `U`-coordinate to a prescribed point of `W` -/

/-- The point of `T = U ×_X W_X` named by a `U`-coordinate over `Z ×_Y X` and a point of `W`
over `Z`. -/
def tLift' (g : Z ⟶ S.Y) (c : (pullback g S.f : Scheme.{u}) ⟶ S.U)
    (hc : c ≫ S.p = pullback.snd g S.f) (x : Z ⟶ S.W) (hx : x ≫ S.w = g) :
    (pullback g S.f : Scheme.{u}) ⟶ S.T :=
  S.isPullback_U.lift c (pullback.fst g S.f ≫ x)
    (by rw [← Category.assoc, hc, Category.assoc, hx]; exact pullback.condition.symm)

/-- The `U`-component of `tLift' g c hc x hx` is `c`. -/
@[simp]
lemma tLift'_comp_bU (g : Z ⟶ S.Y) (c : (pullback g S.f : Scheme.{u}) ⟶ S.U)
    (hc : c ≫ S.p = pullback.snd g S.f) (x : Z ⟶ S.W) (hx : x ≫ S.w = g) :
    S.tLift' g c hc x hx ≫ S.bU = c :=
  S.isPullback_U.lift_fst _ _ _

/-- The `W`-component of `tLift' g c hc x hx` is `x` read on `Z ×_Y X`. -/
@[simp]
lemma tLift'_comp_proj (g : Z ⟶ S.Y) (c : (pullback g S.f : Scheme.{u}) ⟶ S.U)
    (hc : c ≫ S.p = pullback.snd g S.f) (x : Z ⟶ S.W) (hx : x ≫ S.w = g) :
    S.tLift' g c hc x hx ≫ (S.τ ≫ S.πW) = pullback.fst g S.f ≫ x :=
  S.isPullback_U.lift_snd _ _ _

/-- The `X`-component of `tLift' g c hc x hx` is the canonical point of `X` on `Z ×_Y X`. -/
lemma tLift'_comp_projX (g : Z ⟶ S.Y) (c : (pullback g S.f : Scheme.{u}) ⟶ S.U)
    (hc : c ≫ S.p = pullback.snd g S.f) (x : Z ⟶ S.W) (hx : x ≫ S.w = g) :
    S.tLift' g c hc x hx ≫ (S.τ ≫ S.πX) = pullback.snd g S.f := by
  rw [← S.hU.w, ← Category.assoc, tLift'_comp_bU, hc]

/-- There is a point `b` of `V` over `x` whose base change to `Z ×_Y X` is the `V`-component of
`tLift' g c hc x hx`. -/
lemma exists_actOf (g : Z ⟶ S.Y) (c : (pullback g S.f : Scheme.{u}) ⟶ S.U)
    (hc : c ≫ S.p = pullback.snd g S.f) (x : Z ⟶ S.W) (hx : x ≫ S.w = g) :
    ∃ b : Z ⟶ S.V, b ≫ S.v = x ∧
      pullback.fst g S.f ≫ b = S.tLift' g c hc x hx ≫ S.aV := by
  have hcomm : (S.tLift' g c hc x hx ≫ S.aV) ≫ (S.v ≫ S.w) = pullback.snd g S.f ≫ S.f := by
    rw [Category.assoc, S.aV_comp, ← Category.assoc S.τ, ← Category.assoc,
      S.tLift'_comp_projX g c hc x hx]
  obtain ⟨b, hb₁, hb₂⟩ := exists_hom_of_pullbackHom_of_universalHomeomorphism S.f g (S.v ≫ S.w)
    (pullback.lift (S.tLift' g c hc x hx ≫ S.aV) (pullback.snd g S.f) hcomm)
    (pullback.lift_snd _ _ _)
  rw [pullback.lift_fst] at hb₂
  refine ⟨b, ?_, hb₂⟩
  refine hom_ext_of_surjective (pullback.fst g S.f) (S.surjective_pullbackFst g)
    S.w (b ≫ S.v) x (by rw [Category.assoc, hb₁, hx]) ?_
  rw [← Category.assoc, hb₂, Category.assoc, S.hV.w, S.tLift'_comp_proj g c hc x hx]

/-- **The point of `V` with a prescribed `U`-coordinate lying over a prescribed point of `W`.** -/
def actOf (g : Z ⟶ S.Y) (c : (pullback g S.f : Scheme.{u}) ⟶ S.U)
    (hc : c ≫ S.p = pullback.snd g S.f) (x : Z ⟶ S.W) (hx : x ≫ S.w = g) : Z ⟶ S.V :=
  (S.exists_actOf g c hc x hx).choose

/-- `actOf g c hc x hx` lies over `x`. -/
lemma actOf_comp_v (g : Z ⟶ S.Y) (c : (pullback g S.f : Scheme.{u}) ⟶ S.U)
    (hc : c ≫ S.p = pullback.snd g S.f) (x : Z ⟶ S.W) (hx : x ≫ S.w = g) :
    S.actOf g c hc x hx ≫ S.v = x :=
  (S.exists_actOf g c hc x hx).choose_spec.1

/-- `actOf g c hc x hx` lies over `g`. -/
lemma actOf_comp_hom (g : Z ⟶ S.Y) (c : (pullback g S.f : Scheme.{u}) ⟶ S.U)
    (hc : c ≫ S.p = pullback.snd g S.f) (x : Z ⟶ S.W) (hx : x ≫ S.w = g) :
    S.actOf g c hc x hx ≫ S.v ≫ S.w = g := by
  rw [← Category.assoc, actOf_comp_v, hx]

/-- The `U`-coordinate of `actOf g c hc x hx` is `c`. -/
lemma uOf_actOf (g : Z ⟶ S.Y) (c : (pullback g S.f : Scheme.{u}) ⟶ S.U)
    (hc : c ≫ S.p = pullback.snd g S.f) (x : Z ⟶ S.W) (hx : x ≫ S.w = g) :
    S.uOf g (S.actOf g c hc x hx) (S.actOf_comp_hom g c hc x hx) = c := by
  rw [uOf, ← S.tLift_eq g _ (S.actOf_comp_hom g c hc x hx) (S.tLift' g c hc x hx)
    (S.exists_actOf g c hc x hx).choose_spec.2.symm (S.tLift'_comp_projX g c hc x hx),
    tLift'_comp_bU]

/-! ### The action of a point of `W` on a point of `V` -/

/-- **The action of a point of `W` on a point of `V`.** The point of `V` lying over `x` with the
same `U`-coordinate as `a`. -/
def act (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) (x : Z ⟶ S.W)
    (hx : x ≫ S.w = g) : Z ⟶ S.V :=
  S.actOf g (S.uOf g a ha) (S.uOf_comp_p g a ha) x hx

/-- `act g a ha x hx` lies over `x`. -/
lemma act_comp_v (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) (x : Z ⟶ S.W)
    (hx : x ≫ S.w = g) : S.act g a ha x hx ≫ S.v = x :=
  S.actOf_comp_v g _ _ x hx

/-- `act g a ha x hx` lies over `g`. -/
lemma act_comp_hom (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) (x : Z ⟶ S.W)
    (hx : x ≫ S.w = g) : S.act g a ha x hx ≫ S.v ≫ S.w = g :=
  S.actOf_comp_hom g _ _ x hx

/-- The action preserves the `U`-coordinate. -/
lemma uOf_act (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) (x : Z ⟶ S.W)
    (hx : x ≫ S.w = g) :
    S.uOf g (S.act g a ha x hx) (S.act_comp_hom g a ha x hx) = S.uOf g a ha :=
  S.uOf_actOf g _ _ x hx

/-- The action does not depend on the chosen name of the point of `Y` the two points lie
over. -/
lemma act_base_irrel (g g' : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g)
    (ha' : a ≫ S.v ≫ S.w = g') (x : Z ⟶ S.W) (hx : x ≫ S.w = g) (hx' : x ≫ S.w = g') :
    S.act g a ha x hx = S.act g' a ha' x hx' := by
  have hgg : g = g' := hx.symm.trans hx'
  subst hgg
  rfl

/-- **Acting by the point of `W` a point already lies over changes nothing.** -/
lemma act_self (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g)
    (hx : (a ≫ S.v) ≫ S.w = g) : S.act g a ha (a ≫ S.v) hx = a :=
  S.hom_ext_of_uOf g _ a (S.act_comp_hom g a ha _ hx) ha (S.uOf_act g a ha _ hx)
    (S.act_comp_v g a ha _ hx)

/-- **Acting twice is acting once.** -/
lemma act_act (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) (x : Z ⟶ S.W)
    (hx : x ≫ S.w = g) (y : Z ⟶ S.W) (hy : y ≫ S.w = g) :
    S.act g (S.act g a ha x hx) (S.act_comp_hom g a ha x hx) y hy = S.act g a ha y hy := by
  refine S.hom_ext_of_uOf g _ _
    (S.act_comp_hom g _ (S.act_comp_hom g a ha x hx) y hy) (S.act_comp_hom g a ha y hy) ?_ ?_
  · rw [uOf_act, uOf_act, uOf_act]
  · rw [act_comp_v, act_comp_v]

/-! ### Naturality in the test scheme -/

/-- The `U`-coordinate is natural in the test scheme `Z`. -/
lemma uOf_comp (g : Z ⟶ S.Y) (k : Z' ⟶ Z) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) :
    S.uOf (k ≫ g) (k ≫ a) (by rw [Category.assoc, ha]) = S.baseMap g k ≫ S.uOf g a ha := by
  rw [uOf, uOf, ← Category.assoc]
  congr 1
  refine (S.tLift_eq (k ≫ g) (k ≫ a) _ _ ?_ ?_).symm
  · rw [Category.assoc, tLift_comp_aV, ← Category.assoc, baseMap_comp_fst, Category.assoc]
  · rw [Category.assoc, tLift_comp_proj, baseMap_comp_snd]

/-- The action is natural in the test scheme `Z`. -/
lemma comp_act (g : Z ⟶ S.Y) (k : Z' ⟶ Z) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g)
    (x : Z ⟶ S.W) (hx : x ≫ S.w = g) :
    k ≫ S.act g a ha x hx =
      S.act (k ≫ g) (k ≫ a) (by rw [Category.assoc, ha]) (k ≫ x)
        (by rw [Category.assoc, hx]) := by
  refine S.hom_ext_of_uOf (k ≫ g) _ _ (by rw [Category.assoc, act_comp_hom])
    (S.act_comp_hom (k ≫ g) _ _ _ _) ?_ ?_
  · rw [S.uOf_comp g k _ (S.act_comp_hom g a ha x hx), uOf_act, uOf_act, S.uOf_comp g k a ha]
  · rw [Category.assoc, act_comp_v, act_comp_v]

/-- The action depends on its data only through the two points. -/
lemma act_congr {g g' : Z ⟶ S.Y} {a a' : Z ⟶ S.V} {x x' : Z ⟶ S.W}
    (ha : a ≫ S.v ≫ S.w = g) (ha' : a' ≫ S.v ≫ S.w = g') (hx : x ≫ S.w = g)
    (hx' : x' ≫ S.w = g') (hA : a = a') (hX : x = x') :
    S.act g a ha x hx = S.act g' a' ha' x' hx' := by
  subst hA
  subst hX
  exact S.act_base_irrel g g' a ha ha' x hx hx'

/-! ### The gluing isomorphism over `W ×_Y W` -/

/-- The universal point of `V` on `V ×_Y W`. -/
abbrev gfst : (pullback (S.v ≫ S.w) S.w : Scheme.{u}) ⟶ S.V := pullback.fst (S.v ≫ S.w) S.w

/-- The universal point of `W` on `V ×_Y W`. -/
abbrev gsnd : (pullback (S.v ≫ S.w) S.w : Scheme.{u}) ⟶ S.W := pullback.snd (S.v ≫ S.w) S.w

/-- The universal point of `W` on `W ×_Y V`. -/
abbrev hfst : (pullback S.w (S.v ≫ S.w) : Scheme.{u}) ⟶ S.W := pullback.fst S.w (S.v ≫ S.w)

/-- The universal point of `V` on `W ×_Y V`. -/
abbrev hsnd : (pullback S.w (S.v ≫ S.w) : Scheme.{u}) ⟶ S.V := pullback.snd S.w (S.v ≫ S.w)

/-- The two universal points on `V ×_Y W` lie over the same point of `Y`. -/
lemma gcond : S.gfst ≫ S.v ≫ S.w = S.gsnd ≫ S.w := pullback.condition

/-- The two universal points on `W ×_Y V` lie over the same point of `Y`. -/
lemma hcond : S.hsnd ≫ S.v ≫ S.w = S.hfst ≫ S.w := pullback.condition.symm

/-- **The gluing isomorphism over `W ×_Y W`, as a morphism `V ×_Y W ⟶ W ×_Y V`.** It carries the
universal pair `(a, x)` to the pair `(a ≫ v, a · x)`. -/
def gluingHom :
    (pullback (S.v ≫ S.w) S.w : Scheme.{u}) ⟶ (pullback S.w (S.v ≫ S.w) : Scheme.{u}) :=
  pullback.lift (S.gfst ≫ S.v) (S.act (S.gsnd ≫ S.w) S.gfst S.gcond S.gsnd rfl)
    (by rw [Category.assoc, S.gcond, S.act_comp_hom])

/-- The `W`-component of `gluingHom` is the image in `W` of the universal point of `V`. -/
@[simp]
lemma gluingHom_comp_fst : S.gluingHom ≫ S.hfst = S.gfst ≫ S.v := pullback.lift_fst _ _ _

/-- The `V`-component of `gluingHom` is the action of the universal point of `W` on the universal
point of `V`. -/
@[simp]
lemma gluingHom_comp_snd :
    S.gluingHom ≫ S.hsnd = S.act (S.gsnd ≫ S.w) S.gfst S.gcond S.gsnd rfl :=
  pullback.lift_snd _ _ _

/-- **The gluing isomorphism over `W ×_Y W`, the other way round.** It carries the universal pair
`(x, b)` to the pair `(b · x, b ≫ v)`. -/
def gluingInv :
    (pullback S.w (S.v ≫ S.w) : Scheme.{u}) ⟶ (pullback (S.v ≫ S.w) S.w : Scheme.{u}) :=
  pullback.lift (S.act (S.hfst ≫ S.w) S.hsnd S.hcond S.hfst rfl) (S.hsnd ≫ S.v)
    (by rw [S.act_comp_hom, Category.assoc, S.hcond])

/-- The `V`-component of `gluingInv` is the action of the universal point of `W` on the universal
point of `V`. -/
@[simp]
lemma gluingInv_comp_fst :
    S.gluingInv ≫ S.gfst = S.act (S.hfst ≫ S.w) S.hsnd S.hcond S.hfst rfl :=
  pullback.lift_fst _ _ _

/-- The `W`-component of `gluingInv` is the image in `W` of the universal point of `V`. -/
@[simp]
lemma gluingInv_comp_snd : S.gluingInv ≫ S.gsnd = S.hsnd ≫ S.v := pullback.lift_snd _ _ _

/-- Acting by the point of `W` that a point already lies over undoes an earlier action. -/
private lemma act_act_comp_v (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) (x : Z ⟶ S.W)
    (hx : x ≫ S.w = g) :
    S.act g (S.act g a ha x hx) (S.act_comp_hom g a ha x hx) (a ≫ S.v)
      ((Category.assoc _ _ _).trans ha) = a :=
  (S.act_act g a ha x hx _ _).trans (S.act_self g a ha _)

/-- `gluingInv` is a left inverse of `gluingHom`. -/
lemma gluingHom_comp_gluingInv : S.gluingHom ≫ S.gluingInv = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, gluingInv_comp_fst, S.comp_act (S.hfst ≫ S.w) S.gluingHom S.hsnd S.hcond
      S.hfst rfl, Category.id_comp]
    exact (S.act_congr _ _ _ _ S.gluingHom_comp_snd S.gluingHom_comp_fst).trans
      (S.act_act_comp_v (S.gsnd ≫ S.w) S.gfst S.gcond S.gsnd rfl)
  · rw [Category.assoc, gluingInv_comp_snd, Category.id_comp, ← Category.assoc,
      gluingHom_comp_snd, S.act_comp_v]

/-- `gluingInv` is a right inverse of `gluingHom`. -/
lemma gluingInv_comp_gluingHom : S.gluingInv ≫ S.gluingHom = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, gluingHom_comp_fst, Category.id_comp, ← Category.assoc,
      gluingInv_comp_fst, S.act_comp_v]
  · rw [Category.assoc, gluingHom_comp_snd, S.comp_act (S.gsnd ≫ S.w) S.gluingInv S.gfst S.gcond
      S.gsnd rfl, Category.id_comp]
    exact (S.act_congr _ _ _ _ S.gluingInv_comp_fst S.gluingInv_comp_snd).trans
      (S.act_act_comp_v (S.hfst ≫ S.w) S.hsnd S.hcond S.hfst rfl)

/-- **The gluing isomorphism over `W ×_Y W`.** -/
def gluingIso :
    (pullback (S.v ≫ S.w) S.w : Scheme.{u}) ≅ (pullback S.w (S.v ≫ S.w) : Scheme.{u}) where
  hom := S.gluingHom
  inv := S.gluingInv
  hom_inv_id := S.gluingHom_comp_gluingInv
  inv_hom_id := S.gluingInv_comp_gluingHom

/-- The forward morphism of `gluingIso` is `gluingHom`. -/
@[simp]
lemma gluingIso_hom : S.gluingIso.hom = S.gluingHom := rfl

/-! ### The gluing isomorphism satisfies the cocycle condition -/

/-- The isomorphism lies over the first factor of `W ×_Y W`. -/
lemma gluingIso_hom_fst :
    S.gluingIso.hom ≫ pullback.fst S.w (S.v ≫ S.w) =
      pullback.fst (S.v ≫ S.w) S.w ≫ S.v :=
  S.gluingHom_comp_fst

/-- The isomorphism lies over the second factor of `W ×_Y W`. -/
lemma gluingIso_hom_snd :
    S.gluingIso.hom ≫ pullback.snd S.w (S.v ≫ S.w) ≫ S.v =
      pullback.snd (S.v ≫ S.w) S.w := by
  rw [gluingIso_hom, ← Category.assoc, gluingHom_comp_snd, S.act_comp_v]

/-- **The action of the gluing isomorphism is the action of points.** -/
lemma actPullback_gluingIso (a : Z ⟶ S.V) (x : Z ⟶ S.W) (h : a ≫ S.v ≫ S.w = x ≫ S.w) :
    DescentDatum.actPullback (Over.mk S.v) S.gluingIso.hom a x h =
      S.act (x ≫ S.w) a h x rfl := by
  have key : S.gluingIso.hom ≫ pullback.snd S.w (S.v ≫ S.w) =
      S.act (S.gsnd ≫ S.w) S.gfst S.gcond S.gsnd rfl := S.gluingHom_comp_snd
  rw [DescentDatum.actPullback]
  simp only [Over.mk_hom]
  rw [key, S.comp_act (S.gsnd ≫ S.w) (pullback.lift a x h) S.gfst S.gcond S.gsnd rfl]
  exact S.act_congr _ _ _ _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- **The cocycle condition.** The action of the gluing isomorphism satisfies
`AlgebraicGeometry.DescentDatum.ActPullbackLaw`: acting twice is acting once. -/
lemma actPullbackLaw : DescentDatum.ActPullbackLaw (Over.mk S.v) S.gluingIso.hom := by
  intro Z' a x y hv hw hvx
  have ha' : S.act (y ≫ S.w) a (hv.trans hw) x hw ≫ S.v ≫ S.w = y ≫ S.w :=
    S.act_comp_hom (y ≫ S.w) a (hv.trans hw) x hw
  have hA : DescentDatum.actPullback (Over.mk S.v) S.gluingIso.hom a x hv =
      S.act (y ≫ S.w) a (hv.trans hw) x hw :=
    (S.actPullback_gluingIso a x hv).trans
      (S.act_base_irrel (x ≫ S.w) (y ≫ S.w) a hv (hv.trans hw) x rfl hw)
  rw [S.actPullback_gluingIso _ y hvx, S.actPullback_gluingIso a y (hv.trans hw)]
  exact (S.act_congr hvx ha' rfl rfl hA rfl).trans
    (S.act_act (y ≫ S.w) a (hv.trans hw) x hw y rfl)

/-- **The descent datum of `V` relative to `W/Y`.** -/
def datum : DescentDatum S.w :=
  DescentDatum.ofPullbackIso (Over.mk S.v) S.gluingIso S.gluingIso_hom_fst S.gluingIso_hom_snd
    S.actPullbackLaw

/-- The scheme over `W` underlying `datum` is `V`. -/
@[simp]
lemma datum_over : S.datum.over = Over.mk S.v := rfl

/-! ### Effectivity: the scheme over `Y` the datum descends to -/

/-- The action of the descent datum on generalized points is the action of points. -/
lemma datum_act_left {Z' : Over S.Y} (v' : Z' ⟶ (Over.map S.w).obj S.datum.over)
    (x' : Z' ⟶ Over.mk S.w) :
    (S.datum.act v' x').left = DescentDatum.actPullback (Over.mk S.v) S.gluingIso.hom
      v'.left x'.left ((Over.w v').trans (Over.w x').symm) :=
  DescentDatum.left_gluingAction_gluingHomOfPullbackHom (Over.mk S.v) S.gluingIso.hom
    S.gluingIso_hom_fst v' x'

/-- **A morphism out of `V` invariant for the action of the descent datum on generalized points
is invariant for the action of points.** -/
lemma act_comp_of_datum {B : Scheme.{u}} (β : S.V ⟶ B)
    (hinv : ∀ {Z' : Over S.Y} (v' : Z' ⟶ (Over.map S.w).obj S.datum.over)
      (x' : Z' ⟶ Over.mk S.w), (S.datum.act v' x').left ≫ β = v'.left ≫ β)
    (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g) (x : Z ⟶ S.W) (hx : x ≫ S.w = g) :
    S.act g a ha x hx ≫ β = a ≫ β := by
  have hleft : (S.datum.act (T := Over.mk g) (Over.homMk a ha) (Over.homMk x hx)).left =
      S.act g a ha x hx :=
    (S.datum_act_left _ _).trans
      ((S.actPullback_gluingIso a x (ha.trans hx.symm)).trans
        (S.act_base_irrel (x ≫ S.w) g a (ha.trans hx.symm) ha x rfl hx))
  have h := hinv (Z' := Over.mk g) (Over.homMk a ha) (Over.homMk x hx)
  rw [hleft] at h
  exact h

/-- **The descended scheme over `Y`.** The descent datum of `V` relative to `W/Y` is effective by
effectivity of affine descent along a quasi-compact fpqc covering, Stacks Project, Tag 0245, and
the descended scheme is étale over `Y` because étaleness is fpqc local on the target, Stacks
Project, Tag 02VN. The coordinate of a point of `V` on the descended scheme is invariant for the
action. -/
theorem exists_descended :
    ∃ (V₀ : Scheme.{u}) (q : V₀ ⟶ S.Y) (_ : Etale q) (θ : S.V ⟶ V₀),
      IsPullback θ S.v q S.w ∧
        ∀ {Z : Scheme.{u}} (g : Z ⟶ S.Y) (a : Z ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g)
          (x : Z ⟶ S.W) (hx : x ≫ S.w = g), S.act g a ha x hx ≫ θ = a ≫ θ := by
  obtain ⟨W₀, ⟨ε⟩⟩ := DescentDatum.isEffective_of_isAffineHom S.datum
    (inferInstanceAs (IsAffineHom S.v))
  obtain ⟨ι, hπ⟩ := DescentData.exists_iso_canonical_over S.w W₀
  obtain ⟨cv, hcv⟩ : ∃ cv : (Over.mk S.v : Over S.W) ⟶
      DescentDatum.over ((DescentData.canonicalFunctor S.w).obj W₀),
      cv = (DescentDatum.forget S.w).map ε.inv := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : S.V ⟶ W₀.left,
      θ = cv.left ≫ ι.hom.left ≫ pullback.fst W₀.hom S.w := ⟨_, rfl⟩
  have hcvIso : IsIso cv := by
    rw [hcv]; exact ((DescentDatum.forget S.w).mapIso ε.symm).isIso_hom
  have : IsIso cv.left := ((Over.forget S.W).mapIso (asIso cv)).isIso_hom
  have : IsIso ι.hom.left := ((Over.forget S.W).mapIso ι).isIso_hom
  have hv'' : (cv.left ≫ ι.hom.left) ≫ pullback.snd W₀.hom S.w = S.v := by
    have h1 : ι.hom.left ≫ pullback.snd W₀.hom S.w =
        (DescentDatum.over ((DescentData.canonicalFunctor S.w).obj W₀)).hom := Over.w ι.hom
    have h2 : cv.left ≫ (DescentDatum.over ((DescentData.canonicalFunctor S.w).obj W₀)).hom =
        (Over.mk S.v).hom := Over.w cv
    rw [Category.assoc, h1, h2]
    rfl
  have hcs : θ ≫ W₀.hom = S.v ≫ S.w := by
    rw [hθ]
    simp only [Category.assoc, pullback.condition]
    simpa only [Category.assoc] using congrArg (fun m => m ≫ S.w) hv''
  have hpb : IsPullback θ S.v W₀.hom S.w :=
    IsPullback.of_iso_pullback ⟨hcs⟩ (asIso (cv.left ≫ ι.hom.left))
      (by rw [hθ, asIso_hom, Category.assoc]) hv''
  have hsndEtale : Etale (pullback.snd W₀.hom S.w) := by
    have hcomp : Etale ((cv.left ≫ ι.hom.left) ≫ pullback.snd W₀.hom S.w) := by
      rw [hv'']; exact S.hv
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Etale) _ _).mp hcomp
  have hq : Etale W₀.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsndEtale
  have hequiv : ∀ {Z' : Over S.Y} (v' : Z' ⟶ (Over.map S.w).obj S.datum.over)
      (x' : Z' ⟶ Over.mk S.w), S.datum.act v' x' ≫ (Over.map S.w).map cv =
        DescentDatum.act ((DescentData.canonicalFunctor S.w).obj W₀)
          (v' ≫ (Over.map S.w).map cv) x' :=
    (DescentDatum.hom_comm_iff S.datum ((DescentData.canonicalFunctor S.w).obj W₀) cv).mp
      (by rw [hcv]; exact ε.inv.comm () ())
  have hinv : ∀ {Z' : Over S.Y} (v' : Z' ⟶ (Over.map S.w).obj S.datum.over)
      (x' : Z' ⟶ Over.mk S.w), (S.datum.act v' x').left ≫ θ = v'.left ≫ θ := by
    intro Z' v' x'
    calc (S.datum.act v' x').left ≫ θ
        = ((S.datum.act v' x').left ≫ cv.left) ≫
            ι.hom.left ≫ pullback.fst W₀.hom S.w := by
          rw [hθ]; exact (Category.assoc _ _ _).symm
      _ = (S.datum.act v' x' ≫ (Over.map S.w).map cv).left ≫
            ι.hom.left ≫ pullback.fst W₀.hom S.w := rfl
      _ = (DescentDatum.act ((DescentData.canonicalFunctor S.w).obj W₀)
            (v' ≫ (Over.map S.w).map cv) x').left ≫
            ι.hom.left ≫ pullback.fst W₀.hom S.w := by rw [hequiv v' x']
      _ = (v' ≫ (Over.map S.w).map cv).left ≫ ι.hom.left ≫ pullback.fst W₀.hom S.w :=
          hπ (v' ≫ (Over.map S.w).map cv) x'
      _ = (v'.left ≫ cv.left) ≫ ι.hom.left ≫ pullback.fst W₀.hom S.w := rfl
      _ = v'.left ≫ θ := by rw [hθ]; exact Category.assoc _ _ _
  exact ⟨W₀.left, W₀.hom, hq, θ, hpb,
    fun g a ha x hx => S.act_comp_of_datum θ hinv g a ha x hx⟩

/-! ### The identification of `U` with the base change of the descended scheme -/

/-- The projection `W ×_Y X ⟶ X` is flat. -/
instance : Flat S.πX := MorphismProperty.IsStableUnderBaseChange.of_isPullback S.hWX inferInstance

/-- The projection `W ×_Y X ⟶ X` is surjective. -/
instance : Surjective S.πX :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback S.hWX inferInstance

/-- The projection `W ×_Y X ⟶ X` is quasi-compact. -/
instance : QuasiCompact S.πX :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback S.hWX inferInstance

/-- The projection `T ⟶ U` is flat. -/
instance : Flat S.bU :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback S.hU.flip inferInstance

/-- The projection `T ⟶ U` is surjective. -/
instance : Surjective S.bU :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback S.hU.flip inferInstance

/-- The projection `T ⟶ U` is quasi-compact. -/
instance : QuasiCompact S.bU :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback S.hU.flip inferInstance

/-- The canonical section `Z ⟶ Z ×_Y X` of the base change of `f`, for a scheme `Z` over `X`
via `r`. -/
def xSection {Z : Scheme.{u}} (r : Z ⟶ S.X) : Z ⟶ (pullback (r ≫ S.f) S.f : Scheme.{u}) :=
  pullback.lift (𝟙 Z) r (Category.id_comp _)

/-- `xSection r` is a section of the projection `Z ×_Y X ⟶ Z`. -/
lemma xSection_comp_fst {Z : Scheme.{u}} (r : Z ⟶ S.X) :
    S.xSection r ≫ pullback.fst (r ≫ S.f) S.f = 𝟙 Z := pullback.lift_fst _ _ _

/-- The `X`-component of `xSection r` is `r`. -/
lemma xSection_comp_snd {Z : Scheme.{u}} (r : Z ⟶ S.X) :
    S.xSection r ≫ pullback.snd (r ≫ S.f) S.f = r := pullback.lift_snd _ _ _

/-- `xSection r` is surjective on points. -/
lemma surjective_xSection {Z : Scheme.{u}} (r : Z ⟶ S.X) :
    Function.Surjective (S.xSection r).base := by
  intro z
  refine ⟨(pullback.fst (r ≫ S.f) S.f).base z, S.injective_pullbackFst (r ≫ S.f) ?_⟩
  simpa using congrArg (fun m : Z ⟶ Z => m.base ((pullback.fst (r ≫ S.f) S.f).base z))
    (S.xSection_comp_fst r)

/-- A point of `T` over a point `r` of `X` gives a point of `V` over `r ≫ f`. -/
lemma comp_aV_comp_hom {Z : Scheme.{u}} (r : Z ⟶ S.X) (t : Z ⟶ S.T)
    (ht : t ≫ S.τ ≫ S.πX = r) : (t ≫ S.aV) ≫ S.v ≫ S.w = r ≫ S.f := by
  rw [Category.assoc, S.aV_comp, ← ht]
  simp only [Category.assoc]

/-- **The `U`-coordinate of a point of `V` coming from a point of `T`, read at the canonical
section, is the `U`-component of that point of `T`.** -/
lemma xSection_comp_uOf {Z : Scheme.{u}} (r : Z ⟶ S.X) (t : Z ⟶ S.T)
    (ht : t ≫ S.τ ≫ S.πX = r) :
    S.xSection r ≫ S.uOf (r ≫ S.f) (t ≫ S.aV) (S.comp_aV_comp_hom r t ht) = t ≫ S.bU := by
  have hts : S.xSection r ≫ S.tLift (r ≫ S.f) (t ≫ S.aV) (S.comp_aV_comp_hom r t ht) = t := by
    refine S.isPullback_V.hom_ext ?_ ?_
    · rw [Category.assoc, S.tLift_comp_aV, ← Category.assoc, S.xSection_comp_fst,
        Category.id_comp]
    · rw [Category.assoc, S.tLift_comp_proj, S.xSection_comp_snd, ht]
  rw [uOf, ← Category.assoc, hts]

/-- The `U`-coordinate depends on the point of `V` only through its value. -/
lemma uOf_congr (g : Z ⟶ S.Y) {a a' : Z ⟶ S.V} (ha : a ≫ S.v ≫ S.w = g)
    (ha' : a' ≫ S.v ≫ S.w = g) (h : a = a') : S.uOf g a ha = S.uOf g a' ha' := by
  subst h; rfl

/-- **Two points of `T` over one point of `X` whose `U`-components agree have `V`-components with
the same `U`-coordinate.** -/
lemma uOf_eq_of_comp_bU {Z : Scheme.{u}} (r : Z ⟶ S.X) (t t' : Z ⟶ S.T)
    (ht : t ≫ S.τ ≫ S.πX = r) (ht' : t' ≫ S.τ ≫ S.πX = r) (hbU : t ≫ S.bU = t' ≫ S.bU) :
    S.uOf (r ≫ S.f) (t ≫ S.aV) (S.comp_aV_comp_hom r t ht) =
      S.uOf (r ≫ S.f) (t' ≫ S.aV) (S.comp_aV_comp_hom r t' ht') := by
  refine hom_ext_of_surjective (S.xSection r) (S.surjective_xSection r) S.p _ _
    ((S.uOf_comp_p _ _ _).trans (S.uOf_comp_p _ _ _).symm) ?_
  rw [S.xSection_comp_uOf r t ht, S.xSection_comp_uOf r t' ht', hbU]

/-- **Conversely, two points of `T` over one point of `X` whose `V`-components have the same
`U`-coordinate have the same `U`-component.** -/
lemma comp_bU_eq_of_uOf_eq {Z : Scheme.{u}} (r : Z ⟶ S.X) (t t' : Z ⟶ S.T)
    (ht : t ≫ S.τ ≫ S.πX = r) (ht' : t' ≫ S.τ ≫ S.πX = r)
    (hu : S.uOf (r ≫ S.f) (t ≫ S.aV) (S.comp_aV_comp_hom r t ht) =
      S.uOf (r ≫ S.f) (t' ≫ S.aV) (S.comp_aV_comp_hom r t' ht')) :
    t ≫ S.bU = t' ≫ S.bU := by
  rw [← S.xSection_comp_uOf r t ht, ← S.xSection_comp_uOf r t' ht', hu]

/-- **Two points of `T` over one point of `U` and over one point of `X` have `V`-components that
differ by the action of a point of `W`.** Consequently every morphism out of `V` invariant for
the action agrees on them. -/
lemma comp_aV_comp_eq_of_comp_bU {Z : Scheme.{u}} (r : Z ⟶ S.X) (t t' : Z ⟶ S.T)
    (ht : t ≫ S.τ ≫ S.πX = r) (ht' : t' ≫ S.τ ≫ S.πX = r) (hbU : t ≫ S.bU = t' ≫ S.bU)
    {B : Scheme.{u}} (β : S.V ⟶ B)
    (hβ : ∀ {Z' : Scheme.{u}} (g : Z' ⟶ S.Y) (a : Z' ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g)
      (x : Z' ⟶ S.W) (hx : x ≫ S.w = g), S.act g a ha x hx ≫ β = a ≫ β) :
    (t ≫ S.aV) ≫ β = (t' ≫ S.aV) ≫ β := by
  have ha := S.comp_aV_comp_hom r t ht
  have ha' := S.comp_aV_comp_hom r t' ht'
  have hx' : ((t' ≫ S.aV) ≫ S.v) ≫ S.w = r ≫ S.f := (Category.assoc _ _ _).trans ha'
  have hacteq : S.act (r ≫ S.f) (t ≫ S.aV) ha ((t' ≫ S.aV) ≫ S.v) hx' = t' ≫ S.aV :=
    S.hom_ext_of_uOf (r ≫ S.f) _ (t' ≫ S.aV) (S.act_comp_hom _ _ ha _ hx') ha'
      ((S.uOf_act _ _ ha _ hx').trans (S.uOf_eq_of_comp_bU r t t' ht ht' hbU))
      (S.act_comp_v _ _ ha _ hx')
  exact (hβ (r ≫ S.f) (t ≫ S.aV) ha ((t' ≫ S.aV) ≫ S.v) hx').symm.trans
    (congrArg (fun m => m ≫ β) hacteq)

/-- **Two points of `T` over one point of `X` whose `V`-components have the same coordinate on
the descended scheme have the same `U`-component.** -/
lemma comp_bU_eq_of_comp_descended {V₀ : Scheme.{u}} {q : V₀ ⟶ S.Y} (θ : S.V ⟶ V₀)
    (hpb : IsPullback θ S.v q S.w)
    (hθinv : ∀ {Z' : Scheme.{u}} (g : Z' ⟶ S.Y) (a : Z' ⟶ S.V) (ha : a ≫ S.v ≫ S.w = g)
      (x : Z' ⟶ S.W) (hx : x ≫ S.w = g), S.act g a ha x hx ≫ θ = a ≫ θ)
    {Z : Scheme.{u}} (r : Z ⟶ S.X) (t t' : Z ⟶ S.T)
    (ht : t ≫ S.τ ≫ S.πX = r) (ht' : t' ≫ S.τ ≫ S.πX = r)
    (hθeq : (t ≫ S.aV) ≫ θ = (t' ≫ S.aV) ≫ θ) : t ≫ S.bU = t' ≫ S.bU := by
  have ha := S.comp_aV_comp_hom r t ht
  have ha' := S.comp_aV_comp_hom r t' ht'
  have hx' : ((t' ≫ S.aV) ≫ S.v) ≫ S.w = r ≫ S.f := (Category.assoc _ _ _).trans ha'
  have hacteq : S.act (r ≫ S.f) (t ≫ S.aV) ha ((t' ≫ S.aV) ≫ S.v) hx' = t' ≫ S.aV :=
    hpb.hom_ext ((hθinv _ _ ha _ hx').trans hθeq) (S.act_comp_v _ _ ha _ hx')
  refine S.comp_bU_eq_of_uOf_eq r t t' ht ht' ?_
  refine ((S.uOf_act (r ≫ S.f) (t ≫ S.aV) ha _ hx').symm).trans
    (S.uOf_congr (r ≫ S.f) (S.act_comp_hom _ _ ha _ hx') ha' hacteq)

/-- **The descent step, Stacks Project, Tag 04E0 over a genuine fpqc covering.** The étale
scheme `U` over `X` is the base change along `f` of a scheme étale over `Y`.

`V` descends to a scheme `V₀` étale over `Y` by
`Stacks.Etale.FpqcDescent.Setup.exists_descended`; the coordinate `T ⟶ V ⟶ V₀` is invariant for
the two projections of `T ×_U T`, because two points of `T` over one point of `U` have
`V`-components differing by the action of a point of `W`, which that coordinate does not see; so
it descends along the one-member fpqc covering `T ⟶ U` by descent of morphisms, Stacks Project,
Tag 023Q, giving `δ : U ⟶ V₀`. In the other direction `T ⟶ U` descends along the one-member fpqc
covering `T ⟶ V₀ ×_Y X`, because two points of `T` over one point of `V₀ ×_Y X` have
`V`-components with the same coordinate on `V₀` and so the same `U`-component; the two descended
morphisms are mutually inverse, which is what exhibits `U` as `V₀ ×_Y X`. -/
theorem exists_etale_pullback :
    ∃ (V₀ : Scheme.{u}) (q : V₀ ⟶ S.Y) (_ : Etale q) (δ : S.U ⟶ V₀),
      IsPullback δ S.p q S.f := by
  obtain ⟨V₀, q, hq, θ, hpb, hθinv⟩ := S.exists_descended
  have hθq : θ ≫ q = S.v ≫ S.w := hpb.w
  have hinv : pullback.fst S.bU S.bU ≫ S.aV ≫ θ = pullback.snd S.bU S.bU ≫ S.aV ≫ θ := by
    have hrr : pullback.snd S.bU S.bU ≫ S.τ ≫ S.πX =
        pullback.fst S.bU S.bU ≫ S.τ ≫ S.πX := by
      rw [← S.hU.w, pullback.condition_assoc]
    simpa only [Category.assoc] using S.comp_aV_comp_eq_of_comp_bU
      (pullback.fst S.bU S.bU ≫ S.τ ≫ S.πX) (pullback.fst S.bU S.bU)
      (pullback.snd S.bU S.bU) rfl hrr pullback.condition θ hθinv
  obtain ⟨δ, hδ⟩ := exists_desc_of_surjective_flat_quasiCompact' S.bU (S.aV ≫ θ) hinv
  have hδq : δ ≫ q = S.p ≫ S.f := by
    refine eq_of_comp_eq_of_surjective_of_flat S.bU ?_
    rw [← Category.assoc, hδ, Category.assoc, hθq, S.aV_comp, ← Category.assoc, ← S.hU.w,
      Category.assoc]
  have hTpb : IsPullback S.τ (S.aV ≫ θ) (S.πX ≫ S.f) q := by
    have h := S.hV.flip.paste_vert hpb.flip
    rwa [S.hWX.w] at h
  have hcond : (S.aV ≫ θ) ≫ q = (S.τ ≫ S.πX) ≫ S.f := by
    rw [← hTpb.w]; simp only [Category.assoc]
  obtain ⟨b₂, hb₂fst, hb₂snd⟩ : ∃ b₂ : S.T ⟶ (pullback q S.f : Scheme.{u}),
      b₂ ≫ pullback.fst q S.f = S.aV ≫ θ ∧ b₂ ≫ pullback.snd q S.f = S.τ ≫ S.πX :=
    ⟨pullback.lift (S.aV ≫ θ) (S.τ ≫ S.πX) hcond, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have hb₂pb : IsPullback b₂ S.τ (pullback.snd q S.f) S.πX := by
    refine (IsPullback.of_bot ?_ hb₂snd.symm (IsPullback.of_hasPullback q S.f).flip).flip
    rw [hb₂fst]
    exact hTpb
  have : Flat b₂ := MorphismProperty.IsStableUnderBaseChange.of_isPullback hb₂pb.flip
    inferInstance
  have : Surjective b₂ := MorphismProperty.IsStableUnderBaseChange.of_isPullback hb₂pb.flip
    inferInstance
  have : QuasiCompact b₂ := MorphismProperty.IsStableUnderBaseChange.of_isPullback hb₂pb.flip
    inferInstance
  have hinv₂ : pullback.fst b₂ b₂ ≫ S.bU = pullback.snd b₂ b₂ ≫ S.bU := by
    have hrr : pullback.snd b₂ b₂ ≫ S.τ ≫ S.πX = pullback.fst b₂ b₂ ≫ S.τ ≫ S.πX := by
      rw [← hb₂snd, pullback.condition_assoc]
    refine S.comp_bU_eq_of_comp_descended θ hpb hθinv
      (pullback.fst b₂ b₂ ≫ S.τ ≫ S.πX) _ _ rfl hrr ?_
    simp only [Category.assoc]
    rw [← hb₂fst]
    simp only [← Category.assoc]
    rw [pullback.condition]
  obtain ⟨n, hn⟩ := exists_desc_of_surjective_flat_quasiCompact' b₂ S.bU hinv₂
  have hbm : S.bU ≫ pullback.lift δ S.p hδq = b₂ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, hδ, hb₂fst]
    · rw [Category.assoc, pullback.lift_snd, S.hU.w, hb₂snd]
  have : IsIso (pullback.lift δ S.p hδq) := by
    refine ⟨n, ?_, ?_⟩
    · refine eq_of_comp_eq_of_surjective_of_flat S.bU ?_
      rw [← Category.assoc, hbm, hn, Category.comp_id]
    · refine eq_of_comp_eq_of_surjective_of_flat b₂ ?_
      rw [← Category.assoc, hn, hbm, Category.comp_id]
  exact ⟨V₀, q, hq, δ, IsPullback.of_iso_pullback ⟨hδq⟩
    (asIso (pullback.lift δ S.p hδq)) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩

end Setup

end FpqcDescent

open _root_.AlgebraicGeometry

/-- **The descent step of the affine case, over a genuine fpqc covering.**
`Stacks.Etale.EtaleDescentAlongFpqcAffineCover` holds: for a universal homeomorphism
`f : X ⟶ Y` and a surjective quasi-compact étale `w : W ⟶ Y`, a scheme `V` étale and affine
over `W` whose base change to `W ×_Y X` is also the base change of a scheme `U` étale over `X`
descends to a scheme étale over `Y` with base change `U`.

This is the last paragraph of the second proof of Stacks Project, Tag 04DZ. -/
theorem etaleDescentAlongFpqcAffineCover : EtaleDescentAlongFpqcAffineCover.{u} := by
  intro X Y W WX U V T f w πW πX p v α τ β hf hw hwsurj hwqc hp hv hvaff hWX hV hU
  exact FpqcDescent.Setup.exists_etale_pullback
    { X := X, Y := Y, W := W, WX := WX, U := U, V := V, T := T, f := f, w := w, πW := πW,
      πX := πX, p := p, v := v, aV := α, τ := τ, bU := β, hf := hf, hw := hw,
      hwsurj := hwsurj, hwqc := hwqc, hp := hp, hv := hv, hvaff := hvaff, hWX := hWX,
      hV := hV, hU := hU }

end Stacks.Etale

end

end
