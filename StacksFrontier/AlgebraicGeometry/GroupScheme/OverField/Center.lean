module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.WeilRestrictionAffineOverField
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Separated
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs

/-!
# The centre of a locally algebraic group scheme

Let `k` be a field and let `G` be a group scheme over `k` which is locally of finite type, that
is, locally algebraic.  The centre of `G` is not given by a construction on the underlying
scheme; it is a *subfunctor* of `G`, sending a `k`-scheme `T` to the subgroup of those
`g ∈ G(T)` whose inner automorphism is the identity after every further base change.  The
assertion of the source is therefore a representability statement: this subfunctor is
represented by a closed subgroup scheme of `G`.

## Main definitions

* `Stacks.Groupoids.IsCentralPoint` is the functorial centrality condition on a relative point
  of a group scheme: it commutes with every point after every base change of its domain.
* `Stacks.Groupoids.HasWeilRestrictionAffineOverField` names the Weil restriction of a closed
  subscheme of `A ×_k B` along the projection to `B`, for `A` affine and of finite type over `k`
  and `B` arbitrary, in the "every point of the base change factors" form in which the argument
  below consumes it.

## Main results

* `Stacks.Groupoids.isCentralPoint_iff_affineCover` reduces centrality to commutation with the
  points of the members of an affine open cover of the group scheme.
* `Stacks.Groupoids.exists_closed_intersection` intersects an arbitrary family of closed
  subschemes of a scheme.
* `Stacks.Groupoids.hasWeilRestrictionAffineOverField` proves that Weil restriction.
* `Stacks.Groupoids.exists_closedSubgroupScheme_center` represents the functorial centre by a
  closed subgroup scheme.

## Implementation notes

The source's proof is *not* followed.  It cuts the centre out as an intersection of kernels of
the representations of `G` on the infinitesimal neighbourhoods of the identity in the affine
charts, identifies the resulting functor using Tag 00IR, and then descends from `k̄` to `k`
along an fpqc cover with Tags 022W, 06LH, 02L6 and 03I0.  The route taken here never touches
descent, infinitesimal neighbourhoods or the identity component.  Over a field a group scheme is
separated (Tag 047L), so for every affine chart `A ⊆ G` the locus in `A ×_k G` on which the two
composites `(a, g) ↦ a · g` and `(a, g) ↦ g · a` agree is the equalizer of two morphisms into a
separated scheme, hence a closed subscheme.  Weil restriction along the projection
`A ×_k G ⟶ G` turns that closed subscheme into a closed subscheme `W ⊆ G` which universally cuts
out "commutes with every point of `A`"; intersecting the `W` over an affine cover of `G` — which
is legitimate because `isCentralPoint_iff_affineCover` lets centrality be tested chart by chart
— gives the centre.

Only the case of Tag 07AI in which the projection `A ×_k B ⟶ B` is a base change of an affine
morphism of finite type over the field `k` is needed, and in that case all four hypotheses of
Tag 07AI hold outright:
`Stacks.Flatness.exists_closedImmersion_weilRestriction_of_isAffine_over_field`.  The one with
content is purity of the structure sheaf of `A ×_k B` relative to `B`, which holds because
`Γ(A, ⊤)` is a `k`-vector space, hence a projective `k`-module, so that the direct image of the
structure sheaf is locally projective over `Spec k` and stays so after the base change; a module
with locally projective direct image along an affine morphism is pure, by Tag 05MD.  Nothing is
assumed: both `IsCentralPoint` and the representability statement carry a `0BF8` tag, and
together they are the source's assertion — the first says what the centre is, the second that it
is a closed subgroup scheme.

## References

* [Stacks Project, Tag 0BF8](https://stacks.math.columbia.edu/tag/0BF8)
* [Stacks Project, Tag 047L](https://stacks.math.columbia.edu/tag/047L)
* [Stacks Project, Tag 05MD](https://stacks.math.columbia.edu/tag/05MD)
* [Stacks Project, Tag 07AI](https://stacks.math.columbia.edu/tag/07AI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace Stacks.Groupoids

attribute [local simp] Limits.pullback.lift_fst Limits.pullback.lift_snd
  Limits.pullback.lift_fst_assoc Limits.pullback.lift_snd_assoc

universe u

/-- A relative point of a group scheme lies in its functorial centre if it commutes with every
point after every base change of its domain. -/
@[stacks 0BF8 "the functorial centre", sga "3 I 2.3.6" "center", sga "3 VIII 6.5"]
def IsCentralPoint {S : Scheme.{u}} (G : Grp (Over S)) {T : Over S} (h : T ⟶ G.X) : Prop :=
  ∀ (U : Over S) (f : U ⟶ T) (x : U ⟶ G.X), (f ≫ h) * x = x * (f ≫ h)

/-- The central relative points with a fixed domain form a subgroup of the group of all relative
points with that domain. -/
@[sga "3 I 2.3.6" "special case", sga "3 VIII 6.5" "partial, special case"]
private def centralPointSubgroup {S : Scheme.{u}} (G : Grp (Over S)) (T : Over S) :
    Subgroup (T ⟶ G.X) where
  carrier := IsCentralPoint G
  one_mem' := fun U f x ↦ by simp
  mul_mem' := by
    intro h₁ h₂ hh₁ hh₂ U f x
    rw [MonObj.comp_mul]
    exact Commute.mul_left (hh₁ U f x) (hh₂ U f x)
  inv_mem' := by
    intro h hh U f x
    rw [GrpObj.comp_inv]
    exact (show Commute (f ≫ h) x from hh U f x).inv_left

/-- The functorial centre of a group scheme, as a group-valued presheaf on the schemes over the
base. -/
@[sga "3 I 2.3.6" "special case", sga "3 VIB 6.1" "special case", sga "3 VIII 6.5"]
private def centralPointFunctor {S : Scheme.{u}} (G : Grp (Over S)) :
    (Over S)ᵒᵖ ⥤ GrpCat where
  obj T := GrpCat.of (centralPointSubgroup G T.unop)
  map {T U} f := GrpCat.ofHom
    { toFun := fun h ↦ ⟨f.unop ≫ h.val, by
        intro U g x; simpa [Category.assoc] using h.property U (g ≫ f.unop) x⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp [MonObj.comp_mul] }
  map_id T := by ext; simp
  map_comp f g := by ext; simp [Category.assoc]

/-- A closed subscheme of a group scheme through which exactly the central points factor is a
closed subgroup scheme.  The group structure is transported from the functorial centre along the
representability isomorphism, which also forces the inclusion to be a morphism of group
objects. -/
private lemma exists_closedSubgroupScheme_of_representsCentralPoints
    {S : Scheme.{u}} (G : Grp (Over S)) (Z : Over S) (i : Z ⟶ G.X)
    [IsClosedImmersion i.left]
    (hZ : ∀ (T : Over S) (h : T ⟶ G.X),
      (∃ z : T ⟶ Z, z ≫ i = h) ↔ IsCentralPoint G h) :
    ∃ H : ClosedSubgroupScheme G,
      ∀ (T : Over S) (h : T ⟶ G.X),
        (∃ z : T ⟶ H.carrier.X, z ≫ H.ι.hom.hom = h) ↔ IsCentralPoint G h := by
  classical
  have : Mono i := Over.mono_of_mono_left i
  let e : (centralPointFunctor G ⋙ forget _).RepresentableBy Z :=
    { homEquiv := fun {T} ↦
        { toFun := fun z ↦ ⟨z ≫ i, (hZ T _).mp ⟨z, rfl⟩⟩
          invFun := fun h ↦ Classical.choose ((hZ T h.val).mpr h.property)
          left_inv := fun z ↦ (cancel_mono i).mp
            (Classical.choose_spec ((hZ T (z ≫ i)).mpr ((hZ T _).mp ⟨z, rfl⟩)))
          right_inv := fun h ↦ Subtype.ext
            (Classical.choose_spec ((hZ T h.val).mpr h.property)) }
      homEquiv_comp := fun f z ↦ Subtype.ext (Category.assoc _ _ _) }
  let := GrpObj.ofRepresentableBy Z (centralPointFunctor G) e
  let α : yonedaGrpObj Z ⟶ centralPointFunctor G :=
    (yonedaGrpObjIsoOfRepresentableBy Z (centralPointFunctor G) e).hom
  have hi : IsMonHom i := by
    constructor
    · exact congrArg Subtype.val (α.app (Opposite.op (𝟙_ (Over S)))).hom.map_one
    · have h := (α.app (Opposite.op (Z ⊗ Z))).hom.map_mul (fst Z Z) (snd Z Z)
      have hh := congrArg Subtype.val h
      change ((fst Z Z * snd Z Z) ≫ i) = (fst Z Z ≫ i) * (snd Z Z ≫ i) at hh
      rw [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp,
        CategoryTheory.Hom.mul_def] at hh
      convert hh using 1
      congr 1
  let H : ClosedSubgroupScheme G :=
    { carrier := Grp.mk Z
      «ι» := Grp.homMk i
      isClosedImmersion := ‹IsClosedImmersion i.left› }
  exact ⟨H, hZ⟩

/-- A scheme over `X` maps to a closed subscheme of `X` over `X` exactly when the ideal sheaf of
the closed subscheme dies on it. -/
private lemma nonempty_over_hom_iff_ker_le {X : Scheme.{u}} (W T : Over X)
    [IsClosedImmersion W.hom] : Nonempty (T ⟶ W) ↔ W.hom.ker ≤ T.hom.ker := by
  constructor
  · rintro ⟨z⟩
    rw [← z.w]
    exact Scheme.Hom.le_ker_comp z.left W.hom
  · intro h
    exact ⟨Over.homMk (IsClosedImmersion.lift W.hom T.hom h)
      (IsClosedImmersion.lift_fac W.hom T.hom h)⟩

/-- An arbitrary family of closed subschemes of a scheme has an intersection, namely the closed
subscheme cut out by the supremum of their ideal sheaves. -/
lemma exists_closed_intersection {X : Scheme.{u}} {J : Type*}
    (W : J → Over X) (hW : ∀ j, IsClosedImmersion (W j).hom) :
    ∃ Z : Over X, IsClosedImmersion Z.hom ∧
      ∀ T : Over X, Nonempty (T ⟶ Z) ↔ ∀ j, Nonempty (T ⟶ W j) := by
  let I : X.IdealSheafData := ⨆ j, (W j).hom.ker
  let Z : Over X := Over.mk I.subschemeι
  have hZ : IsClosedImmersion Z.hom := inferInstanceAs (IsClosedImmersion I.subschemeι)
  refine ⟨Z, hZ, fun T ↦ ?_⟩
  rw [nonempty_over_hom_iff_ker_le Z T]
  change I.subschemeι.ker ≤ T.hom.ker ↔ _
  rw [Scheme.IdealSheafData.ker_subschemeι, iSup_le_iff]
  exact forall_congr' fun j ↦ (nonempty_over_hom_iff_ker_le (W j) T).symm

/-- Centrality of a relative point may be tested chart by chart: it is enough that the point
commute with the points of each member of the affine open cover of the group scheme.  Two
morphisms of schemes agreeing on an open cover of the source are equal, which is what lets the
test objects be pulled back into the charts. -/
lemma isCentralPoint_iff_affineCover {S : Scheme.{u}} (G : Grp (Over S)) (T : Over S)
    (h : T ⟶ G.X) :
    IsCentralPoint G h ↔
      ∀ (j : G.X.left.affineCover.I₀) (U : Over S)
        (x : U ⟶ Over.mk (G.X.left.affineCover.f j ≫ G.X.hom)) (t : U ⟶ T),
        (x ≫ Over.homMk (G.X.left.affineCover.f j)) * (t ≫ h) =
          (t ≫ h) * (x ≫ Over.homMk (G.X.left.affineCover.f j)) := by
  refine ⟨fun hh j U x t ↦ (hh U t (x ≫ Over.homMk (G.X.left.affineCover.f j))).symm,
    fun hh U t x ↦ ?_⟩
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (G.X.left.affineCover.pullback₁ x.left) _ _
  intro j
  change G.X.left.affineCover.I₀ at j
  let V : Over S :=
    Over.mk (Limits.pullback.fst x.left (G.X.left.affineCover.f j) ≫ U.hom)
  let p : V ⟶ U := Over.homMk (Limits.pullback.fst x.left (G.X.left.affineCover.f j))
  let q : V ⟶ Over.mk (G.X.left.affineCover.f j ≫ G.X.hom) :=
    Over.homMk (Limits.pullback.snd x.left (G.X.left.affineCover.f j)) (by
      change Limits.pullback.snd x.left (G.X.left.affineCover.f j) ≫
        G.X.left.affineCover.f j ≫ G.X.hom =
          Limits.pullback.fst x.left (G.X.left.affineCover.f j) ≫ U.hom
      rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc, Over.w x])
  have hx : q ≫ Over.homMk (G.X.left.affineCover.f j) = p ≫ x :=
    Over.OverMorphism.ext Limits.pullback.condition.symm
  exact congrArg Over.Hom.left (show p ≫ ((t ≫ h) * x) = p ≫ (x * (t ≫ h)) by
    simpa only [hx, MonObj.comp_mul, Category.assoc] using (hh j V q (p ≫ t)).symm)

/-- The easy case of **Stacks Project, Tag 07AI**: for `A` affine and of finite type over the
field `k` and `B` arbitrary over `k`, every closed subscheme `Z ⊆ A ×_k B` admits a Weil
restriction along the projection `A ×_k B ⟶ B`, that is, a closed subscheme `W ⊆ B` through
which a scheme over `B` factors exactly when every point of its base change to `A ×_k B` lands
in `Z`.

It is a predicate rather than a theorem only because it is the form in which the argument below
consumes Tag 07AI, quantified over all `A` and `B` at once; it is proved, by
`Stacks.Groupoids.hasWeilRestrictionAffineOverField`. -/
def HasWeilRestrictionAffineOverField (k : Type u) [Field k] : Prop :=
  ∀ (A B : Over (Spec (.of k))), IsAffine A.left → LocallyOfFiniteType A.hom →
    ∀ {Z : Scheme.{u}} (i : Z ⟶ (A ⊗ B).left), IsClosedImmersion i →
      ∃ W : Over B.left, IsClosedImmersion W.hom ∧
        ∀ T : Over B.left,
          Nonempty (T ⟶ W) ↔
            ∀ (U : Scheme.{u}) (x : U ⟶ T.left) (y : U ⟶ (A ⊗ B).left),
              y ≫ (snd A B).left = x ≫ T.hom → ∃ c : U ⟶ Z, c ≫ i = y

/-- The pointwise universal property of the Weil restriction of a closed subscheme `Y ⟶ X`
along `X ⟶ S`: for every `S`-scheme `T`, the morphisms `T ⟶ W` over `S` correspond to the
single proof that the base change `Y_T ⟶ X_T` is an isomorphism.  This is the form in which
Tag 07AI states its conclusion. -/
def RepresentsClosedSubschemeWeilRestriction {Y X S : Scheme.{u}} (i : Y ⟶ X) (f : X ⟶ S)
    (W : Over S) : Prop :=
  ∀ T : Over S,
    Nonempty ((T ⟶ W) ≃ PLift
      (IsIso ((Over.pullback T.hom).map
        (Over.homMk i (by simp) : Over.mk (i ≫ f) ⟶ Over.mk f)).left))

/-- A Weil restriction in the sense of `RepresentsClosedSubschemeWeilRestriction` is exactly a
closed subscheme of the base through which the schemes all of whose base-changed points factor
through the closed subscheme factor.  The base change `Y_T ⟶ X_T` is a closed immersion, hence
a monomorphism, so it is an isomorphism exactly when it is split by a section, and a section is
the same datum as a factorization of the identity of `X_T`; unwinding the pullback this is the
pointwise factorization condition. -/
lemma weilRestriction_iff_factors {Y X S : Scheme.{u}} (i : Y ⟶ X) (f : X ⟶ S)
    [IsClosedImmersion i] (W : Over S)
    (hW : RepresentsClosedSubschemeWeilRestriction i f W) (T : Over S) :
    Nonempty (T ⟶ W) ↔
      ∀ (U : Scheme.{u}) (a : U ⟶ T.left) (b : U ⟶ X),
        b ≫ f = a ≫ T.hom → ∃ c : U ⟶ Y, c ≫ i = b := by
  classical
  let j := ((Over.pullback T.hom).map
    (Over.homMk i (by simp) : Over.mk (i ≫ f) ⟶ Over.mk f)).left
  have hj₁ : j ≫ Limits.pullback.fst f T.hom = Limits.pullback.fst (i ≫ f) T.hom ≫ i := by
    simp [j, Over.pullback_map_left]
  have hj₂ : j ≫ Limits.pullback.snd f T.hom = Limits.pullback.snd (i ≫ f) T.hom := by
    simp [j, Over.pullback_map_left]
  have hiso : Nonempty (T ⟶ W) ↔ IsIso j := by
    let e := Classical.choice (hW T)
    exact ⟨fun h ↦ (e h.some).down, fun h ↦ ⟨e.symm ⟨h⟩⟩⟩
  rw [hiso]
  constructor
  · intro hj U a b hab
    let := hj
    refine ⟨Limits.pullback.lift b a hab ≫ inv j ≫ Limits.pullback.fst (i ≫ f) T.hom, ?_⟩
    rw [Category.assoc, Category.assoc, ← hj₁, IsIso.inv_hom_id_assoc]
    simp
  · intro h
    obtain ⟨c, hc⟩ := h (Limits.pullback f T.hom)
      (Limits.pullback.snd f T.hom) (Limits.pullback.fst f T.hom) Limits.pullback.condition
    let r : Limits.pullback f T.hom ⟶ Limits.pullback (i ≫ f) T.hom :=
      Limits.pullback.lift c (Limits.pullback.snd f T.hom)
        (by rw [← Category.assoc, hc]; exact Limits.pullback.condition)
    have hr : r ≫ j = 𝟙 _ := by
      apply Limits.pullback.hom_ext
      · simp [Category.assoc, hj₁, r, hc]
      · simp [Category.assoc, hj₂, r]
    have hl : j ≫ r = 𝟙 _ := by
      apply Limits.pullback.hom_ext
      · apply (cancel_mono i).mp
        simpa [Category.assoc, r, hc] using hj₁
      · simp [Category.assoc, r, hj₂]
    exact ⟨⟨r, hl, hr⟩⟩

/-- Tag 07AI in the form in which the source states it — representability of the
Weil-restriction functor by a closed immersion — implies
`HasWeilRestrictionAffineOverField`.  So the latter is not a reformulation of something stronger
than Tag 07AI restricted to an affine first factor. -/
lemma hasWeilRestrictionAffineOverField_of_representability {k : Type u} [Field k]
    (h : ∀ (A B : Over (Spec (.of k))), IsAffine A.left → LocallyOfFiniteType A.hom →
      ∀ {Z : Scheme.{u}} (i : Z ⟶ (A ⊗ B).left), IsClosedImmersion i →
        ∃ W : Over B.left, IsClosedImmersion W.hom ∧
          RepresentsClosedSubschemeWeilRestriction i (snd A B).left W) :
    HasWeilRestrictionAffineOverField k := by
  intro A B hA hft Z i hi
  obtain ⟨W, hw, hW⟩ := h A B hA hft i hi
  exact ⟨W, hw, fun T ↦ weilRestriction_iff_factors i _ W hW T⟩

/-- **Weil restriction along the projection `A ×_k B ⟶ B` for `A` affine and of finite type over
the field `k`.**  The product `A ⊗ B` in the schemes over `k` is the fibre product `A ×_k B`, so
the projection to `B` is a base change of the structure morphism of `A`, and
`Stacks.Flatness.exists_closedImmersion_weilRestriction_of_isAffine_over_field` applies: all
four hypotheses of Tag 07AI hold for such a base change. -/
@[sga "3 VIB 6.2.3" "(i)",
  sga "3 VIB 6.2.4" "(a), special case",
  sga "3 VIB 6.5.2" "special case",
  sga "3 VIII 6.5" "Clause (a), special case"]
theorem hasWeilRestrictionAffineOverField (k : Type u) [Field k] :
    HasWeilRestrictionAffineOverField k := by
  refine hasWeilRestrictionAffineOverField_of_representability
    (fun A B hA hft Z i hi ↦ ?_)
  have := hA
  have := hft
  have := hi
  have hpb : IsPullback (fst A B).left (snd A B).left A.hom B.hom :=
    Over.isPullback_of_binaryFan_isLimit (Limits.BinaryFan.mk (fst A B) (snd A B))
      (tensorProductIsBinaryProduct A B)
  exact Stacks.Flatness.exists_closedImmersion_weilRestriction_of_isAffine_over_field
    A.hom B.hom (fst A B).left (snd A B).left hpb i

/-- Granted Weil restriction for affine `A`, the locus in `B` on which two morphisms
`A ⊗ B ⟶ Y` into a separated scheme agree universally is a closed subscheme of `B`: the
equalizer of the two morphisms is a closed subscheme of `A ⊗ B`, and its Weil restriction along
the projection to `B` is the required closed subscheme. -/
private lemma exists_closed_universal_equalizer {k : Type u} [Field k]
    (hwr : HasWeilRestrictionAffineOverField k) (A B Y : Over (Spec (.of k)))
    [IsAffine A.left] [LocallyOfFiniteType A.hom] [IsSeparated Y.hom] (a b : A ⊗ B ⟶ Y) :
    ∃ W : Over B.left, IsClosedImmersion W.hom ∧
      ∀ (T : Over (Spec (.of k))) (h : T ⟶ B),
        Nonempty (Over.mk h.left ⟶ W) ↔
          ∀ (U : Over (Spec (.of k))) (x : U ⟶ A) (t : U ⟶ T),
            lift x (t ≫ h) ≫ a = lift x (t ≫ h) ≫ b := by
  let i := (Limits.equalizer.ι a b).left
  obtain ⟨W, hWclosed, hW⟩ := hwr A B ‹_› ‹_› i inferInstance
  refine ⟨W, hWclosed, fun T h ↦ ?_⟩
  rw [hW (Over.mk h.left)]
  constructor
  · intro hh U x t
    obtain ⟨c, hc⟩ := hh U.left t.left (lift x (t ≫ h)).left (by
      change (lift x (t ≫ h)).left ≫ (snd A B).left = t.left ≫ h.left
      simp only [← Over.comp_left, lift_snd])
    apply Over.OverMorphism.ext
    change (lift x (t ≫ h)).left ≫ a.left = (lift x (t ≫ h)).left ≫ b.left
    rw [← hc, Category.assoc, Category.assoc]
    exact congrArg (fun m ↦ c ≫ m.left) (Limits.equalizer.condition a b)
  · intro hh U t c hc
    simp only [Over.mk_hom] at hc
    let U' : Over (Spec (.of k)) := Over.mk (t ≫ T.hom)
    let t' : U' ⟶ T := Over.homMk t
    let c' : U' ⟶ A ⊗ B := Over.homMk c (by
      change c ≫ (A ⊗ B).hom = t ≫ T.hom
      rw [← Over.w (snd A B), ← Category.assoc, hc, Category.assoc, Over.w h])
    have hc' : c' ≫ snd A B = t' ≫ h := Over.OverMorphism.ext hc
    have hab := hh U' (c' ≫ fst A B) t'
    rw [← hc', lift_comp_fst_snd] at hab
    exact ⟨(Limits.equalizer.lift c' hab).left,
      congrArg Over.Hom.left (Limits.equalizer.lift_ι c' hab)⟩

/-- **Stacks Project, Tag 0BF8.** The centre of a locally algebraic group scheme over a field is
a closed subgroup scheme: the functorial centre `Stacks.Groupoids.IsCentralPoint` is represented
by a closed subgroup scheme of `G`.

The group scheme is separated over the field by Tag 047L, so for each chart `A` of the affine
open cover of `G` the locus where a point of `A` and a point of `G` commute is a closed subscheme
of `A ⊗ G`; its Weil restriction `W` along the projection to `G`, which exists by
`Stacks.Groupoids.hasWeilRestrictionAffineOverField`, universally cuts out "commutes with every
point of `A`".  The intersection of the `W` over all charts represents the centre by
`isCentralPoint_iff_affineCover`. -/
@[stacks 0BF8 "representability of the centre by a closed subgroup scheme",
  sga "3 VIB 6.2.4" "special case",
  sga "3 VIB 6.2.5" "(i), special case",
  sga "3 VIB 6.2.6" "more general",
  sga "3 VIB 6.5.5" "Clause a), special case",
  sga "3 VIB 7.3.0" "special case",
  sga "3 VIII 6.5" "special case",
  sga "3 VIII 6.7" "first item, special case"]
theorem exists_closedSubgroupScheme_center {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k))))
    [LocallyOfFiniteType G.X.hom] :
    ∃ Z : ClosedSubgroupScheme G,
      ∀ (T : Over (Spec (.of k))) (h : T ⟶ G.X),
        (∃ z : T ⟶ Z.carrier.X, z ≫ Z.ι.hom.hom = h) ↔ IsCentralPoint G h := by
  classical
  have : G.X.left.IsSeparated := isSeparated_of_groupScheme_over_field G
  have : IsSeparated G.X.hom := inferInstance
  let A (j : G.X.left.affineCover.I₀) : Over (Spec (.of k)) :=
    Over.mk (G.X.left.affineCover.f j ≫ G.X.hom)
  let jA (j : G.X.left.affineCover.I₀) : A j ⟶ G.X :=
    Over.homMk (G.X.left.affineCover.f j)
  have hc (j : G.X.left.affineCover.I₀) :
      ∃ W : Over G.X.left, IsClosedImmersion W.hom ∧
        ∀ (T : Over (Spec (.of k))) (h : T ⟶ G.X),
          Nonempty (Over.mk h.left ⟶ W) ↔
            ∀ (U : Over (Spec (.of k))) (x : U ⟶ A j) (t : U ⟶ T),
              (x ≫ jA j) * (t ≫ h) = (t ≫ h) * (x ≫ jA j) := by
    have : IsAffine (A j).left := inferInstanceAs (IsAffine (G.X.left.affineCover.X j))
    have : LocallyOfFiniteType (A j).hom := inferInstanceAs
      (LocallyOfFiniteType (G.X.left.affineCover.f j ≫ G.X.hom))
    obtain ⟨W, hw, h⟩ := exists_closed_universal_equalizer
      (hasWeilRestrictionAffineOverField k) (A j) G.X G.X
      ((fst (A j) G.X ≫ jA j) * snd (A j) G.X)
      (snd (A j) G.X * (fst (A j) G.X ≫ jA j))
    refine ⟨W, hw, fun T hT ↦ ?_⟩
    simpa only [MonObj.comp_mul, Category.assoc, lift_fst_assoc, lift_snd] using h T hT
  choose W hw hW using hc
  obtain ⟨Z, hz, hZ⟩ := exists_closed_intersection W hw
  let Z' : Over (Spec (.of k)) := Over.mk (Z.hom ≫ G.X.hom)
  let i : Z' ⟶ G.X := Over.homMk Z.hom
  have : IsClosedImmersion i.left := hz
  apply exists_closedSubgroupScheme_of_representsCentralPoints G Z' i
  intro T h
  have he : (∃ z : T ⟶ Z', z ≫ i = h) ↔ Nonempty (Over.mk h.left ⟶ Z) := by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨Over.homMk z.left (congrArg Over.Hom.left hz)⟩
    · rintro ⟨z⟩
      refine ⟨Over.homMk z.left ?_, Over.OverMorphism.ext z.w⟩
      change z.left ≫ Z.hom ≫ G.X.hom = T.hom
      rw [← Category.assoc, z.w]
      exact h.w
  rw [he, hZ, isCentralPoint_iff_affineCover]
  exact forall_congr' fun j ↦ hW j T h

end Stacks.Groupoids

end
