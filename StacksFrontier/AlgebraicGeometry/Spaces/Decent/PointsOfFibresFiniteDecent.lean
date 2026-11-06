module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.PullbackMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFibrePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint

/-!
# Finiteness of the points of a fibre over a monomorphic point

Let `D` be a cartesian square of algebraic spaces over `S` as in Tag 0AC1, with corners `W`,
`Z`, `X`, `Y`, and let `x` of `|X|` and `z` of `|Z|` have common image `y` in `|Y|`. Tag 0AC7:
the set of Tag 0AC2 attached to this data is finite as soon as `y` is represented by a
monomorphism from the spectrum of a field and the lower horizontal morphism `g` is quasi-finite
at `z`. In particular this holds when `Y` is decent and `g` is étale.

## Main definitions

* `AlgebraicGeometry.Space.PointsFibresDiagram.flip` exchanges the two off-diagonal corners of
  a cartesian square of Tag 0AC1.
* `AlgebraicGeometry.Space.PointsFibresDiagram.restrictBase` replaces the lower-right corner of
  a cartesian square of Tag 0AC1 by a space mapping to it by a monomorphism through which both
  of its morphisms factor.

## Main results

* `AlgebraicGeometry.Space.finite_fibrePoints_of_mono_of_isQuasiFiniteAt`: the set of Tag 0AC2
  is finite when `y` is represented by a monomorphism from the spectrum of a field and `g` is
  quasi-finite at `z`; `AlgebraicGeometry.Space.finite_fibrePoints_of_isDecentSpace_of_isEtale`
  is the case of a decent `Y` and an étale `g`.
* `AlgebraicGeometry.Space.finite_fibrePoints_of_finite_baseChange` and
  `AlgebraicGeometry.Space.finite_fibrePoints_of_finite_baseChange_left`: finiteness of the set
  of Tag 0AC2 follows from finiteness of the corresponding set after replacing the lower-left,
  respectively the upper-right, corner by anything mapping to it and carrying a lift of the
  prescribed point.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isEtale'`: an étale morphism of algebraic
  spaces over `S` is locally quasi-finite, with no algebraic-space hypothesis on either end.

## Implementation notes

The proof is a chain of reductions, each an application of Tag 0AC5
(`AlgebraicGeometry.Space.surjOn_fibrePoints_baseChange`) or of its reflection by
`AlgebraicGeometry.Space.PointsFibresDiagram.flip`, ending in Example 0AC3 for a square of
schemes (`AlgebraicGeometry.Space.finite_fibrePoints_of_quasiFiniteAt`). First `Z` is replaced
by the locally quasi-finite open subspace through which quasi-finiteness of `g` at `z` is
witnessed; the source instead transports quasi-finiteness of `g` at `z` to the base change by
part (2) of Tag 0ABM, which needs `g` locally of finite type. Then `Z` and `X` are base changed
along the monomorphism `Spec(k) ⟶ Y` representing `y`, the lower-right corner is replaced by
`Spec(k)` (`CategoryTheory.IsPullback.of_comp_mono`), and the two remaining corners are replaced
by surjective étale scheme atlases.

## References

* [Stacks Project, Tag 0AC7](https://stacks.math.columbia.edu/tag/0AC7)
* [Stacks Project, Tag 0AC1](https://stacks.math.columbia.edu/tag/0AC1)
* [Stacks Project, Tag 0AC2](https://stacks.math.columbia.edu/tag/0AC2)
* [Stacks Project, Tag 0AC3](https://stacks.math.columbia.edu/tag/0AC3)
* [Stacks Project, Tag 0AC5](https://stacks.math.columbia.edu/tag/0AC5)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03XL](https://stacks.math.columbia.edu/tag/03XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Étale morphisms are locally quasi-finite -/

/-- An étale morphism of algebraic spaces over `S` in the sense of Stacks 03FR is locally
quasi-finite in the sense of part (1) of Stacks 03XJ. Neither the source nor the target has to
be an algebraic space; compare `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isEtale`. -/
theorem isLocallyQuasiFinite_of_isEtale' {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsEtale B S hS f) :
    IsLocallyQuasiFinite B S hS f := by
  intro U V a b h ha hb hcomm
  have : Etale ((BigFppfOver.toScheme B S hS).map h) :=
    etale_of_comp_etale_chart B S hS (hf U a ha) hb hcomm
  exact locallyQuasiFinite_of_etale _

variable {B S hS}

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. -/
local instance (priority := high) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W)
    (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

namespace PointsFibresDiagram

/-! ### Exchanging the two off-diagonal corners -/

/-- The cartesian square of Tag 0AC1 obtained by reflecting a given one in its diagonal: the
upper-right and lower-left corners are exchanged, and so are the two morphisms out of the
upper-left corner and the two morphisms into the lower-right corner. -/
def flip (D : PointsFibresDiagram B S hS) : PointsFibresDiagram B S hS where
  W := D.W
  Z := D.X
  X := D.Z
  Y := D.Y
  W_isAlgebraicSpace := D.W_isAlgebraicSpace
  Z_isAlgebraicSpace := D.X_isAlgebraicSpace
  X_isAlgebraicSpace := D.Z_isAlgebraicSpace
  Y_isAlgebraicSpace := D.Y_isAlgebraicSpace
  q := D.p
  p := D.q
  f := D.g
  g := D.f
  isPullback := D.isPullback.flip

/-! ### Replacing the lower-right corner along a monomorphism -/

/-- The cartesian square of Tag 0AC1 obtained from a given one by replacing its lower-right
corner `Y` by an algebraic space `T` admitting a monomorphism `m : T ⟶ Y` through which both
morphisms of the square factor. -/
def restrictBase (D : PointsFibresDiagram B S hS)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (m : T ⟶ D.Y) (hm : Mono m) (f' : D.X ⟶ T) (g' : D.Z ⟶ T)
    (hf : f' ≫ m = D.f) (hg : g' ≫ m = D.g) :
    PointsFibresDiagram B S hS where
  W := D.W
  Z := D.Z
  X := D.X
  Y := T
  W_isAlgebraicSpace := D.W_isAlgebraicSpace
  Z_isAlgebraicSpace := D.Z_isAlgebraicSpace
  X_isAlgebraicSpace := D.X_isAlgebraicSpace
  Y_isAlgebraicSpace := hT
  q := D.q
  p := D.p
  f := f'
  g := g'
  isPullback := by
    have := hm
    exact IsPullback.of_comp_mono (m := m)
      (by rw [← cancel_mono m, Category.assoc, Category.assoc, hf, hg]; exact D.isPullback.w)
      (by rw [hf, hg]; exact D.isPullback)

end PointsFibresDiagram

/-! ### Transport of the set of Tag 0AC2 -/

/-- The set of Tag 0AC2 does not depend on the proof that the two prescribed points have a
common image, so two instances of it at equal points are equal. -/
theorem fibrePoints_congr (D : PointsFibresDiagram B S hS) {x : points B S hS D.X}
    {z z' : points B S hS D.Z} (hz : z = z')
    {h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z}
    {h' : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z'} :
    fibrePoints D x z h = fibrePoints D x z' h' := by
  subst hz
  rfl

/-- Reflecting a cartesian square of Tag 0AC1 in its diagonal exchanges the roles of the two
prescribed points and leaves the set of Tag 0AC2 unchanged. -/
theorem fibrePoints_flip (D : PointsFibresDiagram B S hS) (x : points B S hS D.X)
    (z : points B S hS D.Z)
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z) :
    fibrePoints (D.flip) z x h.symm = fibrePoints D x z h :=
  Set.ext fun _ ↦ and_comm

/-- Replacing the lower-right corner of a cartesian square of Tag 0AC1 along a monomorphism
leaves the set of Tag 0AC2 unchanged. -/
theorem fibrePoints_restrictBase (D : PointsFibresDiagram B S hS)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (m : T ⟶ D.Y) (hm : Mono m) (f' : D.X ⟶ T) (g' : D.Z ⟶ T)
    (hf : f' ≫ m = D.f) (hg : g' ≫ m = D.g)
    (x : points B S hS D.X) (z : points B S hS D.Z)
    (h' : pointsMap B S hS D.X f' x = pointsMap B S hS D.Z g' z)
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z) :
    fibrePoints (D.restrictBase hT m hm f' g' hf hg) x z h' = fibrePoints D x z h :=
  rfl

/-! ### The two reduction steps -/

/-- **Reduction of Tag 0AC2 along a base change of the lower-left corner.** If the set of Tag
0AC2 is finite after replacing the lower-left corner `Z` of a cartesian square of Tag 0AC1 by
anything mapping to it and carrying a lift of the prescribed point `z`, then it is finite. -/
theorem finite_fibrePoints_of_finite_baseChange (D : PointsFibresDiagram B S hS)
    (x : points B S hS D.X) (z : points B S hS D.Z)
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    {W' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW' : IsAlgebraicSpace B S hS W') (hZ' : IsAlgebraicSpace B S hS Z')
    {t : Z' ⟶ D.Z} {r : W' ⟶ D.W} {q' : W' ⟶ Z'} (sq : IsPullback r q' D.q t)
    (z' : points B S hS Z') (hz' : pointsMap B S hS Z' t z' = z)
    (h' : pointsMap B S hS D.X D.f x = pointsMap B S hS Z' (t ≫ D.g) z')
    (hfin : (fibrePoints (D.baseChange hW' hZ' sq) x z' h').Finite) :
    (fibrePoints D x z h).Finite := by
  have key : (fibrePoints D x (pointsMap B S hS Z' t z')
      (by rw [h', pointsMap_comp_apply])).Finite :=
    Set.Finite.subset (hfin.image (pointsMap B S hS W' r))
      (surjOn_fibrePoints_baseChange D hW' hZ' sq x z' h')
  rwa [fibrePoints_congr D hz'] at key

/-- **Reduction of Tag 0AC2 along a base change of the upper-right corner.** If the set of Tag
0AC2 is finite after replacing the upper-right corner `X` of a cartesian square of Tag 0AC1 by
anything mapping to it and carrying a lift of the prescribed point `x`, then it is finite. -/
theorem finite_fibrePoints_of_finite_baseChange_left (D : PointsFibresDiagram B S hS)
    (x : points B S hS D.X) (z : points B S hS D.Z)
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    {W' X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW' : IsAlgebraicSpace B S hS W') (hX' : IsAlgebraicSpace B S hS X')
    {t : X' ⟶ D.X} {r : W' ⟶ D.W} {p' : W' ⟶ X'} (sq : IsPullback r p' D.p t)
    (x' : points B S hS X') (hx' : pointsMap B S hS X' t x' = x)
    (h' : pointsMap B S hS D.Z D.g z = pointsMap B S hS X' (t ≫ D.f) x')
    (hfin : (fibrePoints ((D.flip).baseChange hW' hX' sq) z x' h').Finite) :
    (fibrePoints D x z h).Finite := by
  rw [← fibrePoints_flip D x z h]
  exact finite_fibrePoints_of_finite_baseChange D.flip z x h.symm hW' hX' sq x' hx'
    h' hfin

/-! ### Composing with an étale chart -/

/-- Precomposing a locally quasi-finite morphism of algebraic spaces over `S` with a morphism
which is étale after every representable base change is locally quasi-finite. -/
theorem isLocallyQuasiFinite_comp_of_presheafEtale
    {E F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : E ⟶ F} {g : F ⟶ G}
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hg : IsLocallyQuasiFinite B S hS g) :
    IsLocallyQuasiFinite B S hS (a ≫ g) := by
  intro U V a₀ b₀ h₀ ha₀ hb₀ hcomm
  have := isMultiplicative_presheaf_etale B S hS
  refine hg U V (a₀ ≫ a) b₀ h₀ (MorphismProperty.comp_mem _ _ _ ha₀ ha) hb₀ ?_
  rw [Category.assoc]
  exact hcomm

/-! ### The scheme-level endgame -/

/-- The `AlgebraicGeometry.Space.PointsFibresDiagram.SchemeRepresentation` of a cartesian
square of Tag 0AC1 whose three non-pullback corners are representable presheaves: each corner
is represented by its own chosen representing object, through
`CategoryTheory.Functor.reprW`. -/
noncomputable def PointsFibresDiagram.schemeRepresentationOfRepresentable
    (D : PointsFibresDiagram B S hS) [D.X.IsRepresentable] [D.Y.IsRepresentable]
    [D.Z.IsRepresentable] :
    D.SchemeRepresentation where
  X := D.X.reprX
  Y := D.Y.reprX
  Z := D.Z.reprX
  f := yoneda.preimage (D.X.reprW.hom ≫ D.f ≫ D.Y.reprW.inv)
  g := yoneda.preimage (D.Z.reprW.hom ≫ D.g ≫ D.Y.reprW.inv)
  iX := D.X.reprW.symm
  iY := D.Y.reprW.symm
  iZ := D.Z.reprW.symm
  f_compat := by simp
  g_compat := by simp

/-- Tag 0AC3 for a cartesian square of Tag 0AC1 whose three non-pullback corners are
representable and whose lower horizontal morphism is locally quasi-finite: the set of Tag 0AC2
is finite. -/
theorem finite_fibrePoints_of_representable (D : PointsFibresDiagram B S hS)
    (hX : D.X.IsRepresentable) (hY : D.Y.IsRepresentable) (hZ : D.Z.IsRepresentable)
    (x : points B S hS D.X) (z : points B S hS D.Z)
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    (hg : IsLocallyQuasiFinite B S hS D.g) :
    (fibrePoints D x z h).Finite := by
  have := hX
  have := hY
  have := hZ
  have hgr := hg D.Z.reprX D.Y.reprX D.Z.reprW.hom D.Y.reprW.hom
    (D.schemeRepresentationOfRepresentable).g
    (presheaf_etale_of_iso B S hS D.Z.reprW) (presheaf_etale_of_iso B S hS D.Y.reprW)
    (by simp [PointsFibresDiagram.schemeRepresentationOfRepresentable])
  exact finite_fibrePoints_of_quasiFiniteAt D.schemeRepresentationOfRepresentable x z h
    ((forall_quasiFiniteAt_iff _).mpr ⟨hgr.1, hgr.2⟩ _)

/-! ### The reduction to a one-point base -/

/-- Any two morphisms of algebraic spaces with a common target have a pullback square whose
vertex is an algebraic space. -/
private theorem exists_isPullback_isAlgebraicSpace {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (f : F ⟶ H) (g : G ⟶ H) :
    ∃ (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (p : P ⟶ F) (q : P ⟶ G),
      IsPullback p q f g ∧ IsAlgebraicSpace B S hS P :=
  ⟨_, _, _, IsPullback.of_hasPullback f g, isAlgebraicSpace_pullback B S hS f g hF hG hH⟩

/-- If both morphisms of a cartesian square of Tag 0AC1 factor through a monomorphism from a
representable presheaf whose underlying scheme has at most one point, and the factorisation of
the lower horizontal morphism is locally quasi-finite, then the set of Tag 0AC2 is finite. -/
private theorem finite_fibrePoints_of_monoFactorisation (D : PointsFibresDiagram B S hS)
    (x : points B S hS D.X) (z : points B S hS D.Z)
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    {V₀ : BigFppfOver B S hS} (m : yoneda.obj V₀ ⟶ D.Y) (hm : Mono m)
    (hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj V₀))
    {f' : D.X ⟶ yoneda.obj V₀} {g' : D.Z ⟶ yoneda.obj V₀}
    (hf : f' ≫ m = D.f) (hg : g' ≫ m = D.g)
    (hg' : IsLocallyQuasiFinite B S hS g') :
    (fibrePoints D x z h).Finite := by
  have hpts : Subsingleton (points B S hS (yoneda.obj V₀)) :=
    (pointsEquivScheme B S hS V₀).subsingleton
  have helim : ∀ a b : points B S hS (yoneda.obj V₀), a = b := hpts.allEq
  have hV₀ : IsAlgebraicSpace B S hS (yoneda.obj V₀) := isAlgebraicSpace_yoneda B S hS V₀
  rw [← fibrePoints_restrictBase D hV₀ m hm f' g' hf hg x z (helim _ _) h]
  obtain ⟨V, b, hbsurj, hbet⟩ := D.X_isAlgebraicSpace.exists_atlas
  obtain ⟨v₁, hv₁⟩ := isSurjective_of_presheafSurjective B S hS b hbsurj x
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  obtain ⟨W₄, r₄, p₄, sq₄, hW₄⟩ := exists_isPullback_isAlgebraicSpace
    D.W_isAlgebraicSpace hV D.X_isAlgebraicSpace D.p b
  refine finite_fibrePoints_of_finite_baseChange_left
    (D.restrictBase hV₀ m hm f' g' hf hg) x z (helim _ _) hW₄ hV sq₄ v₁ hv₁ (helim _ _) ?_
  obtain ⟨U, a, hasurj, haet⟩ := D.Z_isAlgebraicSpace.exists_atlas
  obtain ⟨u₁, hu₁⟩ := isSurjective_of_presheafSurjective B S hS a hasurj z
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  obtain ⟨W₅, r₅, p₅, sq₅, hW₅⟩ := exists_isPullback_isAlgebraicSpace hW₄ hU
    D.Z_isAlgebraicSpace (r₄ ≫ D.q) a
  refine finite_fibrePoints_of_finite_baseChange_left
    ((D.restrictBase hV₀ m hm f' g' hf hg).flip.baseChange hW₄ hV sq₄) z v₁ (helim _ _)
    hW₅ hU sq₅ u₁ hu₁ (helim _ _) ?_
  exact finite_fibrePoints_of_representable
    (((D.restrictBase hV₀ m hm f' g' hf hg).flip.baseChange hW₄ hV sq₄).flip.baseChange hW₅ hU
      sq₅)
    (inferInstanceAs (Functor.IsRepresentable (yoneda.obj V)))
    (inferInstanceAs (Functor.IsRepresentable (yoneda.obj V₀)))
    (inferInstanceAs (Functor.IsRepresentable (yoneda.obj U)))
    v₁ u₁ (helim _ _) (isLocallyQuasiFinite_comp_of_presheafEtale haet hg')

/-- The variant of `AlgebraicGeometry.Space.finite_fibrePoints_of_monoFactorisation` whose
local quasi-finiteness hypothesis is on the factorisation of the *right vertical* morphism,
obtained by reflecting the square in its diagonal. -/
private theorem finite_fibrePoints_of_monoFactorisation_left (D : PointsFibresDiagram B S hS)
    (x : points B S hS D.X) (z : points B S hS D.Z)
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    {V₀ : BigFppfOver B S hS} (m : yoneda.obj V₀ ⟶ D.Y) (hm : Mono m)
    (hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj V₀))
    {f' : D.X ⟶ yoneda.obj V₀} {g' : D.Z ⟶ yoneda.obj V₀}
    (hf : f' ≫ m = D.f) (hg : g' ≫ m = D.g)
    (hf' : IsLocallyQuasiFinite B S hS f') :
    (fibrePoints D x z h).Finite := by
  rw [← fibrePoints_flip D x z h]
  exact finite_fibrePoints_of_monoFactorisation D.flip z x h.symm m hm hsub hg hf hf'

/-! ### Tag 0AC7 -/

/-- In a cartesian square of Tag 0AC1, the set of Tag 0AC2 attached to two points `x` of `|X|`
and `z` of `|Z|` with common image `y` in `|Y|` is finite whenever `y` can be represented by a
monomorphism from the spectrum of a field and the lower horizontal morphism `g` is quasi-finite
at `z`. -/
@[stacks 0AC7 "finite fibre over a monomorphic point"]
theorem finite_fibrePoints_of_mono_of_isQuasiFiniteAt (D : PointsFibresDiagram B S hS)
    (x : points B S hS D.X) (z : points B S hS D.Z)
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    (hy : HasMonomorphicFieldRepresentative B S hS D.Y (pointsMap B S hS D.X D.f x))
    (hqf : IsQuasiFiniteAt B S hS D.g z) :
    (fibrePoints D x z h).Finite := by
  obtain ⟨p, hpy, hmono⟩ := hy
  obtain ⟨Z₀, hZ₀, z₀, hz₀, hqf₀⟩ := hqf
  have hT : IsAlgebraicSpace B S hS (yoneda.obj p.siteObject) :=
    isAlgebraicSpace_yoneda B S hS p.siteObject
  have hVsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  obtain ⟨W₀, r₀, q₀, sq₀, hW₀⟩ := exists_isPullback_isAlgebraicSpace
    D.W_isAlgebraicSpace hZ₀.1 D.Z_isAlgebraicSpace D.q Z₀.ι
  obtain ⟨Zk, prZ, tZ, sqZ, hZk⟩ := exists_isPullback_isAlgebraicSpace hT hZ₀.1
    D.Y_isAlgebraicSpace (fieldMorphism B S hS D.Y p) (Z₀.ι ≫ D.g)
  obtain ⟨W₁, r₁, q₁, sq₁, hW₁⟩ :=
    exists_isPullback_isAlgebraicSpace hW₀ hZk hZ₀.1 q₀ tZ
  obtain ⟨Xk, prX, tX, sqX, hXk⟩ := exists_isPullback_isAlgebraicSpace hT
    D.X_isAlgebraicSpace D.Y_isAlgebraicSpace (fieldMorphism B S hS D.Y p) D.f
  obtain ⟨W₂, r₂, p₂, sq₂, hW₂⟩ := exists_isPullback_isAlgebraicSpace hW₁ hXk
    D.X_isAlgebraicSpace (r₁ ≫ r₀ ≫ D.p) tX
  obtain ⟨z₁, -, hz₁⟩ := exists_points_of_isPullback B S hS sqZ
    ((p.tautological B S hS).class B S hS (yoneda.obj p.siteObject)) z₀
    ((FieldValuedPoint.pointsMap_eq_class B S hS p _).trans
      (by rw [pointsMap_comp_apply, hz₀, ← h]; exact hpy))
  obtain ⟨x₁, -, hx₁⟩ := exists_points_of_isPullback B S hS sqX
    ((p.tautological B S hS).class B S hS (yoneda.obj p.siteObject)) x
    ((FieldValuedPoint.pointsMap_eq_class B S hS p _).trans hpy)
  have h₀ : pointsMap B S hS D.X D.f x =
      pointsMap B S hS Z₀.toFunctor (Z₀.ι ≫ D.g) z₀ := by
    rw [pointsMap_comp_apply, hz₀]; exact h
  have h₁ : pointsMap B S hS D.X D.f x =
      pointsMap B S hS Zk (tZ ≫ Z₀.ι ≫ D.g) z₁ := by
    rw [pointsMap_comp_apply, hz₁]; exact h₀
  have hx₁' : pointsMap B S hS Xk (tX ≫ D.f) x₁ = pointsMap B S hS D.X D.f x := by
    rw [pointsMap_comp_apply, hx₁]
  refine finite_fibrePoints_of_finite_baseChange D x z h hW₀ hZ₀.1 sq₀ z₀ hz₀ h₀ ?_
  refine finite_fibrePoints_of_finite_baseChange (D.baseChange hW₀ hZ₀.1 sq₀) x z₀ h₀
    hW₁ hZk sq₁ z₁ hz₁ h₁ ?_
  refine finite_fibrePoints_of_finite_baseChange_left
    ((D.baseChange hW₀ hZ₀.1 sq₀).baseChange hW₁ hZk sq₁) x z₁ h₁ hW₂ hXk sq₂ x₁ hx₁
    (h₁.symm.trans hx₁'.symm) ?_
  exact finite_fibrePoints_of_monoFactorisation_left
    (((D.baseChange hW₀ hZ₀.1 sq₀).baseChange hW₁ hZk sq₁).flip.baseChange hW₂ hXk sq₂)
    z₁ x₁ (h₁.symm.trans hx₁'.symm) (fieldMorphism B S hS D.Y p) hmono hVsub sqZ.w sqX.w
    (IsLocallyQuasiFinite.of_isPullback B S hS sqZ hZ₀.1 D.Y_isAlgebraicSpace hqf₀)

/-- In a cartesian square of Tag 0AC1 whose lower-right corner is a decent algebraic space and
whose lower horizontal morphism is étale, the set of Tag 0AC2 is finite. -/
@[stacks 0AC7 "special case: decent lower-right corner and étale lower horizontal morphism"]
theorem finite_fibrePoints_of_isDecentSpace_of_isEtale (D : PointsFibresDiagram B S hS)
    (x : points B S hS D.X) (z : points B S hS D.Z)
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    (hY : IsDecentSpace B S hS D.Y) (hg : IsEtale B S hS D.g) :
    (fibrePoints D x z h).Finite :=
  finite_fibrePoints_of_mono_of_isQuasiFiniteAt D x z h
    (hY.hasMonomorphicFieldRepresentative B S hS D.Y _)
    (isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS D.Z_isAlgebraicSpace
      (isLocallyQuasiFinite_of_isEtale' B S hS hg) z)

end AlgebraicGeometry.Space

end
