module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BigSitesPushforward.ClosedImmersionCoverings
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSheaf

/-!
# Étale-local lifting across a square-zero thickening

Let `i : T ⟶ T'` be a square-zero closed immersion and let `W ⟶ T` be surjective and étale.
The ambient scheme `T'` is then covered by affine schemes étale over it whose base changes to
`T` map to `W` over `T`. This is the geometric input for the descent half of Stacks 04CY: a
section of the intermediate presheaf over `T` extends over an étale neighbourhood in `T'`,
because formal smoothness of the composite produces the lift over each member of such a cover.

## Main results

* `AlgebraicGeometry.exists_affine_etale_cover_of_isThickening` is the statement about schemes:
  an affine étale cover of the ambient scheme refining a given étale cover of the closed
  subscheme.
* `AlgebraicGeometry.Space.app_tautological_section_representing` identifies the image in the
  intermediate presheaf of the tautological section over a representing object.
* `AlgebraicGeometry.Space.exists_affine_etale_cover_lift` transports it to the big fppf site
  over a scheme, where the lift is a morphism of the site.
* `AlgebraicGeometry.Space.exists_etale_affine_local_lift` is the descent half of Stacks 04CY
  in its local form: a formally smooth composite in a representable, surjective, étale
  situation admits lifts over an affine étale neighbourhood of every point.

## Implementation notes

The scheme-level cover is the affine refinement of
`AlgebraicGeometry.exists_etale_zariskiCover_baseChange_of_isClosedImmersion`, which covers a
scheme étale over a closed subscheme by base changes of schemes étale over the ambient scheme.
Those schemes are refined by their affine covers, which keeps them étale over the ambient
scheme and makes them objects of the chosen site: an affine scheme étale over an object of the
site is of finite type over it, hence of no larger size.

Joint surjectivity of the refined family onto the *ambient* scheme — rather than onto the
given étale scheme over the closed subscheme — is what the consumers use, and it is where
surjectivity of the closed immersion and of the étale morphism enter. A square-zero closed
immersion is surjective by `Stacks.Thickenings.IsFirstOrderThickening.isThickening`.

The lifting clause is stated for an arbitrary commutative square over `i` and a member of the
cover, not for a chosen fibre product, and it does not ask the square to be cartesian: the
comparison morphism into the chosen fibre product of schemes exists for any commutative square,
and composing it with the covering lift already has the required factorization.

## References

* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
* [Stacks Project, Tag 04E3](https://stacks.math.columbia.edu/tag/04E3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- **An affine étale cover of a thickening refining an étale cover of its closed subscheme.**
Let `i : T ⟶ T'` be a surjective closed immersion and let `p : W ⟶ T` be surjective and étale.
Then `T'` is covered by affine schemes `V k` étale over it, each equipped with a morphism from
`V k ×_{T'} T` to `W` over `T`.

This is the affine refinement of `exists_etale_zariskiCover_baseChange_of_isClosedImmersion`;
joint surjectivity is stated for `T'`, which is what consumers need and is where the two
surjectivity hypotheses are used. -/
public theorem exists_affine_etale_cover_of_isThickening
    {T T' W : Scheme.{u}} (i : T ⟶ T') [IsClosedImmersion i]
    (hi : Function.Surjective i.base) (p : W ⟶ T) [Etale p]
    (hp : Function.Surjective p.base) :
    ∃ (ι : Type u) (V : ι → Scheme.{u}) (q : ∀ k, V k ⟶ T')
      (l : ∀ k, pullback (q k) i ⟶ W),
      (∀ k, IsAffine (V k)) ∧ (∀ k, Etale (q k)) ∧
        (∀ k, l k ≫ p = pullback.snd (q k) i) ∧
          ∀ t' : T', ∃ (k : ι) (x : (V k : Scheme.{u})), (q k).base x = t' := by
  classical
  obtain ⟨J, V₀, q₀, g₀, hq₀, hg₀, hcov⟩ :=
    exists_etale_zariskiCover_baseChange_of_isClosedImmersion i p
  obtain ⟨hsurj₀, -⟩ :=
    (Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).mp hcov
  refine ⟨(k : J) × (V₀ k).affineCover.I₀,
    fun c ↦ (V₀ c.1).affineCover.X c.2,
    fun c ↦ (V₀ c.1).affineCover.f c.2 ≫ q₀ c.1, fun c ↦ ?_, fun c ↦ inferInstance,
    fun c ↦ ?_, ?_, ?_⟩
  · -- the comparison morphism into the unrefined fibre product, followed by its lift
    refine pullback.lift (pullback.fst _ i ≫ (V₀ c.1).affineCover.f c.2)
      (pullback.snd _ i) ?_ ≫ g₀ c.1
    rw [Category.assoc]
    exact pullback.condition
  · have hqc : Etale (q₀ c.1) := hq₀ c.1
    infer_instance
  · intro c
    have hqc : Etale (q₀ c.1) := hq₀ c.1
    rw [Category.assoc, hg₀ c.1]
    exact pullback.lift_snd _ _ _
  · -- joint surjectivity onto the ambient scheme
    intro t'
    obtain ⟨t, rfl⟩ := hi t'
    obtain ⟨w, rfl⟩ := hp t
    obtain ⟨k, y, hy⟩ := hsurj₀ w
    have hqk : Etale (q₀ k) := hq₀ k
    obtain ⟨c, z, hz⟩ := (V₀ k).affineCover.exists_eq (pullback.fst (q₀ k) i y)
    refine ⟨⟨k, c⟩, z, ?_⟩
    have hcond : (pullback.fst (q₀ k) i ≫ q₀ k) y = (pullback.snd (q₀ k) i ≫ i) y :=
      congrArg (fun m : pullback (q₀ k) i ⟶ T' ↦ m y)
        (pullback.condition (f := q₀ k) (g := i))
    have hsnd : (g₀ k ≫ p) y = (pullback.snd (q₀ k) i) y :=
      congrArg (fun m : pullback (q₀ k) i ⟶ T ↦ m y) (hg₀ k)
    simp only [Scheme.Hom.comp_apply] at hcond hsnd
    show ((V₀ k).affineCover.f c ≫ q₀ k) z = i (p w)
    rw [Scheme.Hom.comp_apply, hz, hcond, ← hsnd, hy]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The tautological section of the source presheaf over an object representing the base
change of a transformation along a section of its target lies over that section. -/
public theorem app_tautological_section_representing
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G} {T P : BigFppfOver B S hS}
    {x : G.obj (op T)} {p : P ⟶ T} {q : yoneda.obj P ⟶ F}
    (hpb : IsPullback q (yoneda.map p) a (yonedaEquiv.symm x)) :
    a.app (op P) (q.app (op P) (𝟙 P)) = G.map p.op x := by
  simpa using congrArg (fun α ↦ α.app (op P) (𝟙 P)) hpb.w

/-- **An affine étale cover of a thickened test object, in the big fppf site.** Let
`i : T ⟶ T'` be a square-zero closed immersion of objects of the big fppf site over `S` and
let `p : W ⟶ T` be surjective and étale. Then `T'` admits a jointly surjective family of
affine objects `U k` étale over it such that every commutative square over `i` and `j k`
factors through `p`. -/
public theorem exists_affine_etale_cover_lift
    {T T' W : BigFppfOver B S hS} {i : T ⟶ T'}
    (hi : IsSquareZeroClosedImmersion B S hS i) {p : W ⟶ T}
    (hpe : Etale ((BigFppfOver.toScheme B S hS).map p))
    (hps : Function.Surjective ((BigFppfOver.toScheme B S hS).map p).base) :
    ∃ (ι : Type u) (U : ι → BigFppfOver B S hS) (j : ∀ k, U k ⟶ T'),
      (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (U k))) ∧
      (∀ k, Etale ((BigFppfOver.toScheme B S hS).map (j k))) ∧
      (∀ t' : (BigFppfOver.toScheme B S hS).obj T',
        ∃ (k : ι) (x : (BigFppfOver.toScheme B S hS).obj (U k)),
          ((BigFppfOver.toScheme B S hS).map (j k)).base x = t') ∧
      ∀ (k : ι) (V : BigFppfOver B S hS) (f : V ⟶ T) (g : V ⟶ U k),
        f ≫ i = g ≫ j k → ∃ m : V ⟶ W, m ≫ p = f := by
  classical
  have hiClosed : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) := hi.1
  have hpe' : Etale ((BigFppfOver.toScheme B S hS).map p) := hpe
  obtain ⟨ι, V, q, l, hVaff, hqet, hlp, hqsurj⟩ :=
    exists_affine_etale_cover_of_isThickening ((BigFppfOver.toScheme B S hS).map i)
      (Stacks.Thickenings.IsFirstOrderThickening.isThickening
        (i := (BigFppfOver.toScheme B S hS).map i) hi).2
      ((BigFppfOver.toScheme B S hS).map p) hps
  -- each member of the cover is an object of the site, étale over `T'`
  have hsize : ∀ k, B.Contains (V k) := by
    intro k
    have hV : IsAffine (V k) := hVaff k
    have hq : Etale (q k) := hqet k
    exact (Scheme.size_le_of_locallyOfFiniteType (q k)).trans_lt T'.left.property
  let Usch : ι → B.Schemes := fun k ↦ ⟨V k, hsize k⟩
  let qs : ∀ k, Usch k ⟶ T'.left := fun k ↦
    B.inclusion.preimage (X := Usch k) (Y := T'.left) (q k)
  have hqs : ∀ k, B.inclusion.map (qs k) = q k := fun k ↦ B.inclusion.map_preimage _
  refine ⟨ι, fun k ↦ Over.mk (qs k ≫ T'.hom), fun k ↦ Over.homMk (qs k) rfl,
    fun k ↦ hVaff k, fun k ↦ (hqs k) ▸ hqet k, ?_, ?_⟩
  · intro t'
    obtain ⟨k, x, hx⟩ := hqsurj t'
    exact ⟨k, x, (hqs k) ▸ hx⟩
  · intro k V₀ f g hsq
    have hq : Etale (q k) := hqet k
    have hjmap : (BigFppfOver.toScheme B S hS).map
        (Over.homMk (qs k) rfl : (Over.mk (qs k ≫ T'.hom) : BigFppfOver B S hS) ⟶ T') =
        q k := hqs k
    have hsqS : (BigFppfOver.toScheme B S hS).map g ≫ q k =
        (BigFppfOver.toScheme B S hS).map f ≫ (BigFppfOver.toScheme B S hS).map i := by
      rw [← hjmap, ← Functor.map_comp, ← Functor.map_comp, hsq]
    set m₀ := pullback.lift ((BigFppfOver.toScheme B S hS).map g)
      ((BigFppfOver.toScheme B S hS).map f) hsqS ≫ l k with hm₀
    have hmSp : m₀ ≫ (BigFppfOver.toScheme B S hS).map p =
        (BigFppfOver.toScheme B S hS).map f := by
      rw [hm₀, Category.assoc, hlp k]
      exact pullback.lift_snd _ _ _
    have hhom : ∀ {X Y : BigFppfOver B S hS} (e : X ⟶ Y), B.inclusion.map X.hom =
        (BigFppfOver.toScheme B S hS).map e ≫ B.inclusion.map Y.hom := fun e ↦ by
      rw [← Over.w e, Functor.map_comp]
      rfl
    refine ⟨Over.homMk (B.inclusion.preimage (X := V₀.left) (Y := W.left) m₀) ?_, ?_⟩
    · apply B.inclusion.map_injective
      rw [Functor.map_comp, B.inclusion.map_preimage, hhom p, hhom f, ← Category.assoc, hmSp]
    · apply Functor.map_injective (F := BigFppfOver.toScheme B S hS)
      rw [Functor.map_comp]
      show B.inclusion.map (B.inclusion.preimage _) ≫
        (BigFppfOver.toScheme B S hS).map p = _
      rw [B.inclusion.map_preimage]
      exact hmSp

/-- **Stacks 04CY, the local form of the descent half.** In a representable, surjective, étale
situation `F ⟶ G ⟶ H` over an affine square-zero thickening `i : T ⟶ T'`, a formally smooth
composite admits, over every point of `T`, an affine étale neighbourhood `U' ⟶ T'` of its
image and a section of `G` over `U'` which lifts the given section of `H` and agrees with the
given section of `G` over `T` after restriction to every common refinement. -/
@[stacks 04CY "local_formal_smooth_lift"]
public theorem exists_etale_affine_local_lift
    (D : RepresentableSurjectiveEtaleSituation.{u})
    (T T' : BigFppfOver D.B D.S D.hS) (i : T ⟶ T')
    (_hT' : IsAffine ((BigFppfOver.toScheme D.B D.S D.hS).obj T'))
    (hi : IsSquareZeroClosedImmersion D.B D.S D.hS i)
    (x : D.G.obj (op T)) (y : D.H.obj (op T'))
    (hxy : D.b.app (op T) x = D.H.map i.op y)
    (hsmooth : FormallySmooth (D.a ≫ D.b))
    (t : (BigFppfOver.toScheme D.B D.S D.hS).obj T) :
    ∃ (U' : BigFppfOver D.B D.S D.hS) (j : U' ⟶ T') (z : D.G.obj (op U')),
      IsAffine ((BigFppfOver.toScheme D.B D.S D.hS).obj U') ∧
      Etale ((BigFppfOver.toScheme D.B D.S D.hS).map j) ∧
      (∃ u : (BigFppfOver.toScheme D.B D.S D.hS).obj U',
        ((BigFppfOver.toScheme D.B D.S D.hS).map j).base u =
          ((BigFppfOver.toScheme D.B D.S D.hS).map i).base t) ∧
      D.b.app (op U') z = D.H.map j.op y ∧
      ∀ (V : BigFppfOver D.B D.S D.hS) (f : V ⟶ T) (g : V ⟶ U'),
        f ≫ i = g ≫ j → D.G.map f.op x = D.G.map g.op z := by
  classical
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme D.B D.S D.hS
  have hpull : HasPullbacks (BigFppfOver D.B D.S D.hS) := inferInstance
  -- the representing object of the base change of `D.a` along the given section of `G`
  let g : yoneda.obj T ⟶ D.G := yonedaEquiv.symm x
  let W := D.representable_a.pullback g
  let p : W ⟶ T := D.representable_a.snd g
  let q : yoneda.obj W ⟶ D.F := D.representable_a.fst g
  have hpb : IsPullback q (yoneda.map p) D.a g := D.representable_a.isPullback g
  have hpe : Etale ((BigFppfOver.toScheme D.B D.S D.hS).map p) :=
    D.etale_a.property g q p hpb
  have hps : Function.Surjective
      ((BigFppfOver.toScheme D.B D.S D.hS).map p).base :=
    (D.surjective_a.property g q p hpb).surj
  obtain ⟨ι, U, j, hUaff, hjet, hjsurj, hlift⟩ :=
    exists_affine_etale_cover_lift D.B D.S D.hS hi hpe hps
  obtain ⟨k, u, hu⟩ := hjsurj (((BigFppfOver.toScheme D.B D.S D.hS).map i).base t)
  -- the base change of the thickening to the chosen member of the cover
  let f : Limits.pullback i (j k) ⟶ T := pullback.fst i (j k)
  let v : Limits.pullback i (j k) ⟶ U k := pullback.snd i (j k)
  have hsq : f ≫ i = v ≫ j k := pullback.condition
  have hsqS : IsPullback ((BigFppfOver.toScheme D.B D.S D.hS).map f)
      ((BigFppfOver.toScheme D.B D.S D.hS).map v)
      ((BigFppfOver.toScheme D.B D.S D.hS).map i)
      ((BigFppfOver.toScheme D.B D.S D.hS).map (j k)) :=
    (IsPullback.of_hasPullback i (j k)).map (BigFppfOver.toScheme D.B D.S D.hS)
  have hvThick : IsSquareZeroClosedImmersion D.B D.S D.hS v :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Stacks.Thickenings.IsFirstOrderThickening.{u}) hsqS hi
  have hvClosed : IsClosedImmersion ((BigFppfOver.toScheme D.B D.S D.hS).map v) := hvThick.1
  have hUk : IsAffine ((BigFppfOver.toScheme D.B D.S D.hS).obj (U k)) := hUaff k
  have hVaff : IsAffine ((BigFppfOver.toScheme D.B D.S D.hS).obj
      (Limits.pullback i (j k))) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme D.B D.S D.hS).map v)
  -- the lift of the square into the representing object, and the section of `F` it carries
  obtain ⟨m, hm⟩ := hlift k (Limits.pullback i (j k)) f v hsq
  have hξa : D.a.app (op (Limits.pullback i (j k)))
      (D.F.map m.op (q.app (op W) (𝟙 W))) = D.G.map f.op x := by
    calc D.a.app (op (Limits.pullback i (j k))) (D.F.map m.op (q.app (op W) (𝟙 W)))
        = D.G.map m.op (D.a.app (op W) (q.app (op W) (𝟙 W))) :=
          D.a.naturality_apply m.op (q.app (op W) (𝟙 W))
      _ = D.G.map m.op (D.G.map p.op x) := by
        rw [app_tautological_section_representing D.B D.S D.hS hpb]
      _ = D.G.map (m ≫ p).op x := ExtendingFunctors.map_map_apply D.G m p x
      _ = D.G.map f.op x := by rw [hm]
  have hbase : (D.a ≫ D.b).app (op (Limits.pullback i (j k)))
      (D.F.map m.op (q.app (op W) (𝟙 W))) = D.H.map v.op (D.H.map (j k).op y) := by
    calc (D.a ≫ D.b).app (op (Limits.pullback i (j k)))
          (D.F.map m.op (q.app (op W) (𝟙 W)))
        = D.b.app (op (Limits.pullback i (j k))) (D.G.map f.op x) := by rw [← hξa]; rfl
      _ = D.H.map f.op (D.H.map i.op y) := by rw [D.b.naturality_apply f.op x, hxy]
      _ = D.H.map (f ≫ i).op y := ExtendingFunctors.map_map_apply D.H f i y
      _ = D.H.map (v ≫ j k).op y := by rw [hsq]
      _ = D.H.map v.op (D.H.map (j k).op y) := (ExtendingFunctors.map_map_apply D.H v (j k) y).symm
  obtain ⟨zF, hzF⟩ := hsmooth (Limits.pullback i (j k)) (U k) hVaff hUk v hvThick
    (D.F.map m.op (q.app (op W) (𝟙 W))) (D.H.map (j k).op y) hbase
  refine ⟨U k, j k, D.a.app (op (U k)) zF, hUk, hjet k, ⟨u, hu⟩, hzF.2, ?_⟩
  -- agreement over the base change, propagated to every common refinement
  have hred : D.G.map v.op (D.a.app (op (U k)) zF) = D.G.map f.op x := by
    calc D.G.map v.op (D.a.app (op (U k)) zF)
        = D.a.app (op (Limits.pullback i (j k))) (D.F.map v.op zF) :=
          (D.a.naturality_apply v.op zF).symm
      _ = D.a.app (op (Limits.pullback i (j k)))
            (D.F.map m.op (q.app (op W) (𝟙 W))) := congrArg _ hzF.1
      _ = D.G.map f.op x := hξa
  intro V₀ f₀ g₀ hcomp
  have hlift₀ : (pullback.lift f₀ g₀ hcomp : V₀ ⟶ Limits.pullback i (j k)) ≫ f = f₀ :=
    pullback.lift_fst _ _ _
  have hlift₁ : (pullback.lift f₀ g₀ hcomp : V₀ ⟶ Limits.pullback i (j k)) ≫ v = g₀ :=
    pullback.lift_snd _ _ _
  have e₀ : D.G.map (pullback.lift f₀ g₀ hcomp).op (D.G.map f.op x) = D.G.map f₀.op x := by
    rw [ExtendingFunctors.map_map_apply, hlift₀]
  have e₁ : D.G.map (pullback.lift f₀ g₀ hcomp).op
      (D.G.map v.op (D.a.app (op (U k)) zF)) = D.G.map g₀.op (D.a.app (op (U k)) zF) := by
    rw [ExtendingFunctors.map_map_apply, hlift₁]
  rw [← e₀, ← hred]
  exact e₁

end Space

end AlgebraicGeometry

end
