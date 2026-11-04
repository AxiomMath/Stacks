module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhoodFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Module
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.StalkFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness

/-!
# Openness in a fibre of the flat locus of a finite type module

Let `f : X ⟶ S` be a morphism of schemes and let `F` be a quasi-coherent `𝒪_X`-module of finite
type. For a point `s` of `S`, the locus in the fibre `X_s` where `F` is flat over `S` is open.

Stacks 05I5 produces, at a point `x` where `F` is flat over `S`, an elementary étale
neighbourhood `(S', s')` of `(S, s)` and an open `V ⊆ X ×_S Spec 𝒪_{S', s'}` containing the
unique point over `x` on which the pullback of `F` is flat over `𝒪_{S', s'}`. Two steps turn
that into openness in the fibre. First, because `(S', s')` is elementary the residue fields
`κ(s)` and `κ(s')` agree, so the fibre of `X ×_S Spec 𝒪_{S', s'} ⟶ Spec 𝒪_{S', s'}` over the
point lying over `s'` is `X_s` itself; pulling `V` back along that identification gives an open
neighbourhood of `x` in `X_s`. Second, at every point of `V` the pullback of `F` is flat over
`𝒪_{S', s'}`, hence over `S`, and the projection `X ×_S Spec 𝒪_{S', s'} ⟶ X` is flat, so Stacks
02JZ returns flatness of `F` over `S` at the corresponding point of `X_s`.

## Main definitions

* `AlgebraicGeometry.ExistsElementaryEtaleNeighborhoodFlatOverAt` is the conclusion of Stacks
  05I5 and Stacks 05KT at a single point, with the finite-presentation clause dropped.
* `AlgebraicGeometry.ExistsElementaryEtaleNeighborhoodFlatOver` is the statement of Stacks 05KT,
  named once so that a consumer may take it as a single hypothesis.

## Main results

* `AlgebraicGeometry.exists_homeomorph_fiber` identifies the fibre of a base change along a
  morphism which is trivial on residue fields with the fibre of the original morphism.
* `AlgebraicGeometry.eq_of_pullback_fst_eq` and `AlgebraicGeometry.exists_pullback_fst_eq` say
  that over an elementary étale neighbourhood of `(S, s)` there is exactly one point of
  `X ×_S Spec 𝒪_{S', s'}` above each point of `X` over `s`.
* `AlgebraicGeometry.isFlatOverAt_of_isFlatOverAt_pullback` is the descent step: flatness over a
  flat base of the pullback of `F` to `X ×_S T` gives flatness of `F` over `S`.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_isFlatOverAt_nhds` reads the conclusion
  of Stacks 05KT at a point of `X_s` uniformly over a neighbourhood of that point in `X_s`: the
  open `V` it produces contains the point over every point of that neighbourhood. This is the
  form in which Stacks 05I5 enters the proofs of both Stacks 05M9 and Stacks 05KU.
* `AlgebraicGeometry.isOpen_isFlatOverAt_fiber_of_forall` proves openness of the flat locus in a
  fibre from the conclusion of Stacks 05KT at each of its points.
* `AlgebraicGeometry.isOpen_isFlatOverAt_fiber` is **Stacks 05M9** for `f` locally of finite
  presentation, and `AlgebraicGeometry.isOpen_isFlatOverAt_fiber_of_exists` is Stacks 05M9 for
  `f` locally of finite type, granted Stacks 05KT.

## Implementation notes

The fibre is the scheme-theoretic fibre `Scheme.Hom.fiber`, and the flat locus is a set of its
points pulled back along `Scheme.Hom.fiberι`. This is the source's `{x ∈ X_s | …}`: the fibre
`X_s` is homeomorphic to the subspace `f ⁻¹' {s}` of `X` by `Scheme.Hom.fiberHomeo`, because
`Scheme.Hom.fiberι` is a preimmersion with range `f ⁻¹' {s}`.

Stacks 05M9 is stated in the source for `f` locally of finite type, but its proof cites Stacks
05I5, which assumes locally of finite presentation; the finite type statement needs Stacks 05KT
instead. Only the finite presentation case is proved outright here. The finite type case is
`AlgebraicGeometry.isOpen_isFlatOverAt_fiber_of_exists`, which takes the statement of Stacks
05KT as a hypothesis.

The point of `Spec 𝒪_{U, u}` lying over `u` is handled through a variable `y` together with the
hypothesis `U.scheme.fromSpecStalk U.point y = U.point`, rather than by writing
`IsLocalRing.closedPoint` into the statements: that term inhabits the carrier of
`Spec 𝒪_{U, u}` only up to unfolding `Spec`, so goals mentioning it are not type-correct at
`implicit` transparency.

## References

* [Stacks Project, Tag 05M9](https://stacks.math.columbia.edu/tag/05M9)
* [Stacks Project, Tag 05KT](https://stacks.math.columbia.edu/tag/05KT)
* [Stacks Project, Tag 05KU](https://stacks.math.columbia.edu/tag/05KU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- `Spec 𝒪_{X, x}` has a point lying over `x`, namely the closed point. -/
theorem exists_fromSpecStalk_eq {X : Scheme.{u}} (x : X) :
    ∃ y : ↥(Spec (X.presheaf.stalk x)), X.fromSpecStalk x y = x :=
  ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩

/-- For a morphism `g : U ⟶ S` inducing an isomorphism of residue fields at `u`, the composite
`Spec 𝒪_{U, u} ⟶ U ⟶ S` induces an isomorphism of residue fields at the point lying over `u`:
the morphism `Spec 𝒪_{U, u} ⟶ U` is a preimmersion, hence surjective on stalks. -/
theorem isIso_residueFieldMap_fromSpecStalk_comp {U S : Scheme.{u}} (g : U ⟶ S) (u : U)
    (hg : IsIso (g.residueFieldMap u)) {y : ↥(Spec (U.presheaf.stalk u))}
    (hy : U.fromSpecStalk u y = u) :
    IsIso ((U.fromSpecStalk u ≫ g).residueFieldMap y) := by
  rw [Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' ((g.isIso_residueFieldMap_congr hy).mpr hg)
    ((U.fromSpecStalk u).isIso_residueFieldMap_of_surjectiveOnStalks y)

/-- An étale neighbourhood of `(S, s)` is an étale neighbourhood of `(S, s')` for any point
`s'` equal to `s`. -/
def EtaleNeighborhood.congrPoint {S : Scheme.{u}} {s s' : S} (U : EtaleNeighborhood S s)
    (h : s = s') : EtaleNeighborhood S s' where
  scheme := U.scheme
  point := U.point
  toBase := U.toBase
  map_point := U.map_point.trans h

/-- The scheme of `U.congrPoint h` is the scheme of `U`. -/
@[simp]
theorem EtaleNeighborhood.congrPoint_scheme {S : Scheme.{u}} {s s' : S}
    (U : EtaleNeighborhood S s) (h : s = s') : (U.congrPoint h).scheme = U.scheme := rfl

/-- The point of `U.congrPoint h` is the point of `U`. -/
@[simp]
theorem EtaleNeighborhood.congrPoint_point {S : Scheme.{u}} {s s' : S}
    (U : EtaleNeighborhood S s) (h : s = s') : (U.congrPoint h).point = U.point := rfl

/-- The structure morphism of `U.congrPoint h` is that of `U`. -/
@[simp]
theorem EtaleNeighborhood.congrPoint_toBase {S : Scheme.{u}} {s s' : S}
    (U : EtaleNeighborhood S s) (h : s = s') : (U.congrPoint h).toBase = U.toBase := rfl

/-- Being elementary does not depend on the spelling of the base point. -/
theorem EtaleNeighborhood.IsElementary.congrPoint {S : Scheme.{u}} {s s' : S}
    {U : EtaleNeighborhood S s} (hU : U.IsElementary) (h : s = s') :
    (U.congrPoint h).IsElementary := by
  rwa [EtaleNeighborhood.isElementary_iff] at hU ⊢

/-- Flatness over the base of the restriction of a module to an open subscheme is flatness of
the module itself at the corresponding point: an open immersion is flat, so Tag 02JZ applies. -/
theorem isFlatOverAt_pullback_ι_iff {P T : Scheme.{u}} (h : P ⟶ T) (V : P.Opens)
    (G : P.Modules) (p : V) :
    IsFlatOverAt (V.ι ≫ h).toLRSHom.toShHom ((Scheme.Modules.pullback V.ι).obj G) p ↔
      IsFlatOverAt h.toLRSHom.toShHom G (V.ι p) :=
  (isFlatOverAt_iff_modulePullback_isFlatOverAt V.ι h G p (Flat.stalkMap V.ι p)).symm

/-- **The fibre does not change under a base change which is trivial on residue fields.** If
`b : T ⟶ S` carries `y` to `s` and induces an isomorphism `κ(s) ⟶ κ(y)`, then the fibre of
`X ×_S T ⟶ T` over `y` is isomorphic to the fibre `X_s`, compatibly with the two morphisms to
`X`. This is the step "`X_{s'} = X_s` as `κ(s) = κ(s')`" in the proofs of Tags 05M9 and 05KU.

Stated for the underlying homeomorphism, which is all its consumers use. -/
theorem exists_homeomorph_fiber {X S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S) {y : T} {s : S}
    (hb : b y = s) (hres : IsIso (b.residueFieldMap y)) :
    ∃ e : f.fiber s ≃ₜ (pullback.snd f b).fiber y, ∀ w : f.fiber s,
      pullback.fst f b ((pullback.snd f b).fiberι y (e w)) = f.fiberι s w := by
  subst hb
  set g₁ : Spec (T.residueField y) ⟶ S := T.fromSpecResidueField y ≫ b with hg₁
  set g₂ : Spec (S.residueField (b y)) ⟶ S := S.fromSpecResidueField (b y) with hg₂
  let k := Scheme.Spec.mapIso (asIso (b.residueFieldMap y)).op
  have hk : k.hom ≫ g₂ = g₁ := by
    rw [hg₁, hg₂, Functor.mapIso_hom]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField b y
  let m₂ : pullback f g₁ ⟶ pullback f g₂ :=
    pullback.map f g₁ f g₂ (𝟙 X) k.hom (𝟙 S) (by simp) hk.symm
  have hm₂ : IsIso m₂ := pullback.map_isIso f g₁ f g₂ (𝟙 X) k.hom (𝟙 S) (by simp) hk.symm
  let e₁ := pullbackLeftPullbackSndIso f b (T.fromSpecResidueField y)
  let e : (pullback.snd f b).fiber y ≅ f.fiber (b y) := e₁ ≪≫ @asIso _ _ _ _ m₂ hm₂
  have hcomp : e.hom ≫ f.fiberι (b y) =
      (pullback.snd f b).fiberι y ≫ pullback.fst f b := by
    have he₂ : m₂ ≫ pullback.fst f g₂ = pullback.fst f g₁ := by
      simp only [m₂, pullback.map, pullback.lift_fst, Category.comp_id]
    show e₁.hom ≫ m₂ ≫ pullback.fst f g₂ = _
    rw [he₂]
    exact pullbackLeftPullbackSndIso_hom_fst f b (T.fromSpecResidueField y)
  refine ⟨(Scheme.homeoOfIso e).symm, fun w => ?_⟩
  simpa [Scheme.Hom.comp_apply] using (congrArg (fun m : (pullback.snd f b).fiber y ⟶ X =>
    m ((Scheme.homeoOfIso e).symm w)) hcomp).symm

/-- **Flatness over a flat base descends.** If the pullback of `F` to `X ×_S T` is flat over `T`
at a point and `T ⟶ S` is flat, then `F` is flat over `S` at the image of that point in `X`:
flatness over `T` and flatness of `T` over `S` compose, and the projection `X ×_S T ⟶ X` is
flat, so Tag 02JZ carries the conclusion back to `F`. -/
theorem isFlatOverAt_of_isFlatOverAt_pullback {X S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S)
    [Flat b] (F : X.Modules) {p : ↑(pullback f b)}
    (hp : IsFlatOverAt (pullback.snd f b).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f b)).obj F) p) :
    IsFlatOverAt f.toLRSHom.toShHom F (pullback.fst f b p) := by
  have hcomp := IsFlatOverAt.comp (pullback.snd f b).toLRSHom.toShHom b.toLRSHom.toShHom
    ((Scheme.Modules.pullback (pullback.fst f b)).obj F) p hp
    (Flat.stalkMap b (pullback.snd f b p))
  have hOverS : IsFlatOverAt (pullback.fst f b ≫ f).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f b)).obj F) p := by
    simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom,
      pullback.condition] using hcomp
  exact (isFlatOverAt_iff_modulePullback_isFlatOverAt (pullback.fst f b) f F p
    (Flat.stalkMap (pullback.fst f b) p)).mpr hOverS

/-- The conclusion of **Stacks Project, Tags 05I5 and 05KT** at a single point: there is an
elementary étale neighbourhood `U` of `(S, f a)` and an open subscheme
`V ⊆ X ×_S Spec 𝒪_{U, u}` containing the unique point of `X ×_S Spec 𝒪_{U, u}` over `a` on which
the pullback of `F` is flat over `Spec 𝒪_{U, u}`. -/
def ExistsElementaryEtaleNeighborhoodFlatOverAt {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (a : X) : Prop :=
  ∃ (U : EtaleNeighborhood S (f a)) (_ : U.IsElementary),
    let b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
      U.scheme.fromSpecStalk U.point ≫ U.toBase
    ∃ (V : (pullback f b).Opens) (v : V),
      (pullback.fst f b ⁻¹' {a} = {V.ι v}) ∧
      IsFlatOver
        (LocallyRingedSpace.forgetToSheafedSpace.map (V.ι ≫ pullback.snd f b).toLRSHom)
        ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F)

/-- Tag 05I5 implies its own conclusion with the finite-presentation clause dropped. -/
theorem ExistsElementaryEtaleNeighborhoodFlatOverAt.of_finitePresentation
    (h : ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (a : X)
    (ha : IsFlatOverAt f.toLRSHom.toShHom F a) :
    ExistsElementaryEtaleNeighborhoodFlatOverAt f F a := by
  obtain ⟨U, hU, V, v, huniq, -, hflat⟩ := h f F a ha
  exact ⟨U, hU, V, v, huniq, hflat⟩

/-- **Stacks Project, Tag 05KT**, as a proposition: for `f` locally of finite type and `F`
quasi-coherent of finite type and flat over `S` at `x`, there is an elementary étale
neighbourhood `(S', s')` of `(S, f x)` and an open subscheme of `X ×_S Spec 𝒪_{S', s'}`
containing the unique point over `x` on which the pullback of `F` is flat over `𝒪_{S', s'}`.

This is Tag 05I5 with the finite-presentation hypothesis on `f` relaxed to finite type and the
finite-presentation clause of the conclusion dropped. -/
def ExistsElementaryEtaleNeighborhoodFlatOver : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
      [F.IsQuasicoherent] [F.IsFiniteType] (x : X),
    IsFlatOverAt f.toLRSHom.toShHom F x → ExistsElementaryEtaleNeighborhoodFlatOverAt f F x

/-- There is a unique point of `X ×_S Spec 𝒪_{U, u}` over a point `x` of `X` over `s`, for an
elementary étale neighbourhood `U` of `(S, s)`. -/
private theorem existsUnique_pullback_fst_eq {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (U : EtaleNeighborhood S s) (hU : U.IsElementary) {x : X} (hx : f x = s) :
    ∃! p : ↑(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)),
      pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) p = x := by
  obtain ⟨v, hv⟩ := EtaleNeighborhood.exists_preimage_fst_eq_singleton f x
    (U.congrPoint hx.symm) (hU.congrPoint hx.symm)
  exact ⟨v, Set.eq_singleton_iff_unique_mem.mp hv⟩

/-- **The unique point over a point of the fibre.** For an elementary étale neighbourhood `U` of
`(S, s)` and a point `x` of `X` over `s`, the fibre of `X ×_S Spec 𝒪_{U, u} ⟶ X` over `x` is a
single point, so any two points over `x` agree. -/
theorem eq_of_pullback_fst_eq {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (U : EtaleNeighborhood S s) (hU : U.IsElementary) {x : X} (hx : f x = s)
    {p q : ↑(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase))}
    (hp : pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) p = x)
    (hq : pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) q = x) : p = q :=
  (existsUnique_pullback_fst_eq f U hU hx).unique hp hq

/-- **Tag 05I5 at a point of a fibre, uniformly over a neighbourhood in the fibre.** At a point
of `X_s` where `F` is flat over `S` there is an elementary étale neighbourhood `(S', s')` of
`(S, s)` and an open `V ⊆ X ×_S Spec 𝒪_{S', s'}` such that the pullback of `F` to
`X ×_S Spec 𝒪_{S', s'}` is flat over `𝒪_{S', s'}` at every point of `V`, and such that `V`
contains the point over `x'` for every `x'` in an open neighbourhood of `x` in `X_s`.

The neighbourhood in `X_s` is the inverse image of `V` under the identification of `X_s` with
the fibre of `X ×_S Spec 𝒪_{S', s'} ⟶ Spec 𝒪_{S', s'}` over the point lying over `s'`. -/
theorem exists_elementaryEtaleNeighborhood_isFlatOverAt_nhds {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) {s : S} (w : f.fiber s)
    (hw : ExistsElementaryEtaleNeighborhoodFlatOverAt f F (f.fiberι s w)) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary) (W : Set (f.fiber s)),
      IsOpen W ∧ w ∈ W ∧
      ∃ V : (pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).Opens,
        (∀ p : ↑(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)), p ∈ V →
          IsFlatOverAt (pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).toLRSHom.toShHom
            ((Scheme.Modules.pullback
              (pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F) p) ∧
        (∀ w' ∈ W, ∀ p : ↑(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)),
          pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) p = f.fiberι s w' →
            p ∈ V) := by
  have hfa : f (f.fiberι s w) = s := f.apply_fiberι s w
  obtain ⟨U₀, hU₀, V, v, huniq, hflat⟩ := hw
  set U : EtaleNeighborhood S s := U₀.congrPoint hfa
  have hU : U.IsElementary := hU₀.congrPoint hfa
  set b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
    U.scheme.fromSpecStalk U.point ≫ U.toBase with hb
  have : Flat b := Stacks.Flatness.flat_fromSpecStalk_comp_toBase U
  obtain ⟨y, hy⟩ := exists_fromSpecStalk_eq U.point
  have hby : b y = s := by rw [hb, Scheme.Hom.comp_apply, hy, U.map_point]
  have hres : IsIso (b.residueFieldMap y) :=
    isIso_residueFieldMap_fromSpecStalk_comp U.toBase U.point
      ((EtaleNeighborhood.isElementary_iff U).mp hU) hy
  obtain ⟨e, he⟩ := exists_homeomorph_fiber f b hby hres
  set G := (Scheme.Modules.pullback (pullback.fst f b)).obj F
  refine ⟨U, hU, {z | (pullback.snd f b).fiberι y (e z) ∈ V}, V.2.preimage
    (((pullback.snd f b).fiberι y).continuous.comp e.continuous), ?_, V, ?_, ?_⟩
  · have huniq' : pullback.fst f b ⁻¹' {f.fiberι s w} = {V.ι v} := huniq
    have hmem : (pullback.snd f b).fiberι y (e w) ∈
        ({V.ι v} : Set ↑(pullback f b)) := huniq' ▸ he w
    show (pullback.snd f b).fiberι y (e w) ∈ V.1
    rw [Set.eq_of_mem_singleton hmem]
    exact v.2
  · intro p hp
    exact (isFlatOverAt_pullback_ι_iff (pullback.snd f b) V G ⟨p, hp⟩).mp
      (isFlatOverAt_of_moduleIso (V.ι ≫ pullback.snd f b).toLRSHom.toShHom
        ((Scheme.Modules.pullbackComp V.ι (pullback.fst f b)).app F).symm _ (hflat ⟨p, hp⟩))
  · intro w' hw' p hp
    rwa [eq_of_pullback_fst_eq f U hU (f.apply_fiberι s w') hp (he w')]

/-- **A point of `X` over `s` in the base change to the local ring.** For an elementary étale
neighbourhood `U` of `(S, s)` and a point `x` of `X` over `s`, some point of
`X ×_S Spec 𝒪_{U, u}` lies over `x`. -/
theorem exists_pullback_fst_eq {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (U : EtaleNeighborhood S s) (hU : U.IsElementary) {x : X} (hx : f x = s) :
    ∃ p : ↑(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)),
      pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) p = x :=
  (existsUnique_pullback_fst_eq f U hU hx).exists

/-- **The flat locus is open in a fibre, from the neighbourhood statement at each of its
points.** If every point `a` of the fibre `X_s` at which `F` is flat over `S` admits an
elementary étale neighbourhood of `(S, s)` and an open `V ⊆ X ×_S Spec 𝒪_{S', s'}` as in Tag
05KT, then the locus in `X_s` where `F` is flat over `S` is open.

At a point of that locus, `V` contains the point over every point of an open neighbourhood in
`X_s` by `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_isFlatOverAt_nhds`, and there the
pullback of `F` is flat over `𝒪_{S', s'}`, hence `F` is flat over `S` by
`AlgebraicGeometry.isFlatOverAt_of_isFlatOverAt_pullback`. -/
theorem isOpen_isFlatOverAt_fiber_of_forall {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (s : S) (h : ∀ a : X, f a = s → IsFlatOverAt f.toLRSHom.toShHom F a →
      ExistsElementaryEtaleNeighborhoodFlatOverAt f F a) :
    IsOpen {w : f.fiber s | IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s w)} := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  obtain ⟨U, hU, W, hWo, hwW, V, hVflat, hVmem⟩ :=
    exists_elementaryEtaleNeighborhood_isFlatOverAt_nhds f F w (h _ (f.apply_fiberι s w) hw)
  have : Flat (U.scheme.fromSpecStalk U.point ≫ U.toBase) :=
    Stacks.Flatness.flat_fromSpecStalk_comp_toBase U
  refine Filter.mem_of_superset (hWo.mem_nhds hwW) fun w' hw' => ?_
  obtain ⟨p, hp⟩ := exists_pullback_fst_eq f U hU (f.apply_fiberι s w')
  have hflat := isFlatOverAt_of_isFlatOverAt_pullback f
    (U.scheme.fromSpecStalk U.point ≫ U.toBase) F (hVflat p (hVmem w' hw' p hp))
  rwa [hp] at hflat

/-- **Stacks Project, Tag 05M9** for a morphism locally of finite presentation: in every fibre of
`f`, the locus where a finite type quasi-coherent `𝒪_X`-module is flat over the base is open.

The source states this for `f` locally of finite type, and deduces it from Tag 05I5, which
assumes locally of finite presentation. For `f` only locally of finite type the same argument
needs Tag 05KT in place of Tag 05I5; that deduction is
`AlgebraicGeometry.isOpen_isFlatOverAt_fiber_of_exists`. -/
@[stacks 05M9 "for f locally of finite presentation"]
theorem isOpen_isFlatOverAt_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (s : S) :
    IsOpen {w : f.fiber s | IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s w)} :=
  isOpen_isFlatOverAt_fiber_of_forall f F s fun a _ ha =>
    ExistsElementaryEtaleNeighborhoodFlatOverAt.of_finitePresentation
      @existsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u} f F a ha

/-- **Stacks Project, Tag 05M9**, for `f` locally of finite type: in every fibre of `f`, the
locus where a finite type quasi-coherent `𝒪_X`-module is flat over the base is open, granted the
statement of Tag 05KT. -/
theorem isOpen_isFlatOverAt_fiber_of_exists (h : ExistsElementaryEtaleNeighborhoodFlatOver.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (s : S) :
    IsOpen {w : f.fiber s | IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s w)} :=
  isOpen_isFlatOverAt_fiber_of_forall f F s fun a _ ha => h f F a ha

end AlgebraicGeometry

end
