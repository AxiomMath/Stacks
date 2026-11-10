module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.UniqueLiftingAlongUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom

/-!
# Pushing an étale chart forward along a thickening

Let `ι : X₀ ⟶ X` be a morphism of fppf sheaves on the big fppf site of `S` which is a
representable thickening: every base change of it along a scheme-valued point of `X` is a
thickening of schemes. Let `c : V ⟶ X₀` be representable by objects of the site and étale.
This file constructs a morphism `π : W ⟶ X`, again representable by objects of the site and
étale, whose base change along `ι` is `c`.

This is the topological invariance of the étale site (Stacks 039R, 0BTY) read over an
arbitrary sheaf `X`, which need not be an algebraic space; it is the chart construction in the
proof of Stacks 0AIU, where an affine étale chart of one stage of a directed system of
thickenings is transported to every later stage, here transported to the colimit at once.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_etale_isPullback_of_isThickening`: Stacks 039R for
  objects of the site, with a cartesian square in the site.
* `AlgebraicGeometry.FormalSpace.exists_etale_isPullback_of_isRepresentableThickeningULift`:
  the transported chart.

## Implementation notes

`W` is the pushforward of `V` along `ι`: a section of `W` over `T` is a section `x` of `X` over
`T` together with a morphism `T ×_X X₀ ⟶ V` over `X₀`. Its base change along a point
`ξ : T ⟶ X` is computed by the base change `T₀ = T ×_X X₀`, a thickening of `T`, and the étale
scheme `Q₀ = T₀ ×_{X₀} V` over it: the lift `P` of `Q₀` along `T₀ ⟶ T` given by Stacks 039R
represents it, because morphisms into `P` over `T` are the morphisms into `Q₀` over `T₀`, which
is Stacks 0BTY in the form `AlgebraicGeometry.FormalSpace.uniqueLiftingAlong_bigFppfOver`. The
sheaf condition for `W` follows, since `X` is a sheaf and every such base change is
representable.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 039R for objects of the site.** Let `i₀ : U₀ ⟶ U` be a morphism of the big fppf
site of `S` whose underlying morphism of schemes is a thickening, and let `q : Q₀ ⟶ U₀` be
étale. Then `q` is the base change along `i₀` of an étale morphism `p : P ⟶ U` of the site. -/
theorem exists_etale_isPullback_of_isThickening {U₀ U Q₀ : BigFppfOver B S hS} (i₀ : U₀ ⟶ U)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i₀))
    (q : Q₀ ⟶ U₀) (hq : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    ∃ (P : BigFppfOver B S hS) (p : P ⟶ U) (k : Q₀ ⟶ P),
      Etale ((BigFppfOver.toScheme B S hS).map p) ∧ IsPullback k q p i₀ := by
  let F := BigFppfOver.toScheme B S hS
  have : _root_.AlgebraicGeometry.IsClosedImmersion (F.map i₀) := hi.1
  obtain ⟨P', q', hq', e, he, hP'⟩ :=
    Stacks.Etale.exists_etale_pullback_iso_contains_of_isClosedImmersion_of_surjective B
      (F.map i₀) hi.2 U.left.2 (F.obj Q₀) Q₀.left.2 (F.map q) hq
  let P : BigFppfOver B S hS := siteObject B S hS hP' (q' ≫ B.inclusion.map U.hom)
  let p : P ⟶ U := BigFppfOver.homOfCompEq B S hS (T := P) (W := U) q' rfl
  have hp : F.map p = q' := BigFppfOver.toScheme_map_homOfCompEq B S hS _ _
  have he' : e.inv ≫ pullback.snd q' (F.map i₀) = F.map q := by
    rw [← he, Iso.inv_hom_id_assoc]
  have hk : (e.inv ≫ pullback.fst q' (F.map i₀)) ≫ B.inclusion.map P.hom =
      B.inclusion.map Q₀.hom := by
    change (e.inv ≫ pullback.fst q' (F.map i₀)) ≫ q' ≫ B.inclusion.map U.hom = _
    rw [Category.assoc, reassoc_of% pullback.condition, reassoc_of% he',
      BigFppfOver.toScheme_map_comp_hom, BigFppfOver.toScheme_map_comp_hom]
  let k : Q₀ ⟶ P := BigFppfOver.homOfCompEq B S hS _ hk
  have hkF : F.map k = e.inv ≫ pullback.fst q' (F.map i₀) :=
    BigFppfOver.toScheme_map_homOfCompEq B S hS _ _
  have hw : k ≫ p = q ≫ i₀ := by
    apply BigFppfOver.map_toScheme_injective B S hS
    change F.map (k ≫ p) = F.map (q ≫ i₀)
    rw [F.map_comp, F.map_comp, hkF, hp, Category.assoc, pullback.condition,
      ← Category.assoc, he']
  have hsq : IsPullback (F.map k) (F.map q) (F.map p) (F.map i₀) := by
    rw [hp]
    exact IsPullback.of_iso_pullback ⟨by rw [← hp, ← F.map_comp, ← F.map_comp, hw]⟩ e.symm
      (by rw [hkF]; rfl) (by rw [← he']; rfl)
  have : PreservesLimitsOfShape WalkingCospan F :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  exact ⟨P, p, k, by rwa [hp], IsPullback.of_map F hw hsq⟩

/-! ### The pushforward of a sheaf over `X₀` along `ι : X₀ ⟶ X` -/

section Pushforward

variable {B S hS}
variable {X X₀ E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (ι : X₀ ⟶ X) (c : E ⟶ X₀)

/-- A family `R` of subsets of the sections of `E`, indexed by the morphisms `g : T' ⟶ T` and
the sections `z` of `X₀` over `T'`, is the graph of a morphism `T ×_X X₀ ⟶ E` over `X₀`, where
`T ⟶ X` is the section `x`: `R g z` is a single section lying over `z` when `(g, z)` is a
section of `T ×_X X₀` and is empty otherwise, compatibly with restriction. -/
structure IsPushforwardSection {T : BigFppfOver B S hS} (x : X.obj (Opposite.op T))
    (R : ∀ T' : BigFppfOver B S hS, (T' ⟶ T) → X₀.obj (Opposite.op T') →
      Set (E.obj (Opposite.op T'))) : Prop where
  /-- The set `R g z` is nonempty when `(g, z)` is a section of `T ×_X X₀`. -/
  nonempty : ∀ T' (g : T' ⟶ T) (z : X₀.obj (Opposite.op T')),
    ι.app _ z = X.map g.op x → (R T' g z).Nonempty
  /-- The set `R g z` has at most one element. -/
  subsingleton : ∀ T' (g : T' ⟶ T) (z : X₀.obj (Opposite.op T')), (R T' g z).Subsingleton
  /-- An element of `R g z` lies over `z`, and then `(g, z)` is a section of `T ×_X X₀`. -/
  mem : ∀ T' (g : T' ⟶ T) (z : X₀.obj (Opposite.op T')) (e : E.obj (Opposite.op T')),
    e ∈ R T' g z → ι.app _ z = X.map g.op x ∧ c.app _ e = z
  /-- The family `R` is compatible with restriction along a morphism `h : T'' ⟶ T'`. -/
  map : ∀ T' T'' (h : T'' ⟶ T') (g : T' ⟶ T) (z : X₀.obj (Opposite.op T'))
    (e : E.obj (Opposite.op T')), e ∈ R T' g z → E.map h.op e ∈ R T'' (h ≫ g) (X₀.map h.op z)

namespace IsPushforwardSection

variable {ι c} {T : BigFppfOver B S hS} {x : X.obj (Opposite.op T)}

/-- Two graphs over the same section, one contained in the other, are equal. -/
theorem eq_of_subset {R R' : ∀ T' : BigFppfOver B S hS, (T' ⟶ T) →
      X₀.obj (Opposite.op T') → Set (E.obj (Opposite.op T'))}
    (hR : IsPushforwardSection ι c x R) (hR' : IsPushforwardSection ι c x R')
    (h : ∀ T' g z, R T' g z ⊆ R' T' g z) : R = R' := by
  funext T' g z
  refine Set.Subset.antisymm (h T' g z) fun e he ↦ ?_
  obtain ⟨e', he'⟩ := hR.nonempty T' g z (hR'.mem T' g z e he).1
  rwa [hR'.subsingleton T' g z he (h T' g z he')]

/-- The restriction of a graph along a morphism `f : T₂ ⟶ T`. -/
theorem restrict {R : ∀ T' : BigFppfOver B S hS, (T' ⟶ T) →
      X₀.obj (Opposite.op T') → Set (E.obj (Opposite.op T'))}
    (hR : IsPushforwardSection ι c x R) {T₂ : BigFppfOver B S hS} (f : T₂ ⟶ T) :
    IsPushforwardSection ι c (X.map f.op x) (fun T' g z ↦ R T' (g ≫ f) z) where
  nonempty T' g z hz := hR.nonempty T' (g ≫ f) z (by
    rw [hz, op_comp, Functor.map_comp_apply])
  subsingleton T' g z := hR.subsingleton T' (g ≫ f) z
  mem T' g z e he := by
    obtain ⟨h₁, h₂⟩ := hR.mem T' (g ≫ f) z e he
    exact ⟨by rw [h₁, op_comp, Functor.map_comp_apply], h₂⟩
  map T' T'' h g z e he := by
    simpa only [Category.assoc] using hR.map T' T'' h (g ≫ f) z e he

end IsPushforwardSection

/-- **The pushforward of `c : E ⟶ X₀` along `ι : X₀ ⟶ X`.** A section over `T` is a section `x`
of `X` over `T` together with the graph of a morphism `T ×_X X₀ ⟶ E` over `X₀`. -/
def thickeningPushforward : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) where
  obj T := { p : X.obj T × (∀ T' : BigFppfOver B S hS, (T' ⟶ T.unop) →
      X₀.obj (Opposite.op T') → Set (E.obj (Opposite.op T'))) //
    IsPushforwardSection ι c p.1 p.2 }
  map {T₁ T₂} f := ↾fun p ↦ ⟨(X.map f p.1.1, fun T' g z ↦ p.1.2 T' (g ≫ f.unop) z),
    p.2.restrict f.unop⟩
  map_id T := by
    ext p <;> simp
  map_comp f g := by
    ext p <;> simp

/-- The projection of the pushforward to `X`. -/
def thickeningPushforwardπ : thickeningPushforward ι c ⟶ X where
  app _ := ↾fun p ↦ p.1.1
  naturality _ _ _ := rfl

variable {ι c}

/-- The section of the pushforward attached to a section `e` of `E`: the graph of the morphism
`T ×_X X₀ ⟶ E` which restricts `e`, the projection to `T` being an isomorphism because `ι` is a
monomorphism. -/
def thickeningPushforwardι (hinj : ∀ T, Function.Injective (ι.app T)) :
    E ⟶ thickeningPushforward ι c where
  app T := ↾fun e ↦ ⟨(ι.app T (c.app T e), fun T' g z ↦
      {e' | e' = E.map g.op e ∧ z = X₀.map g.op (c.app T e)}), {
    nonempty := fun T' g z hz ↦ ⟨E.map g.op e, rfl, hinj _ (by
      rw [hz, NatTrans.naturality_apply])⟩
    subsingleton := fun T' g z e₁ he₁ e₂ he₂ ↦ he₁.1.trans he₂.1.symm
    mem := fun T' g z e' he' ↦ by
      obtain ⟨rfl, rfl⟩ := he'
      exact ⟨NatTrans.naturality_apply ι g.op _, NatTrans.naturality_apply c g.op _⟩
    map := fun T' T'' h g z e' he' ↦ by
      obtain ⟨rfl, rfl⟩ := he'
      refine ⟨?_, ?_⟩ <;> simp only [op_comp, Functor.map_comp_apply] }⟩
  naturality T₁ T₂ f := by
    ext e
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change ι.app T₂ (c.app T₂ (E.map f e)) = X.map f (ι.app T₁ (c.app T₁ e))
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    · funext T' g z
      ext e'
      change (e' = E.map g.op (E.map f e) ∧ z = X₀.map g.op (c.app T₂ (E.map f e))) ↔
        (e' = E.map (g ≫ f.unop).op e ∧ z = X₀.map (g ≫ f.unop).op (c.app T₁ e))
      rw [NatTrans.naturality_apply]
      simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply]

/-- **The base change of the pushforward along `ι` is `E`.** -/
theorem isPullback_thickeningPushforwardι (hinj : ∀ T, Function.Injective (ι.app T)) :
    IsPullback (thickeningPushforwardι hinj) c (thickeningPushforwardπ ι c) ι := by
  refine isPullback_of_existsUnique_app (by ext; rfl) fun T w z hwz ↦ ?_
  have hz : ι.app _ z = X.map (𝟙 T.unop).op w.1.1 := by
    rw [← hwz]
    simp only [op_id, Functor.map_id_apply]
    rfl
  obtain ⟨e, he⟩ := w.2.nonempty T.unop (𝟙 _) z hz
  have hce : c.app T e = z := (w.2.mem _ _ _ e he).2
  refine ⟨e, ⟨?_, hce⟩, fun e' ⟨he'w, he'z⟩ ↦ ?_⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · change ι.app T (c.app T e) = w.1.1
      rw [hce]
      exact hwz.symm
    · refine IsPushforwardSection.eq_of_subset
        (x := w.1.1) ?_ w.2 fun T' g z' e' he' ↦ ?_
      · have := ((thickeningPushforwardι (c := c) hinj).app T e).2
        change IsPushforwardSection ι c (ι.app T (c.app T e)) _ at this
        rwa [hce, ← hwz] at this
      · obtain ⟨rfl, rfl⟩ := he'
        have := w.2.map T.unop T' g (𝟙 _) z e he
        rwa [Category.comp_id, ← hce] at this
  · have h₁ : e' ∈ w.1.2 T.unop (𝟙 _) z := by
      rw [← he'w]
      exact ⟨by simp, by rw [← he'z]; simp⟩
    exact w.2.subsingleton _ _ _ h₁ he

/-- A natural transformation out of a universe-lifted representable presheaf, evaluated at a
composite. -/
private theorem app_up_comp {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {U T' T'' : BigFppfOver B S hS} (ξ : uliftYoneda.{u + 1}.obj U ⟶ F) (g : T'' ⟶ T')
    (m : T' ⟶ U) : ξ.app (Opposite.op T'') ⟨g ≫ m⟩ = F.map g.op (ξ.app (Opposite.op T') ⟨m⟩) :=
  NatTrans.naturality_apply ξ g.op ⟨m⟩

/-- For a cartesian square exhibiting `uliftYoneda P` as the base change of `π : F ⟶ X` along
`ξ`, a section of `F` over `Y` lying over `ξ` at `f : Y ⟶ U` comes from a lift of `f` to `P`. -/
private theorem exists_lift_of_isPullback {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {π : F ⟶ X} {U P : BigFppfOver B S hS} {p : P ⟶ U} {r : uliftYoneda.{u + 1}.obj P ⟶ F}
    {ξ : uliftYoneda.{u + 1}.obj U ⟶ X} (hpb : IsPullback r (uliftYoneda.{u + 1}.map p) π ξ)
    {Y : BigFppfOver B S hS} (s : F.obj (Opposite.op Y)) (f : Y ⟶ U)
    (hs : π.app _ s = ξ.app _ ⟨f⟩) : ∃ l : Y ⟶ P, r.app _ ⟨l⟩ = s ∧ l ≫ p = f := by
  obtain ⟨⟨l⟩, hl₁, hl₂⟩ := Types.exists_of_isPullback (hpb.map ((evaluation _ _).obj _)) s ⟨f⟩ hs
  exact ⟨l, hl₁, congrArg ULift.down hl₂⟩

/-- For a cartesian square exhibiting `uliftYoneda P` as the base change of `π : F ⟶ X` along
`ξ`, two morphisms into `P` with the same section of `F` and the same composite with `p` are
equal. -/
private theorem eq_of_isPullback {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {π : F ⟶ X} {U P : BigFppfOver B S hS} {p : P ⟶ U} {r : uliftYoneda.{u + 1}.obj P ⟶ F}
    {ξ : uliftYoneda.{u + 1}.obj U ⟶ X} (hpb : IsPullback r (uliftYoneda.{u + 1}.map p) π ξ)
    {Y : BigFppfOver B S hS} {a b : Y ⟶ P} (h₁ : r.app (Opposite.op Y) ⟨a⟩ = r.app _ ⟨b⟩)
    (h₂ : a ≫ p = b ≫ p) : a = b :=
  congrArg ULift.down (Types.ext_of_isPullback (hpb.map ((evaluation _ _).obj _)) h₁
    (congrArg ULift.up h₂))

/-- The commuting square of a cartesian square of presheaves, evaluated at a morphism `m`. -/
private theorem app_eq_of_isPullback {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {π : F ⟶ X} {U P : BigFppfOver B S hS} {p : P ⟶ U} {r : uliftYoneda.{u + 1}.obj P ⟶ F}
    {ξ : uliftYoneda.{u + 1}.obj U ⟶ X} (hpb : IsPullback r (uliftYoneda.{u + 1}.map p) π ξ)
    {Y : BigFppfOver B S hS} (m : Y ⟶ P) :
    π.app (Opposite.op Y) (r.app _ ⟨m⟩) = ξ.app _ ⟨m ≫ p⟩ :=
  congrFun (congrArg (fun φ ↦ φ.app (Opposite.op Y)) hpb.w) ⟨m⟩

/-- The graph over `P` defined by `k : Q₀ ⟶ P`: a section `e` of `E` lies in the set at `(g, z)`
when `g` and `z` come from a morphism `m` into `Q₀`, and `e` is the section of `E` given by `m`. -/
def pushforwardGraph {U₀ Q₀ P : BigFppfOver B S hS} (fst₀ : uliftYoneda.{u + 1}.obj U₀ ⟶ X₀)
    (fst₁ : uliftYoneda.{u + 1}.obj Q₀ ⟶ E) (q : Q₀ ⟶ U₀) (k : Q₀ ⟶ P)
    (T' : BigFppfOver B S hS) (g : T' ⟶ P) (z : X₀.obj (Opposite.op T')) :
    Set (E.obj (Opposite.op T')) :=
  {e | ∃ m : T' ⟶ Q₀, m ≫ k = g ∧ fst₀.app _ ⟨m ≫ q⟩ = z ∧ e = fst₁.app _ ⟨m⟩}

section Graph

variable {U U₀ Q₀ P : BigFppfOver B S hS} {ξ : uliftYoneda.{u + 1}.obj U ⟶ X} {i₀ : U₀ ⟶ U}
  {fst₀ : uliftYoneda.{u + 1}.obj U₀ ⟶ X₀} {q : Q₀ ⟶ U₀} {fst₁ : uliftYoneda.{u + 1}.obj Q₀ ⟶ E}
  {p : P ⟶ U} {k : Q₀ ⟶ P}

/-- For cartesian squares exhibiting `U₀` as the base change of `ι` along `ξ`, `Q₀` as the base
change of `c` along `U₀ ⟶ X₀`, and `Q₀` as the base change of `p` along `i₀`, the graph
`pushforwardGraph` is a section of the pushforward over `P`, lying over `ξ` at `p`. -/
theorem isPushforwardSection_pushforwardGraph
    (hsq₀ : IsPullback fst₀ (uliftYoneda.{u + 1}.map i₀) ι ξ)
    (hsq₁ : IsPullback fst₁ (uliftYoneda.{u + 1}.map q) c fst₀) (hsq : IsPullback k q p i₀) :
    IsPushforwardSection ι c (ξ.app _ ⟨p⟩) (pushforwardGraph fst₀ fst₁ q k) := by
  refine ⟨fun T' g z hz ↦ ?_, fun T' g z e he e' he' ↦ ?_, fun T' g z e he ↦ ?_,
    fun T' T'' h g z e he ↦ ?_⟩
  · obtain ⟨m₀, hm₀z, hm₀⟩ :=
      exists_lift_of_isPullback hsq₀ z (g ≫ p) (by rw [hz, app_up_comp])
    refine ⟨_, hsq.lift g m₀ hm₀.symm, hsq.lift_fst _ _ _, ?_, rfl⟩
    rwa [hsq.lift_snd]
  · obtain ⟨m, hmk, hmz, rfl⟩ := he
    obtain ⟨m', hm'k, hm'z, rfl⟩ := he'
    have hmq : m ≫ q = m' ≫ q := eq_of_isPullback hsq₀ (hmz.trans hm'z.symm) (by
      rw [Category.assoc, Category.assoc, ← hsq.w, ← Category.assoc, hmk, ← Category.assoc, hm'k])
    rw [hsq.hom_ext (hmk.trans hm'k.symm) hmq]
  · obtain ⟨m, hmk, rfl, rfl⟩ := he
    refine ⟨?_, ?_⟩
    · rw [app_eq_of_isPullback hsq₀, Category.assoc, ← hsq.w, ← Category.assoc, hmk, app_up_comp]
    · exact app_eq_of_isPullback hsq₁ m
  · obtain ⟨m, hmk, rfl, rfl⟩ := he
    refine ⟨h ≫ m, by rw [Category.assoc, hmk], ?_, ?_⟩
    · rw [Category.assoc, app_up_comp]
    · exact (app_up_comp fst₁ h m).symm

/-- Let `ψ : T ⟶ P` over `a : T ⟶ U` restrict, over `T ×_U U₀`, to `m₀ : T ×_U U₀ ⟶ Q₀`. Then the
restriction of `pushforwardGraph` along `ψ` is any graph over `T` containing the section of `E`
given by `m₀`. -/
theorem pushforwardGraph_restrict_eq (hsq₀ : IsPullback fst₀ (uliftYoneda.{u + 1}.map i₀) ι ξ)
    (hsq₁ : IsPullback fst₁ (uliftYoneda.{u + 1}.map q) c fst₀) (hsq : IsPullback k q p i₀)
    {T : BigFppfOver B S hS} {a : T ⟶ U} {ψ : T ⟶ P} (hψp : ψ ≫ p = a)
    {m₀ : pullback a i₀ ⟶ Q₀} (hψk : pullback.fst a i₀ ≫ ψ = m₀ ≫ k)
    (hm₀q : m₀ ≫ q = pullback.snd a i₀) {x : X.obj (Opposite.op T)}
    {R : ∀ T' : BigFppfOver B S hS, (T' ⟶ T) → X₀.obj (Opposite.op T') →
      Set (E.obj (Opposite.op T'))}
    (hR : IsPushforwardSection ι c x R) (hx : X.map ψ.op (ξ.app _ ⟨p⟩) = x)
    (he₀ : fst₁.app (Opposite.op (pullback a i₀)) ⟨m₀⟩ ∈
      R (pullback a i₀) (pullback.fst a i₀)
        (fst₀.app (Opposite.op (pullback a i₀)) ⟨pullback.snd a i₀⟩)) :
    (fun T' g z ↦ pushforwardGraph fst₀ fst₁ q k T' (g ≫ ψ) z) = R := by
  have hR' := (isPushforwardSection_pushforwardGraph hsq₀ hsq₁ hsq).restrict ψ
  rw [hx] at hR'
  refine IsPushforwardSection.eq_of_subset hR' hR fun T' g z e he ↦ ?_
  obtain ⟨m, hmk, hmz, rfl⟩ := he
  change m ≫ k = g ≫ ψ at hmk
  have hn : g ≫ a = (m ≫ q) ≫ i₀ := by
    rw [← hψp, ← Category.assoc, ← hmk, Category.assoc, hsq.w, Category.assoc]
  let n : T' ⟶ pullback a i₀ := pullback.lift g (m ≫ q) hn
  have hnt : n ≫ pullback.fst a i₀ = g := pullback.lift_fst _ _ _
  have hnt₀ : n ≫ pullback.snd a i₀ = m ≫ q := pullback.lift_snd _ _ _
  have hnm : n ≫ m₀ = m := hsq.hom_ext
    (by rw [Category.assoc, ← hψk, ← Category.assoc, hnt, hmk])
    (by rw [Category.assoc, hm₀q, hnt₀])
  have hz : X₀.map n.op (fst₀.app (Opposite.op (pullback a i₀)) ⟨pullback.snd a i₀⟩) = z := by
    rw [← hmz, ← app_up_comp]
    exact congrArg (fun m' ↦ fst₀.app (Opposite.op T') ⟨m'⟩) hnt₀
  have := hR.map _ T' n _ _ _ he₀
  rwa [hnt, hz, ← app_up_comp, hnm] at this

/-- A section `w` of the pushforward over `T`, lying over `ξ` at `a : T ⟶ U`, is the restriction
of the section `pushforwardGraph` over `P` along a unique `b : T ⟶ P` over `U`. -/
theorem existsUnique_map_pushforwardGraph
    (hsq₀ : IsPullback fst₀ (uliftYoneda.{u + 1}.map i₀) ι ξ)
    (hsq₁ : IsPullback fst₁ (uliftYoneda.{u + 1}.map q) c fst₀) (hsq : IsPullback k q p i₀)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i₀))
    (hp : Etale ((BigFppfOver.toScheme B S hS).map p)) {T : BigFppfOver B S hS}
    (w : (thickeningPushforward ι c).obj (Opposite.op T)) (a : T ⟶ U)
    (hwa : w.1.1 = ξ.app _ ⟨a⟩) :
    ∃! b : T ⟶ P, (thickeningPushforward ι c).map b.op
      ⟨(ξ.app _ ⟨p⟩, pushforwardGraph fst₀ fst₁ q k),
        isPushforwardSection_pushforwardGraph hsq₀ hsq₁ hsq⟩ = w ∧ b ≫ p = a := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i₀) :=
    hi.1
  let t' := pullback.fst a i₀
  let t₀ := pullback.snd a i₀
  let z₀ := fst₀.app (Opposite.op (pullback a i₀)) ⟨t₀⟩
  have hz₀ : ι.app _ z₀ = X.map t'.op w.1.1 := by
    refine (app_eq_of_isPullback hsq₀ t₀).trans ?_
    rw [← pullback.condition, app_up_comp, hwa]
  obtain ⟨e₀, he₀⟩ := w.2.nonempty _ t' z₀ hz₀
  have hce₀ : c.app _ e₀ = z₀ := (w.2.mem _ _ _ _ he₀).2
  obtain ⟨m₀, hm₀e, hm₀q'⟩ := exists_lift_of_isPullback hsq₁ e₀ t₀ hce₀
  obtain ⟨ψ, ⟨hψp, hψk⟩, hψuniq⟩ :=
    uniqueLiftingAlong_bigFppfOver B S hS i₀ a p
      (Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective _ hi.2) hp t' t₀ k q
      (IsPullback.of_hasPullback a i₀) hsq m₀ hm₀q'
  have hψ₁ : X.map ψ.op (ξ.app _ ⟨p⟩) = w.1.1 := by
    rw [← app_up_comp, hψp, hwa]
  refine ⟨ψ, ⟨Subtype.ext (Prod.ext hψ₁ ?_), hψp⟩, fun b ⟨hbw, hbp⟩ ↦ hψuniq b ⟨hbp, ?_⟩⟩
  · exact pushforwardGraph_restrict_eq hsq₀ hsq₁ hsq hψp hψk hm₀q' w.2 hψ₁
      (by rwa [hm₀e])
  · have he₀' : e₀ ∈ pushforwardGraph fst₀ fst₁ q k _ (t' ≫ b) z₀ := by
      change e₀ ∈ (fun T' g z ↦ pushforwardGraph fst₀ fst₁ q k T' (g ≫ b) z) _ t' z₀
      rwa [show (fun T' g z ↦ pushforwardGraph fst₀ fst₁ q k T' (g ≫ b) z) = w.1.2 from
        congrArg (fun v ↦ v.1.2) hbw]
    obtain ⟨m, hmk, hmz, hme⟩ := he₀'
    have hmq : m ≫ q = t₀ := eq_of_isPullback hsq₀ hmz (by
      rw [Category.assoc, ← hsq.w, ← Category.assoc, hmk, Category.assoc, hbp,
        pullback.condition])
    have hmm : m = m₀ :=
      eq_of_isPullback hsq₁ (hme.symm.trans hm₀e.symm) (hmq.trans hm₀q'.symm)
    rw [← hmk, hmm]

end Graph

/-- **The base change of the pushforward along a point is represented by an étale object.** For
a point `ξ : T ⟶ X`, the base change of the pushforward along `ξ` is represented by the étale
lift, along the thickening `T ×_X X₀ ⟶ T`, of the étale object `(T ×_X X₀) ×_{X₀} E`. -/
theorem exists_isPullback_thickeningPushforwardπ
    (hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι)
    (hc : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} c)
    {U : BigFppfOver B S hS} (ξ : uliftYoneda.{u + 1}.obj U ⟶ X) :
    ∃ (P : BigFppfOver B S hS) (p : P ⟶ U)
      (r : uliftYoneda.{u + 1}.obj P ⟶ thickeningPushforward ι c),
      Etale ((BigFppfOver.toScheme B S hS).map p) ∧
        IsPullback r (uliftYoneda.{u + 1}.map p) (thickeningPushforwardπ ι c) ξ := by
  obtain ⟨U₀, i₀, fst₀, hsq₀⟩ := hι.rep ξ
  have hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i₀) :=
    hι.property ξ fst₀ i₀ hsq₀
  obtain ⟨Q₀, q, fst₁, hsq₁⟩ := hc.rep fst₀
  obtain ⟨P, p, k, hp, hsq⟩ :=
    exists_etale_isPullback_of_isThickening B S hS i₀ hi q (hc.property fst₀ fst₁ q hsq₁)
  let r₀ : (thickeningPushforward ι c).obj (Opposite.op P) :=
    ⟨(ξ.app _ ⟨p⟩, pushforwardGraph fst₀ fst₁ q k),
      isPushforwardSection_pushforwardGraph hsq₀ hsq₁ hsq⟩
  refine ⟨P, p, uliftYonedaEquiv.symm r₀, hp,
    isPullback_of_existsUnique_app ?_ fun T w a hwa ↦ ?_⟩
  · ext T ⟨b⟩
    change X.map b.op (ξ.app _ ⟨p⟩) = ξ.app T ⟨b ≫ p⟩
    rw [app_up_comp]
  · obtain ⟨T⟩ := T
    obtain ⟨a⟩ := a
    obtain ⟨ψ, ⟨hψw, hψp⟩, hψ⟩ := existsUnique_map_pushforwardGraph hsq₀ hsq₁ hsq hi hp w a hwa
    exact ⟨⟨ψ⟩, ⟨hψw, congrArg ULift.up hψp⟩,
      fun ⟨b⟩ ⟨hbw, hbp⟩ ↦ congrArg ULift.up (hψ b ⟨hbw, congrArg ULift.down hbp⟩)⟩

/-- For a cartesian square exhibiting `uliftYoneda P` as the base change of `π : F ⟶ X` along
`ξ`, a section of `F` over `Y` lying over `ξ` at `f : Y ⟶ U` comes from a lift of `f` to `P`. -/
theorem exists_lift_of_isPullback_uliftYoneda {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {π : F ⟶ X} {U P : BigFppfOver B S hS} {p : P ⟶ U} {r : uliftYoneda.{u + 1}.obj P ⟶ F}
    {ξ : uliftYoneda.{u + 1}.obj U ⟶ X} (hpb : IsPullback r (uliftYoneda.{u + 1}.map p) π ξ)
    {Y : BigFppfOver B S hS} (s : F.obj (Opposite.op Y)) (f : Y ⟶ U)
    (hs : π.app _ s = ξ.app _ ⟨f⟩) : ∃ l : Y ⟶ P, r.app _ ⟨l⟩ = s ∧ l ≫ p = f :=
  exists_lift_of_isPullback hpb s f hs

/-- For a cartesian square exhibiting `uliftYoneda P` as the base change of `π : F ⟶ X` along
`ξ`, two morphisms into `P` with the same section of `F` and the same composite with `p` are
equal. -/
theorem eq_of_isPullback_uliftYoneda {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {π : F ⟶ X} {U P : BigFppfOver B S hS} {p : P ⟶ U} {r : uliftYoneda.{u + 1}.obj P ⟶ F}
    {ξ : uliftYoneda.{u + 1}.obj U ⟶ X} (hpb : IsPullback r (uliftYoneda.{u + 1}.map p) π ξ)
    {Y : BigFppfOver B S hS} {a b : Y ⟶ P} (h₁ : r.app (Opposite.op Y) ⟨a⟩ = r.app _ ⟨b⟩)
    (h₂ : a ≫ p = b ≫ p) : a = b :=
  eq_of_isPullback hpb h₁ h₂

/-- Let the base change of `π : F ⟶ X` along `ξ : T ⟶ X` be represented by `P`, where `ξ` is the
section `x`. A compatible family `s` of sections of `F` over a presieve `R` on `T` for which
`uliftYoneda P` is a sheaf and `X` is separated has a unique amalgamation, when `x` amalgamates
the family it induces on `X`. -/
theorem existsUnique_isAmalgamation_of_isPullback_uliftYoneda
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {π : F ⟶ X} {T P : BigFppfOver B S hS}
    {p : P ⟶ T} {r : uliftYoneda.{u + 1}.obj P ⟶ F} {ξ : uliftYoneda.{u + 1}.obj T ⟶ X}
    (hpb : IsPullback r (uliftYoneda.{u + 1}.map p) π ξ) {x : X.obj (Opposite.op T)}
    (hξ : ∀ {Y : BigFppfOver B S hS} (f : Y ⟶ T), ξ.app (Opposite.op Y) ⟨f⟩ = X.map f.op x)
    {R : Presieve T} (hP : Presieve.IsSheafFor (uliftYoneda.{u + 1}.obj P) R)
    (hX : Presieve.IsSeparatedFor X R) {s : Presieve.FamilyOfElements F R} (hs : s.Compatible)
    (hx : (s.map π).IsAmalgamation x) : ∃! t, s.IsAmalgamation t := by
  have hlift : ∀ {Y : BigFppfOver B S hS} (f : Y ⟶ T) (hf : R f), ∃ l : Y ⟶ P,
      r.app _ ⟨l⟩ = s f hf ∧ l ≫ p = f := fun f hf ↦
    exists_lift_of_isPullback_uliftYoneda hpb (s f hf) f (by rw [hξ]; exact (hx f hf).symm)
  let l : ∀ {Y : BigFppfOver B S hS} (f : Y ⟶ T), R f → (Y ⟶ P) :=
    fun f hf ↦ (hlift f hf).choose
  have hl₁ : ∀ {Y : BigFppfOver B S hS} (f : Y ⟶ T) (hf : R f), r.app _ ⟨l f hf⟩ = s f hf :=
    fun f hf ↦ (hlift f hf).choose_spec.1
  have hl₂ : ∀ {Y : BigFppfOver B S hS} (f : Y ⟶ T) (hf : R f), l f hf ≫ p = f :=
    fun f hf ↦ (hlift f hf).choose_spec.2
  let lf : Presieve.FamilyOfElements (uliftYoneda.{u + 1}.obj P) R := fun _ f hf ↦
    ULift.up (l f hf)
  have hlf : lf.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    change (⟨g₁ ≫ l f₁ h₁⟩ : ULift.{u + 1} (Z ⟶ P)) = ⟨g₂ ≫ l f₂ h₂⟩
    refine congrArg ULift.up (eq_of_isPullback_uliftYoneda hpb ?_ ?_)
    · rw [app_up_comp, app_up_comp, hl₁, hl₁]
      exact hs g₁ g₂ h₁ h₂ hcomm
    · rw [Category.assoc, Category.assoc, hl₂, hl₂, hcomm]
  let lt := hP.amalgamate lf hlf
  have hlt : lf.IsAmalgamation lt := hP.isAmalgamation hlf
  refine ⟨r.app _ lt, fun Y f hf ↦ ?_, fun t ht ↦ ?_⟩
  · rw [← NatTrans.naturality_apply, hlt f hf]
    exact hl₁ f hf
  · have htx : π.app _ t = x := hX _ _ _
      (fun Y f hf ↦ by rw [← NatTrans.naturality_apply, ht f hf]; rfl) hx
    obtain ⟨l', hl'₁, hl'₂⟩ := exists_lift_of_isPullback_uliftYoneda hpb t (𝟙 T)
      (by rw [htx, hξ]; simp)
    have hl't : lf.IsAmalgamation ⟨l'⟩ := by
      intro Y f hf
      change (⟨f ≫ l'⟩ : ULift.{u + 1} (Y ⟶ P)) = ⟨l f hf⟩
      refine congrArg ULift.up (eq_of_isPullback_uliftYoneda hpb ?_ ?_)
      · rw [app_up_comp, hl₁, hl'₁]
        exact ht f hf
      · rw [Category.assoc, hl'₂, hl₂, Category.comp_id]
    rw [← hl'₁, hP.isSeparatedFor lf _ _ hl't hlt]

/-- **The sheaf condition descends along a morphism whose base changes along points are
representable.** Let `π : F ⟶ X` be a morphism of presheaves on the big fppf site of `S`, valued
in `Type (u + 1)`, into a sheaf. If the base change of `π` along every universe-lifted
scheme-valued point of `X` is represented by an object of the site, then `F` is a sheaf. -/
theorem isSheaf_of_forall_isPullback_uliftYoneda
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (π : F ⟶ X)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (h : ∀ (U : BigFppfOver B S hS) (ξ : uliftYoneda.{u + 1}.obj U ⟶ X),
      ∃ (P : BigFppfOver B S hS) (p : P ⟶ U) (r : uliftYoneda.{u + 1}.obj P ⟶ F),
        IsPullback r (uliftYoneda.{u + 1}.map p) π ξ) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) F := by
  let J := BigFppfOver.topology B S hS
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have hrep : ∀ P : BigFppfOver B S hS, Presieve.IsSheaf J (uliftYoneda.{u + 1}.obj P) :=
    fun P ↦ (CategoryTheory.isSheaf_iff_isSheaf_of_type J _).1
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS P).isSheaf
  have hX' : Presieve.IsSheaf J X := (CategoryTheory.isSheaf_iff_isSheaf_of_type J X).1 hX
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  intro T R hR s hs
  have hπs := hs.map π
  let x := (hX' R hR).amalgamate _ hπs
  obtain ⟨P, p, r, hpb⟩ := h T (uliftYonedaEquiv.symm x)
  exact existsUnique_isAmalgamation_of_isPullback_uliftYoneda hpb (x := x) (fun _ ↦ rfl)
    (hrep P R hR) (hX' R hR).isSeparatedFor hs ((hX' R hR).isAmalgamation hπs)

end Pushforward

/-! ### The transported chart -/

/-- **Transport of an étale chart along a representable thickening.** Let `ι : X₀ ⟶ X` be a
morphism of fppf sheaves over `S` every base change of which along a scheme-valued point of `X`
is a thickening of schemes, and let `c : E ⟶ X₀` be representable by objects of the site and
étale. Then there is `π : W ⟶ X`, representable by objects of the site and étale, whose base
change along `ι` is `c`. -/
theorem exists_etale_isPullback_of_isRepresentableThickeningULift
    {X X₀ E : FppfSheaf B S hS} (ι : X₀ ⟶ X) (c : E ⟶ X₀)
    (hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom)
    (hc : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} c.hom) :
    ∃ (W : FppfSheaf B S hS) (π : W ⟶ X) (j : E ⟶ W),
      (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} π.hom ∧
      IsPullback j c π ι := by
  have hmono : Mono ι.hom := mono_of_isRepresentableThickeningULift B S hS hι
  have hinj : ∀ T, Function.Injective (ι.hom.app T) := fun T ↦
    (mono_iff_injective (ι.hom.app T)).1 inferInstance
  have hpt : ∀ {U : BigFppfOver B S hS} (ξ : uliftYoneda.{u + 1}.obj U ⟶ X.obj), _ :=
    fun ξ ↦ exists_isPullback_thickeningPushforwardπ (B := B) (S := S) (hS := hS) hι hc ξ
  have hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (thickeningPushforward ι.hom c.hom) :=
    isSheaf_of_forall_isPullback_uliftYoneda (B := B) (S := S) (hS := hS)
      (thickeningPushforwardπ ι.hom c.hom) X.property fun U ξ ↦
        (hpt ξ).imp fun P ⟨p, r, _, hsq⟩ ↦ ⟨p, r, hsq⟩
  let W : FppfSheaf B S hS := ⟨thickeningPushforward ι.hom c.hom, hW⟩
  let π : W ⟶ X := ⟨thickeningPushforwardπ ι.hom c.hom⟩
  let j : E ⟶ W := ⟨thickeningPushforwardι hinj⟩
  refine ⟨W, π, j, MorphismProperty.relative.of_exists fun U ξ ↦ ?_, ?_⟩
  · exact (hpt ξ).imp fun P ⟨p, r, hp, hsq⟩ ↦ ⟨r, p, hsq, hp⟩
  · have hpre : IsPullback ((sheafToPresheaf _ _).map j) ((sheafToPresheaf _ _).map c)
        ((sheafToPresheaf _ _).map π) ((sheafToPresheaf _ _).map ι) :=
      isPullback_thickeningPushforwardι hinj
    exact IsPullback.of_map (sheafToPresheaf _ _)
      ((sheafToPresheaf _ _).map_injective (by simpa using hpre.w)) hpre

end AlgebraicGeometry.FormalSpace

end
