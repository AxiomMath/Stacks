module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.OfIsSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothnessOverNoetherianBase
public import StacksCore.Tactic.StacksAttribute

/-!
# The infinitesimal lifting criterion for smoothness over a Noetherian base, unconditionally

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` locally Noetherian. Then `f` is smooth exactly when every solid square

  `Spec B ⟶ X`, `Spec B' ⟶ Y`, over a small extension `B' ⟶ B` of Artinian local rings whose
  map `Spec B' ⟶ Y` is locally of finite type,

admits a dotted arrow `Spec B' ⟶ X`. This is Stacks 0APP.

## Main results

* `AlgebraicGeometry.Space.FormallySmooth.exists_lift_of_isSquareZeroSurjection`: a formally
  smooth morphism of algebraic spaces solves every lifting problem along the spectrum of a
  surjection of rings with square-zero kernel.
* `AlgebraicGeometry.Space.IsSmooth.exists_lift_of_isSquareZeroSurjection`: the same for a smooth
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.LiftsAgainstFiniteTypeSmallExtensions` is condition (2) of
  Stacks 0APP read literally, with the test morphism of finite type, and
  `AlgebraicGeometry.Space.IsSmooth.liftsAgainstFiniteTypeSmallExtensions` is the implication
  (1) ⇒ (2) of Stacks 0APP as stated.
* `AlgebraicGeometry.Space.exists_lift_chart_of_isSquareZeroClosedImmersion`: a lifting problem
  for a commuting square of étale charts is solved by any solution of the corresponding lifting
  problem in the algebraic spaces.
* `AlgebraicGeometry.Space.isSmooth_iff_forall_exists_lift_isSmallExtension` is **Stacks 0APP**.

## Implementation notes

The implication from smoothness is the formal smoothness of a smooth morphism of algebraic
spaces, Stacks 04AM, which is `AlgebraicGeometry.Space.formallySmooth_of_isSmooth'` and carries
no hypothesis beyond smoothness; so no descent statement is assumed here. The converse runs, on
each commuting square of étale charts `h : U ⟶ V` of `f` (with `V` locally Noetherian and `h`
locally of finite type), the scheme-level global criterion
`AlgebraicGeometry.smooth_iff_lifts_finiteType_smallExtensions` (Stacks 02HY): a lifting problem
for `h` is pushed into `X` along the chart, solved there, and pulled back to `U` because the
charts are formally étale (Stacks 04AL). Finite type of the scheme-level test map places the two
Artinian spectra below the cutoff of the site.

The spectra of the test rings are presented as objects of the big fppf site together with
isomorphisms of their underlying schemes with those spectra, as in
`AlgebraicGeometry.Space.isSmooth_iff_exists_lift_of_isSmallExtension`.

### Why the test map is only required to be locally of finite type

The source asks the test map `Spec B' ⟶ Y` to be of finite type, that is locally of finite type
and quasi-compact. With that condition the converse implication is false:
`AlgebraicGeometry.Space.not_forall_isSmooth_iff_liftsAgainstFiniteTypeSmallExtensions`, in
`StacksFrontier/AlgebraicGeometry/Spaces/SmoothnessFiniteTypeLiftingCounterexample.lean`, proves
that the point `Spec ℚ ⟶ 𝔸¹_ℚ/ℤ` of the zero section, in the quotient of the affine line by the
translation action of the integers, satisfies the literal condition (2) and is not smooth. Over
that non-quasi-separated target no test morphism of a square for this point is quasi-compact, so
the literal condition holds for want of a test square. The hypothesis kept here is therefore
`AlgebraicGeometry.Space.IsLocallyOfFiniteType`, which is never vacuous; the implication from
smoothness holds with either condition.

## References

* [Stacks Project, Tag 02HY](https://stacks.math.columbia.edu/tag/02HY)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 0APP](https://stacks.math.columbia.edu/tag/0APP)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Commutation of a square of presheaf maps, read on the elements given by Yoneda. -/
private theorem app_yonedaEquiv_eq_map_of_comp_eq {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X ⟶ Y) {T T' : BigFppfOver B S hS} (i : T ⟶ T') (α : yoneda.obj T ⟶ X)
    (β : yoneda.obj T' ⟶ Y) (h : α ≫ g = yoneda.map i ≫ β) :
    g.app (op T) (yonedaEquiv α) = Y.map i.op (yonedaEquiv β) :=
  calc
    g.app (op T) (yonedaEquiv α) = yonedaEquiv (α ≫ g) := (yonedaEquiv_comp α g).symm
    _ = yonedaEquiv (yoneda.map i ≫ β) := congrArg yonedaEquiv h
    _ = Y.map i.op (yonedaEquiv β) := (yonedaEquiv_naturality β i).symm

/-- An element `z` restricting along `i` to `yonedaEquiv α` gives a morphism extending `α`. -/
private theorem map_comp_symm_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T T' : BigFppfOver B S hS} (i : T ⟶ T') (α : yoneda.obj T ⟶ X) (z : X.obj (op T'))
    (hz : X.map i.op z = yonedaEquiv α) : yoneda.map i ≫ yonedaEquiv.symm z = α := by
  apply yonedaEquiv.injective
  rw [← yonedaEquiv_naturality (yonedaEquiv.symm z) i]
  simpa using hz

/-- An element `z` mapping under `g` to `yonedaEquiv β` gives a morphism lying over `β`. -/
private theorem symm_comp_eq {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X ⟶ Y)
    {T' : BigFppfOver B S hS} (β : yoneda.obj T' ⟶ Y) (z : X.obj (op T'))
    (hz : g.app (op T') z = yonedaEquiv β) : yonedaEquiv.symm z ≫ g = β := by
  apply yonedaEquiv.injective
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hz

/-- A formally smooth morphism of algebraic spaces solves every lifting problem along the
spectrum of a surjection `φ : R' ⟶ R` of rings with square-zero kernel: the site morphism
presenting `Spec φ` is a square-zero closed immersion of affine objects, so the problem is one of
those in the definition of formal smoothness. -/
theorem FormallySmooth.exists_lift_of_isSquareZeroSurjection
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (hformal : FormallySmooth f)
    {R' R : CommRingCat.{u}} (φ : R' ⟶ R)
    (hφ : InfinitesimalLifting.IsSquareZeroSurjection φ)
    {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
    (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R')
    (hi : (BigFppfOver.toScheme B S hS).map i = e.hom ≫ Spec.map φ ≫ e'.inv)
    (α : yoneda.obj T ⟶ X) (β : yoneda.obj T' ⟶ Y)
    (hcomm : α ≫ f = yoneda.map i ≫ β) :
    ∃ γ : yoneda.obj T' ⟶ X, yoneda.map i ≫ γ = α ∧ γ ≫ f = β := by
  have hsite : IsSquareZeroClosedImmersion B S hS i :=
    isSquareZeroClosedImmersion_of_specMap B S hS φ hφ.2.2.1 hφ.2.2.2 T T' i e e' hi
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := IsAffine.of_isIso e.hom
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := IsAffine.of_isIso e'.hom
  obtain ⟨z, hz⟩ := hformal T T' ‹_› ‹_› i hsite (yonedaEquiv α) (yonedaEquiv β)
    (app_yonedaEquiv_eq_map_of_comp_eq B S hS f i α β hcomm)
  exact ⟨yonedaEquiv.symm z, map_comp_symm_eq B S hS i α z hz.1, symm_comp_eq B S hS f β z hz.2⟩

/-- A smooth morphism of algebraic spaces solves every lifting problem along the spectrum of a
surjection of rings with square-zero kernel, since it is formally smooth (Stacks 04AM). -/
theorem IsSmooth.exists_lift_of_isSquareZeroSurjection
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsSmooth B S hS f)
    {R' R : CommRingCat.{u}} (φ : R' ⟶ R)
    (hφ : InfinitesimalLifting.IsSquareZeroSurjection φ)
    {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
    (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R')
    (hi : (BigFppfOver.toScheme B S hS).map i = e.hom ≫ Spec.map φ ≫ e'.inv)
    (α : yoneda.obj T ⟶ X) (β : yoneda.obj T' ⟶ Y)
    (hcomm : α ≫ f = yoneda.map i ≫ β) :
    ∃ γ : yoneda.obj T' ⟶ X, yoneda.map i ≫ γ = α ∧ γ ≫ f = β :=
  FormallySmooth.exists_lift_of_isSquareZeroSurjection B S hS
    (formallySmooth_of_isSmooth' hX hY hf) φ hφ i e e' hi α β hcomm

/-- **Condition (2) of Stacks 0APP, read literally.** Every solid square

  `α : Spec R ⟶ X`, `β : Spec R' ⟶ Y`, over a small extension `φ : R' ⟶ R` of Artinian local
  rings, with `β` *of finite type* (locally of finite type and quasi-compact, Stacks 03XF),

admits a dotted arrow `γ : Spec R' ⟶ X` making both triangles commute. The spectra are
presented by objects of the big fppf site together with isomorphisms of their underlying schemes
with the spectra. -/
def LiftsAgainstFiniteTypeSmallExtensions {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) : Prop :=
  ∀ ⦃R' R : CommRingCat.{u}⦄ (φ : R' ⟶ R),
    InfinitesimalLifting.IsSmallExtension φ →
    ∀ (T T' : BigFppfOver B S hS) (i : T ⟶ T')
      (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
      (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R'),
      (BigFppfOver.toScheme B S hS).map i = e.hom ≫ Spec.map φ ≫ e'.inv →
      ∀ (α : yoneda.obj T ⟶ X) (β : yoneda.obj T' ⟶ Y),
        IsFiniteType B S hS β →
        α ≫ f = yoneda.map i ≫ β →
        ∃ γ : yoneda.obj T' ⟶ X, yoneda.map i ≫ γ = α ∧ γ ≫ f = β

/-- **Stacks 0APP, (1) implies (2), as stated.** A smooth morphism of algebraic spaces
satisfies condition (2) of Stacks 0APP with the test morphism of finite type. No hypothesis on
the target is needed. -/
@[stacks 0APP "(1) implies (2) as stated, with the test morphism Spec B' ⟶ Y of finite type"]
theorem IsSmooth.liftsAgainstFiniteTypeSmallExtensions
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsSmooth B S hS f) : LiftsAgainstFiniteTypeSmallExtensions B S hS f :=
  fun _ _ φ hφ _ _ i e e' hi α β _ hcomm =>
    IsSmooth.exists_lift_of_isSquareZeroSurjection B S hS hX hY hf φ
      (InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection φ hφ) i e e' hi α β hcomm

/-- Let `h : U ⟶ V` be a commuting square of étale charts `a`, `b` of `f : X ⟶ Y`, and let
`i : T ⟶ T'` be a square-zero closed immersion of affine objects of the site. A lifting problem
`α`, `β` for `h` along `i` is solved as soon as the lifting problem `α ≫ a`, `β ≫ b` for `f` has
a solution `γX`: the source chart is formally étale, so `γX` lifts uniquely through it, and the
target chart is formally étale too, which identifies the image of that lift in `V` with `β`. -/
theorem exists_lift_chart_of_isSquareZeroClosedImmersion
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {U V : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ f)
    {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    (hsite : IsSquareZeroClosedImmersion B S hS i)
    (α : yoneda.obj T ⟶ yoneda.obj U) (β : yoneda.obj T' ⟶ yoneda.obj V)
    (hαβ : α ≫ yoneda.map h = yoneda.map i ≫ β)
    (γX : yoneda.obj T' ⟶ X) (hγX₁ : yoneda.map i ≫ γX = α ≫ a) (hγX₂ : γX ≫ f = β ≫ b) :
    ∃ γ : yoneda.obj T' ⟶ yoneda.obj U,
      yoneda.map i ≫ γ = α ∧ γ ≫ yoneda.map h = β := by
  have haFormal : FormallyEtale a := formallyEtale_of_etale B S hS a ha
  have hbFormal : FormallyEtale b := formallyEtale_of_etale B S hS b hb
  obtain ⟨z, hz, -⟩ := haFormal T T' ‹_› ‹_› i hsite (yonedaEquiv α) (yonedaEquiv γX)
    (app_yonedaEquiv_eq_map_of_comp_eq B S hS a i α γX hγX₁.symm)
  let γ := yonedaEquiv.symm z
  have hγα : yoneda.map i ≫ γ = α := map_comp_symm_eq B S hS i α z hz.1
  have hγa : γ ≫ a = γX := symm_comp_eq B S hS a γX z hz.2
  have hsource := app_yonedaEquiv_eq_map_of_comp_eq B S hS b i (α ≫ yoneda.map h) (β ≫ b)
    (by rw [hαβ, Category.assoc])
  obtain ⟨zb, -, huniq⟩ := hbFormal T T' ‹_› ‹_› i hsite
    (yonedaEquiv (α ≫ yoneda.map h)) (yonedaEquiv (β ≫ b)) hsource
  have hcandidate : IsLift b i (yonedaEquiv (α ≫ yoneda.map h))
      (yonedaEquiv (β ≫ b)) (yonedaEquiv (γ ≫ yoneda.map h)) := by
    constructor
    · calc
        (yoneda.obj V).map i.op (yonedaEquiv (γ ≫ yoneda.map h)) =
            yonedaEquiv (yoneda.map i ≫ γ ≫ yoneda.map h) :=
          yonedaEquiv_naturality (γ ≫ yoneda.map h) i
        _ = yonedaEquiv (α ≫ yoneda.map h) := by
          rw [← Category.assoc, hγα]
    · calc
        b.app (op T') (yonedaEquiv (γ ≫ yoneda.map h)) =
            yonedaEquiv ((γ ≫ yoneda.map h) ≫ b) := (yonedaEquiv_comp _ b).symm
        _ = yonedaEquiv (γX ≫ f) := by
          rw [Category.assoc, hcomm, ← Category.assoc, hγa]
        _ = yonedaEquiv (β ≫ b) := congrArg yonedaEquiv hγX₂
  have hβlift : IsLift b i (yonedaEquiv (α ≫ yoneda.map h))
      (yonedaEquiv (β ≫ b)) (yonedaEquiv β) := by
    constructor
    · calc
        (yoneda.obj V).map i.op (yonedaEquiv β) = yonedaEquiv (yoneda.map i ≫ β) :=
          yonedaEquiv_naturality β i
        _ = yonedaEquiv (α ≫ yoneda.map h) := congrArg yonedaEquiv hαβ.symm
    · exact yonedaEquiv_comp β b
  exact ⟨γ, hγα, yonedaEquiv.injective ((huniq _ hcandidate).trans (huniq _ hβlift).symm)⟩

/-- Let `h : U ⟶ V` be a commuting square of étale charts `a`, `b` of `f : X ⟶ Y`, and let
`i : T ⟶ T'` be a square-zero closed immersion of affine objects of the site. A lifting problem
`aT`, `bT'` of morphisms of the site for `h` along `i` is solved as soon as the lifting problem
`yoneda.map aT ≫ a`, `yoneda.map bT' ≫ b` for `f` has a solution `γX`. -/
theorem exists_lift_site_of_isSquareZeroClosedImmersion
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {U V : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ f)
    {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    (hsite : IsSquareZeroClosedImmersion B S hS i)
    (aT : T ⟶ U) (bT' : T' ⟶ V) (hsq : aT ≫ h = i ≫ bT')
    (γX : yoneda.obj T' ⟶ X) (hγX₁ : yoneda.map i ≫ γX = yoneda.map aT ≫ a)
    (hγX₂ : γX ≫ f = yoneda.map bT' ≫ b) :
    ∃ γ : T' ⟶ U, i ≫ γ = aT ∧ γ ≫ h = bT' := by
  obtain ⟨γ, hγ₁, hγ₂⟩ := exists_lift_chart_of_isSquareZeroClosedImmersion B S hS f a b h ha hb
    hcomm i hsite (yoneda.map aT) (yoneda.map bT')
    (by simpa only [Functor.map_comp] using congrArg yoneda.map hsq) γX hγX₁ hγX₂
  obtain ⟨g, rfl⟩ := yoneda.map_surjective γ
  exact ⟨g, yoneda.map_injective (by rwa [Functor.map_comp]),
    yoneda.map_injective (by rwa [Functor.map_comp])⟩

/-- Let `b : V ⟶ Y` be an étale chart of an algebraic space and `g : T ⟶ V` a morphism of the
site whose underlying morphism of schemes is locally of finite type. Then `yoneda.map g ≫ b` is
locally of finite type: the identity of `T` is a surjective étale chart of its source, so
Stacks 03MJ computes the property on the square it forms with `b`. -/
theorem isLocallyOfFiniteType_yoneda_map_comp {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {T V : BigFppfOver B S hS} (b : yoneda.obj V ⟶ Y)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (g : T ⟶ V) (hg : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g)) :
    IsLocallyOfFiniteType B S hS (yoneda.map g ≫ b) := by
  let F := BigFppfOver.toScheme B S hS
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (MorphismProperty.inverseImage (@Etale.{u}) F).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ F
  have : (MorphismProperty.inverseImage (@Surjective.{u}) F).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ F
  apply (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    (isAlgebraicSpace_yoneda B S hS T) hY (yoneda.map g ≫ b)).mpr
  refine ⟨T, V, 𝟙 _, b, g, ?_, hb, ?_, ?_, hg⟩
  · apply MorphismProperty.relative.of_exists
    intro W g
    refine ⟨W, g, 𝟙 W, ?_, ?_⟩
    · simpa only [yoneda.map_id] using CategoryTheory.IsPullback.of_id_snd
    · change Etale (F.map (𝟙 W))
      rw [F.map_id]
      infer_instance
  · apply MorphismProperty.relative.of_exists
    intro W g
    refine ⟨W, g, 𝟙 W, ?_, ?_⟩
    · simpa only [yoneda.map_id] using CategoryTheory.IsPullback.of_id_snd
    · change Surjective (F.map (𝟙 W))
      rw [F.map_id]
      infer_instance
  · simp

/-- Let `f : X ⟶ Y` satisfy the lifting property of Stacks 0APP, and let `h : U ⟶ V` be a
commuting square of étale charts `a`, `b` of `f`. Then every lifting problem for `h` along the
spectrum of a small extension `φ : R' ⟶ R`, with test map `β` of finite type, has a solution:
the two spectra are objects of the site, the problem is solved in `X`, and the solution is pulled
back along the formally étale charts. -/
theorem exists_lift_chart_of_forall_exists_lift
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hlift : ∀ ⦃R' R : CommRingCat.{u}⦄ (φ : R' ⟶ R),
      InfinitesimalLifting.IsSmallExtension φ →
      ∀ (T T' : BigFppfOver B S hS) (i : T ⟶ T')
        (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
        (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R'),
        (BigFppfOver.toScheme B S hS).map i = e.hom ≫ Spec.map φ ≫ e'.inv →
        ∀ (α : yoneda.obj T ⟶ X) (β : yoneda.obj T' ⟶ Y),
          IsLocallyOfFiniteType B S hS β →
          α ≫ f = yoneda.map i ≫ β →
          ∃ γ : yoneda.obj T' ⟶ X, yoneda.map i ≫ γ = α ∧ γ ≫ f = β)
    {U V : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hchart : yoneda.map h ≫ b = a ≫ f)
    {R' R : CommRingCat.{u}} (φ : R' ⟶ R) (hφ : InfinitesimalLifting.IsSmallExtension φ)
    (α : Spec R ⟶ (BigFppfOver.toScheme B S hS).obj U)
    (β : Spec R' ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (hβ : LocallyOfFiniteType β ∧ QuasiCompact β)
    (hcomm : α ≫ (BigFppfOver.toScheme B S hS).map h = Spec.map φ ≫ β) :
    ∃ γ : Spec R' ⟶ (BigFppfOver.toScheme B S hS).obj U,
      Spec.map φ ≫ γ = α ∧ γ ≫ (BigFppfOver.toScheme B S hS).map h = β := by
  let F := BigFppfOver.toScheme B S hS
  have : LocallyOfFiniteType β := hβ.1
  have : QuasiCompact β := hβ.2
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_surjective φ hφ.2.2.2.2.1
  have hR' : B.Contains (Spec R') :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact β V.left.property
  have hR : B.Contains (Spec R) := Scheme.size_lt_of_isClosedImmersion (Spec.map φ) hR'
  let T₀ : B.Schemes := B.obj hR
  let T'₀ : B.Schemes := B.obj hR'
  let tU : T₀ ⟶ U.left := B.inclusion.preimage α
  let tV : T'₀ ⟶ V.left := B.inclusion.preimage β
  let i₀ : T₀ ⟶ T'₀ := B.inclusion.preimage (Spec.map φ)
  have hiBase : i₀ ≫ tV ≫ V.hom = tU ≫ U.hom := by
    apply B.inclusion.map_injective
    simp only [Functor.map_comp, i₀, tU, tV, B.inclusion.map_preimage]
    change Spec.map φ ≫ β ≫ B.inclusion.map V.hom = α ≫ B.inclusion.map U.hom
    rw [← reassoc_of% hcomm]
    change α ≫ B.inclusion.map h.left ≫ _ = _
    rw [← B.inclusion.map_comp, h.w]
  let T : BigFppfOver B S hS := Over.mk (tU ≫ U.hom)
  let T' : BigFppfOver B S hS := Over.mk (tV ≫ V.hom)
  let i : T ⟶ T' := Over.homMk i₀ hiBase
  let aT : T ⟶ U := Over.homMk tU (by simp [T])
  let bT' : T' ⟶ V := Over.homMk tV (by simp [T'])
  have hsiteSq : aT ≫ h = i ≫ bT' := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map tU ≫ B.inclusion.map h.left = B.inclusion.map i₀ ≫ B.inclusion.map tV
    simp only [tU, tV, i₀, B.inclusion.map_preimage]
    exact hcomm
  let e : F.obj T ≅ Spec R := Iso.refl _
  let e' : F.obj T' ≅ Spec R' := Iso.refl _
  have hi' : F.map i = Spec.map φ := B.inclusion.map_preimage _
  have hi : F.map i = e.hom ≫ Spec.map φ ≫ e'.inv := by
    rw [hi']
    change Spec.map φ = 𝟙 (Spec R) ≫ Spec.map φ ≫ 𝟙 (Spec R')
    simp
  have haT : F.map aT = α := B.inclusion.map_preimage _
  have hbT' : F.map bT' = β := B.inclusion.map_preimage _
  have : IsAffine (F.obj T) := IsAffine.of_isIso e.hom
  have : IsAffine (F.obj T') := IsAffine.of_isIso e'.hom
  have hsq := InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection φ hφ
  obtain ⟨γX, hγX₁, hγX₂⟩ := hlift φ hφ T T' i e e' hi (yoneda.map aT ≫ a) (yoneda.map bT' ≫ b)
    (isLocallyOfFiniteType_yoneda_map_comp B S hS hY b hb bT' (by rw [hbT']; exact hβ.1))
    (by rw [Category.assoc, ← hchart, ← Functor.map_comp_assoc, hsiteSq,
      Functor.map_comp_assoc])
  obtain ⟨γ, hγ₁, hγ₂⟩ := exists_lift_site_of_isSquareZeroClosedImmersion B S hS f a b h ha hb
    hchart i (isSquareZeroClosedImmersion_of_specMap B S hS φ hsq.2.2.1 hsq.2.2.2 T T' i e e' hi)
    aT bT' hsiteSq γX hγX₁ hγX₂
  exact ⟨F.map γ, by rw [← hi', ← F.map_comp, hγ₁, haT], by rw [← F.map_comp, hγ₂, hbT']⟩

/-- **Stacks 0APP.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, with `Y` locally Noetherian. Then `f` is smooth if and only if every
solid square whose vertical map is induced by a small extension `φ : R' ⟶ R` of Artinian local
rings and whose map `Spec R' ⟶ Y` is locally of finite type admits a dotted arrow making the
diagram commute.

The implication towards the lifting property is the formal smoothness of a smooth morphism
(Stacks 04AM). The converse runs the scheme-level criterion of Stacks 02HY on each commuting
square of étale charts, pushing each scheme-level lifting problem into the algebraic spaces and
pulling its solution back along the formally étale charts.

The source asks the map `Spec R' ⟶ Y` to be of finite type; with that condition the
equivalence is false, by
`AlgebraicGeometry.Space.not_forall_isSmooth_iff_liftsAgainstFiniteTypeSmallExtensions`, so
here the map is asked only to be locally of finite type. See the module documentation. -/
@[stacks 0APP "corrected form: the test morphism Spec R' ⟶ Y is required to be locally of finite
type. With it of finite type, as in the source, the statement is false:
not_forall_isSmooth_iff_liftsAgainstFiniteTypeSmallExtensions", sga "1 III 3.1" "(iii), (iii)⇒(i)"]
theorem isSmooth_iff_forall_exists_lift_isSmallExtension
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hFiniteType : IsLocallyOfFiniteType B S hS f) :
    IsSmooth B S hS f ↔
      ∀ ⦃R' R : CommRingCat.{u}⦄ (φ : R' ⟶ R),
        InfinitesimalLifting.IsSmallExtension φ →
        ∀ (T T' : BigFppfOver B S hS) (i : T ⟶ T')
          (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
          (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R'),
          (BigFppfOver.toScheme B S hS).map i = e.hom ≫ Spec.map φ ≫ e'.inv →
          ∀ (α : yoneda.obj T ⟶ X) (β : yoneda.obj T' ⟶ Y),
            IsLocallyOfFiniteType B S hS β →
            α ≫ f = yoneda.map i ≫ β →
            ∃ γ : yoneda.obj T' ⟶ X, yoneda.map i ≫ γ = α ∧ γ ≫ f = β := by
  constructor
  · intro hsm R' R φ hφ T T' i e e' hi α β _ hcomm
    exact IsSmooth.exists_lift_of_isSquareZeroSurjection B S hS hX hY hsm φ
      (InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection φ hφ) i e e' hi α β hcomm
  · intro hlift U V a b h ha hb hchart
    let F := BigFppfOver.toScheme B S hS
    have hV : IsLocallyNoetherian (F.obj V) :=
      (exists_atlas_iff_forall_etale B S hS Y
        (fun Z : Scheme.{u} => IsLocallyNoetherian Z) hY).mp hNoeth V b hb
    have hh : LocallyOfFiniteType (F.map h) := hFiniteType U V a b h ha hb hchart
    apply (AlgebraicGeometry.smooth_iff_lifts_finiteType_smallExtensions (F.map h)).mpr
    exact fun _ _ φ hφ α β hβ hcomm => exists_lift_chart_of_forall_exists_lift B S hS hY f
      hlift a b h ha hb hchart φ hφ α β hβ hcomm

end AlgebraicGeometry.Space

end
