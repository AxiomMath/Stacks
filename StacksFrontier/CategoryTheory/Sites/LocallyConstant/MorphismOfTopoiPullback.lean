module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.ConstantInverseImage
public import StacksFrontier.CategoryTheory.Sites.SlicePost.MorphismOfSites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteLocallyConstant
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of a locally constant sheaf along a morphism of topoi

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi between the topoi of sheaves of sets on two
sites `(C, J)` and `(D, K)`. Tag 093R asserts that `f⁻¹` carries locally constant sheaves to
locally constant sheaves.

The inverse image of a *constant* sheaf is constant for an arbitrary morphism of topoi, by
uniqueness of left adjoints (`MorphismOfTopoi.isConstant_inverseImage`). Local constancy is
the same statement over each member of a covering, so what the passage from constant to
locally constant needs is the *localizations* of `f`: a morphism of topoi
`Sh(C/U) ⟶ Sh(D/V)` whose inverse image is the restriction of `f⁻¹`, for suitable pairs of
objects `U` of `C` and `V` of `D`. A bare adjoint pair between `Sh(C)` and `Sh(D)` carries no
such data: localizing a morphism of topoi is done at a subobject of the final sheaf, and the
comparison of the result with a sheaf category on a localized *site* is the content of
Stacks 0791 and 04GZ.

`MorphismOfTopoi.LocalizationDatum` below is exactly that missing data, isolated as a
structure: a functor `u : D ⥤ C` of sites running against `f`, carrying coverings to
coverings and some object of `D` to a final object of `C`, together with a localized morphism
of topoi `Sh(C/u V) ⟶ Sh(D/V)` for every object `V` of `D` and the commuting square
identifying its inverse image with the restriction of `f⁻¹`. Given such a datum,
`MorphismOfTopoi.isLocallyConstant_inverseImage` is Tag 093R: nothing more is needed than the
constant case applied in the localized topoi, which is why the statement asks nothing of the
coefficients beyond their being sets and nothing of the sites beyond fibre products in `C`.

The datum is not vacuous: it exists whenever `f` comes from a morphism of sites, by
`MorphismOfTopoi.LocalizationDatum.ofSheafPullback`, the square being
`Stacks.ConstantSheaf.overPullbackSheafPullbackIso`.

A morphism of topoi whose inverse image is not induced by a functor of the two sites has no
such datum to offer, and for it the tag is proved differently, in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.MorphismOfTopoiSectionRelocalization`: when
both sites are small, a section `h_V^# ⟶ f⁻¹h_Y^#` relocalizes `f` far enough to carry a
trivialization over `Y` to one over `V`, and such sections exist on a covering of every object.
That statement — `MorphismOfTopoi.isLocallyConstant_inverseImage_of_smallSites` — assumes
nothing of `f` beyond its being a morphism of topoi; the datum remains the route for sites and
coefficient universes outside the reach of the represented sheaves `h_V^#`, which is where the
section argument lives.

## Main definitions

* `MorphismOfTopoi.LocalizationDatum` — the localizations of a morphism of topoi along a
  functor of sites, with the squares comparing them to `f⁻¹`.
* `MorphismOfTopoi.LocalizationDatum.ofSheafPullback` — the datum of a morphism of topoi whose
  inverse image is the sheaf pullback along a left exact, cover-preserving functor of sites.

## Main results

* `MorphismOfTopoi.isLocallyConstant_inverseImage` — **Tag 093R** for a morphism of topoi
  equipped with a localization datum: the inverse image of a locally constant sheaf of sets is
  locally constant. For a morphism of topoi between the topoi of sheaves of sets on two *small*
  sites no datum is needed, by
  `MorphismOfTopoi.isLocallyConstant_inverseImage_of_smallSites`.
* `MorphismOfTopoi.isFiniteLocallyConstant_inverseImage` — the same for a finite locally
  constant sheaf of sets, the constant values being unchanged.
* `MorphismOfTopoi.isLocallyConstant_sheafPullback_of_morphismOfSites` — the case of a morphism
  of sites, deduced from the above through its localization datum, which is what shows the datum
  to be inhabited. It assumes no object with a final image, unlike
  `Stacks.ConstantSheaf.isLocallyConstant_sheafPullback`: left exactness of the functor of sites
  already carries a final object to a final object.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe wc w v u v' u'

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The **localizations of a morphism of topoi** `f : Sh(C) ⟶ Sh(D)` along a functor of sites.

A morphism of topoi is an adjoint pair, and carries no information about the two sites; this
structure records the data which the localization of `f` has when `f` is a morphism of sites,
and which Tag 093R consumes:

* a functor `u : D ⥤ C` running against `f`, as the functor of a morphism of sites does,
  which carries coverings to coverings;
* an object of `D` whose image under `u` is a final object of `C`, where a trivializing
  covering is to be taken;
* for every object `V` of `D` a *localized* morphism of topoi `Sh(C/u V) ⟶ Sh(D/V)`;
* the *localization square*: its inverse image is the restriction of `f⁻¹` to `u V`.

For `f` the morphism of topoi of a morphism of sites this is
`MorphismOfTopoi.LocalizationDatum.ofSheafPullback`. -/
public structure LocalizationDatum
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))) where
  /-- The functor of sites, running against `f` as in Stacks 00X1. -/
  functor : D ⥤ C
  /-- It carries coverings to coverings. -/
  coverPreserving : CoverPreserving K J functor
  /-- An object of the target site whose image is a final object of the source site. -/
  final : D
  /-- The image of `final` is a final object of the source site. -/
  isTerminal_functor_final : IsTerminal (functor.obj final)
  /-- The localization of `f` at an object `V` of the target site. -/
  localized : ∀ V : D,
    MorphismOfTopoi (Sheaf (J.over (functor.obj V)) (Type w)) (Sheaf (K.over V) (Type w))
  /-- The localization square: restricting to `u V` after `f⁻¹` is the inverse image of the
  localized morphism after restricting to `V`. -/
  square : ∀ V : D, f.inverseImage ⋙ J.overPullback (Type w) (functor.obj V) ≅
    K.overPullback (Type w) V ⋙ (localized V).inverseImage

namespace LocalizationDatum

variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]
  [∀ V : D, HasWeakSheafify (K.over V) (Type w)]
  {f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))}

/-- **A trivialization survives inverse image, with the same value.** If `G` restricted to `V`
is the constant sheaf on a set `E`, then `f⁻¹G` restricted to `u V` is the constant sheaf on
the same `E`: the restriction of `f⁻¹G` is the inverse image of the restriction of `G` along
the localization of `f` at `V`, and the inverse image of a constant sheaf of sets along a
morphism of topoi is constant with the same value. -/
public def constantIsoOverPullbackInverseImage (d : LocalizationDatum f) (V : D)
    (G : Sheaf K (Type w)) (E : Type w)
    (c : (constantSheaf (K.over V) (Type w)).obj E ≅ (K.overPullback (Type w) V).obj G) :
    (constantSheaf (J.over (d.functor.obj V)) (Type w)).obj E ≅
      (J.overPullback (Type w) (d.functor.obj V)).obj (f.inverseImage.obj G) :=
  ((d.localized V).constantSheafIso Over.mkIdTerminal Over.mkIdTerminal).symm.app E ≪≫
    (d.localized V).inverseImage.mapIso c ≪≫ ((d.square V).app G).symm

/-- The restriction of `f⁻¹G` to `u V` is constant as soon as the restriction of `G` to `V`
is. This is the `Prop`-valued form of
`MorphismOfTopoi.LocalizationDatum.constantIsoOverPullbackInverseImage`. -/
public lemma isConstant_overPullback_inverseImage (d : LocalizationDatum f) (V : D)
    (G : Sheaf K (Type w))
    [Sheaf.IsConstant (K.over V) ((K.overPullback (Type w) V).obj G)] :
    Sheaf.IsConstant (J.over (d.functor.obj V))
      ((J.overPullback (Type w) (d.functor.obj V)).obj (f.inverseImage.obj G)) := by
  obtain ⟨E, ⟨c⟩⟩ := Sheaf.mem_essImage_of_isConstant (K.over V)
    ((K.overPullback (Type w) V).obj G)
  exact ⟨E, ⟨d.constantIsoOverPullbackInverseImage V G E c⟩⟩

end LocalizationDatum

variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]
  [∀ V : D, HasWeakSheafify (K.over V) (Type w)] [HasPullbacks C]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

/-- **Tag 093R.** The inverse image of a locally constant sheaf of sets along a morphism of
topoi which is equipped with a localization datum is locally constant.

A trivializing covering of the distinguished object of the target site is carried forward by
cover preservation to a covering of a final object of the source site, which is enough for
local constancy there (`Stacks.ConstantSheaf.isLocallyConstant_of_cover`), and on a member the
restriction of `f⁻¹G` is constant by
`MorphismOfTopoi.LocalizationDatum.isConstant_overPullback_inverseImage`. -/
@[stacks 093R "locally constant sheaves of sets, for a morphism of topoi equipped with a \
  localization datum along a functor of sites"]
public lemma isLocallyConstant_inverseImage (d : LocalizationDatum f) (G : Sheaf K (Type w))
    [hG : IsLocallyConstant K G] : IsLocallyConstant J (f.inverseImage.obj G) := by
  obtain ⟨I, Y, g, hg, hc⟩ := hG.exists_cover d.final
  refine isLocallyConstant_of_cover J (Type w) d.isTerminal_functor_final _
    (sieve_ofArrows_map_mem K J d.functor d.coverPreserving hg) fun i => ?_
  have := hc i
  exact d.isConstant_overPullback_inverseImage (Y i) G

/-- **Tag 093R.** The inverse image of a *finite* locally constant sheaf of sets along a
morphism of topoi which is equipped with a localization datum is finite locally constant.

The constant values are unchanged by
`MorphismOfTopoi.LocalizationDatum.constantIsoOverPullbackInverseImage`, so their finiteness
needs no argument. -/
@[stacks 093R "finite locally constant sheaves of sets, for a morphism of topoi equipped with \
  a localization datum along a functor of sites"]
public lemma isFiniteLocallyConstant_inverseImage {FA : Type w → Type w → Type*}
    {CA : Type w → Type wc} [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)]
    [ConcreteCategory.{wc} (Type w) FA]
    (d : LocalizationDatum f) (G : Sheaf K (Type w))
    [hG : IsFiniteLocallyConstant (FD := FA) (CD := CA) K G] :
    IsFiniteLocallyConstant (FD := FA) (CD := CA) J (f.inverseImage.obj G) := by
  obtain ⟨I, Y, g, hg, hc⟩ := hG.exists_finite_cover d.final
  refine isFiniteLocallyConstant_of_cover J (Type w) d.isTerminal_functor_final _
    (sieve_ofArrows_map_mem K J d.functor d.coverPreserving hg) fun i => ?_
  obtain ⟨E, hE, ⟨c⟩⟩ := hc i
  exact ⟨E, hE, ⟨d.constantIsoOverPullbackInverseImage (Y i) G E c⟩⟩

/-! ### The localization datum of a morphism of sites -/

section OfSites

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasFiniteLimits C] [HasFiniteLimits D]

/-- **The localization datum of a morphism of sites.** Let `u : D ⥤ C` be a continuous left
exact functor between sites with finite limits — a morphism of sites `f : C → D` by
Stacks 00X6 — which carries coverings to coverings, and let `f` be a morphism of topoi whose
inverse image is `u_s`. Then `f` has a localization datum: the localized morphisms of topoi
are those of the morphisms of sites `Over.post u` (Stacks 03EF), the localization square is
`Stacks.ConstantSheaf.overPullbackSheafPullbackIso`, and the distinguished object is the final
object of `D`, whose image is final in `C` because `u` is left exact.

This is what makes `MorphismOfTopoi.isLocallyConstant_inverseImage` applicable; for the inverse
image `u_s` itself, pass `Iso.refl _`. -/
public def LocalizationDatum.ofSheafPullback
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))) (u : D ⥤ C)
    [u.IsContinuous K J] [PreservesFiniteLimits u]
    (e : f.inverseImage ≅ u.sheafPullback (Type w) K J) (hu : CoverPreserving K J u) :
    LocalizationDatum f where
  functor := u
  coverPreserving := hu
  final := ⊤_ D
  isTerminal_functor_final := IsTerminal.isTerminalObj u (⊤_ D) terminalIsTerminal
  localized V := (Functor.isMorphismOfSites_overPost K J u V).morphismOfTopoi
  square V := Functor.isoWhiskerRight e (J.overPullback (Type w) (u.obj V)) ≪≫
    overPullbackSheafPullbackIso K J (Type w) u V

/-- **Tag 093R for a morphism of sites and sheaves of sets**, as an instance of the statement
for a morphism of topoi: the inverse image of a locally constant sheaf of sets along a
continuous left exact cover-preserving functor of sites with finite limits is locally constant.

This is `Stacks.ConstantSheaf.isLocallyConstant_sheafPullback` at the coefficients `Type w`,
obtained from `MorphismOfTopoi.isLocallyConstant_inverseImage` through the localization datum
`MorphismOfTopoi.LocalizationDatum.ofSheafPullback`, and it is what shows that datum to be
inhabited. No object with a final image is assumed: left exactness of `u` already carries the
final object of `D` to a final object of `C`. -/
public lemma isLocallyConstant_sheafPullback_of_morphismOfSites (u : D ⥤ C) [u.IsContinuous K J]
    [PreservesFiniteLimits u] (hu : CoverPreserving K J u)
    (G : Sheaf K (Type w)) [IsLocallyConstant K G] :
    IsLocallyConstant J ((u.sheafPullback (Type w) K J).obj G) :=
  (Functor.isMorphismOfSites_of_preservesFiniteLimits u K J).morphismOfTopoi
    |>.isLocallyConstant_inverseImage
      (LocalizationDatum.ofSheafPullback _ u (Iso.refl _) hu) G

end OfSites

end MorphismOfTopoi

end
