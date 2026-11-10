module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerGluing
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Basic

/-!
# Open immersions and the small crystalline site

Let `X' ⊆ X` and `S' ⊆ S` be open subschemes with `X'` mapping into `S'`.  A divided power
thickening `(U, T, δ)` of `X'` relative to `(S', I', γ')` is one of `X` relative to `(S, I, γ)`,
and if `U ⟶ X'` is an open immersion then so is `U ⟶ X' ⟶ X`; so change of divided power base
restricts to a functor `Cris(X'/S') ⥤ Cris(X/S)` between the small crystalline sites.  This
functor is fully faithful, because the two morphisms `S' ⟶ S` and `X' ⟶ X` are monomorphisms and
a morphism of thickenings is determined by its two components; and it is cocontinuous, so it
induces a morphism of crystalline topoi `(X'/S')_cris ⟶ (X/S)_cris`.

An open subscheme of `X` is the same thing as a global crystalline situation together with an
open immersion into the given one, so the hypotheses here are those of change of base
[Stacks, Tag 07IC] with the two structure morphisms open immersions.

The cocontinuity argument is the one of [Stacks, Tag 07IC], carried out on the full
subcategories: a covering sieve of an object `B` of `Cris(X/S)` pulled back along a morphism `p`
out of the image of `A` is refined by the restrictions of `A` to the opens `p⁻¹(Tᵢ)` of its
ambient scheme, where `{Tᵢ ⟶ T_B}` is a Zariski covering family refining the sieve.  Those
restrictions are again objects of `Cris(X'/S')`, because the structure map of a restriction is the
structure map of the original object precomposed with an open immersion.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.restrictOpen` — the restriction of
  an object of `Cris(X/S)` to an open of its ambient scheme, with its structure morphism
  `CrystallineThickening.restrictOpenHom` and the family
  `CrystallineThickening.restrictOpenCover`.
* `Crystalline.GlobalCrystallineSituation.changeBaseRestrictOpenHom` — the comparison morphism
  between restricting after change of base and before.
* `Crystalline.GlobalCrystallineSituation.smallChangeBase` — the functor
  `Cris(X'/S') ⥤ Cris(X/S)` of [Stacks, Tag 07KL], and
  `smallChangeBaseFullyFaithful` the statement that it is fully faithful.
* `Crystalline.GlobalCrystallineSituation.smallChangeBaseMorphism` — the morphism of crystalline
  topoi `(X'/S')_cris ⟶ (X/S)_cris` of [Stacks, Tag 07KL].
* `Crystalline.GlobalCrystallineSituation.smallChangeBaseFullyFaithfulOfMono` and
  `smallChangeBaseFullyFaithfulOfIsClosedImmersion` — change of base exhibits `Cris(X/S')` as a
  full subcategory of `Cris(X/S)` already when the morphism of divided power bases is a
  monomorphism, in particular when it is a closed immersion.
* `Crystalline.GlobalCrystallineSituation.changeBaseDescend` — an object of `CRIS(X/S)` whose
  structure map lands in `X'` read as an object of `CRIS(X'/S')`, with
  `changeBaseDescendIso` the identification of its image with the object it came from, and
  `smallChangeBaseDescend` the same on the small crystalline categories.

## Main results

* `Crystalline.GlobalCrystallineSituation.changeBase_full` — change of divided power base is full
  as soon as the two structure morphisms are monomorphisms.
* `Crystalline.GlobalCrystallineSituation.smallChangeBase_full_of_mono` — the same for the small
  crystalline sites.
* `Crystalline.GlobalCrystallineSituation.Thickening.isCrystalline_restrictOpen` — a restriction
  of an object of the small crystalline category to an open of its ambient scheme is again one.
* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.isZariskiCovering_restrictOpenCover`
  — the restrictions of an object of `Cris(X/S)` to a family of opens covering its ambient scheme
  form a Zariski covering family.
* `Crystalline.GlobalCrystallineSituation.smallChangeBase_isCocontinuous` — the functor
  `Cris(X'/S') ⥤ Cris(X/S)` is cocontinuous for the Zariski topologies of the small crystalline
  sites, [Stacks, Tag 07KL].
* `Crystalline.GlobalCrystallineSituation.smallChangeBase_essImage_iff` — when `S' ⟶ S` carries
  the induced divided power structure, an object of `Cris(X/S)` is in the essential image of
  change of base exactly when its structure map to `X` factors through `X'`.

## Implementation notes

Change of base leaves the underlying divided power thickening untouched and composes the two
structure morphisms, so it commutes with restriction to an open only up to associativity;
`changeBaseRestrictOpenHom` is the resulting comparison morphism, whose two components are
identities, and `changeBaseRestrictOpenHom_restrictOpenHom` is the commutation it witnesses.  It
plays the role that `Crystalline.GlobalCrystallineSituation.Thickening.ofSquareComparison` plays
for the big site.

The two assertions of [Stacks, Tag 07KL] about the Zariski topoi are not covered here, being
statements about `u_{X/S}` — which is
`Crystalline.GlobalCrystallineSituation.zariskiToposMorphism` of [Stacks, Tag 07IL], in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ZariskiToposMorphism.lean`.  That the square
formed with `u_{X'/S'}` and `u_{X/S}` commutes is
`Crystalline.GlobalCrystallineSituation.smallChangeBaseZariskiSquare`, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ChangeBaseZariski.lean`; that it realizes
the localization of a morphism of topoi of [Stacks, Tag 04H1] at the sheaf represented by `X'` is
`Crystalline.GlobalCrystallineSituation.smallChangeBaseLocalizationSquare`, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobjectLocalization.lean`, together
with the two slice equivalences of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobjectSlice.lean`.
`essImage` above is
one of the inputs it needs: the site of elements of `u_{X/S}⁻¹h_{X'}^#` is the full subcategory of
`Cris(X/S)` on the objects whose structure map lands in `X'`, so the localization statement asks
for change of base to be an equivalence onto it, which is full faithfulness together with
`smallChangeBase_essImage_iff`.  Note the hypothesis that the latter needs and the rest of this
file does not: at the bare generality of `smallChangeBase` the essential image is *smaller* than
that subcategory, since an object lying over `X'` acquires a map to `S'` of divided power schemes
only when the divided power structure of `S'` is induced from that of `S`.

## References

* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 04H1](https://stacks.math.columbia.edu/tag/04H1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Crystalline.DividedPowerScheme

/-- **A morphism of divided power schemes whose underlying morphism of schemes is a monomorphism
is a monomorphism.**  A morphism of divided power schemes is determined by the underlying
morphism of schemes. -/
theorem mono_of_mono_hom {X Y : DividedPowerScheme.{u}} {φ : X ⟶ Y} (hφ : Mono φ.hom) : Mono φ where
  right_cancellation a b e := by
    refine Hom.ext (hφ.right_cancellation _ _ ?_)
    have e' := congrArg Hom.hom e
    rwa [Hom.comp_hom, Hom.comp_hom] at e'

end Crystalline.DividedPowerScheme

namespace Crystalline.GlobalCrystallineSituation

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}

/-- **Change of divided power base is faithful.**  A morphism of divided power thickenings is
determined by its two components, which change of base leaves untouched. -/
instance changeBase_faithful : (changeBase S S' f g h).Faithful where
  map_injective e := Thickening.Hom.ext (congrArg (·.sourceHom) e) (congrArg (·.targetHom) e)

/-- **Change of divided power base is full when the two structure morphisms are
monomorphisms.**  A morphism between the images of `A` and `B` has the two components of a
morphism `A ⟶ B`, and its compatibilities with the structure morphisms are the required ones
composed with `f` and with `g`. -/
theorem changeBase_full (hf : Mono f) (hg : Mono g) : (changeBase S S' f g h).Full where
  map_surjective k :=
    ⟨{ sourceHom := k.sourceHom
       targetHom := k.targetHom
       immersion_naturality := k.immersion_naturality
       base_naturality :=
         hf.right_cancellation _ _ ((Category.assoc _ _ _).trans k.base_naturality)
       toX_naturality :=
         hg.right_cancellation _ _ ((Category.assoc _ _ _).trans k.toX_naturality) }, rfl⟩

/-- **The comparison morphism between restricting after change of base and before.**  Change of
base composes the structure morphisms of an object with `f` and `g` and leaves the underlying
thickening untouched, so the two objects differ only by the bracketing of those composites; the
comparison is the identity on the underlying thickening. -/
noncomputable def changeBaseRestrictOpenHom (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) :
    (changeBase S S' f g h).obj (A.restrictOpen V) ⟶
      ((changeBase S S' f g h).obj A).restrictOpen V where
  sourceHom := 𝟙 _
  targetHom := 𝟙 _
  immersion_naturality := (Category.comp_id _).trans (Category.id_comp _).symm
  base_naturality := (Category.id_comp _).trans (Category.assoc _ _ _).symm
  toX_naturality := (Category.id_comp _).trans (Category.assoc _ _ _).symm

/-- Restricting after change of base and before agree on the structure morphisms, through the
comparison of `Crystalline.GlobalCrystallineSituation.changeBaseRestrictOpenHom`. -/
@[reassoc]
theorem changeBaseRestrictOpenHom_restrictOpenHom (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) :
    changeBaseRestrictOpenHom (f := f) (g := g) (h := h) A V ≫
        ((changeBase S S' f g h).obj A).restrictOpenHom V =
      (changeBase S S' f g h).map (A.restrictOpenHom V) :=
  Thickening.Hom.ext (Category.id_comp _) (Category.id_comp _)

namespace Thickening

/-- **A restriction of an object of the small crystalline category is again one.**  The structure
map of the restriction of `A` to an open `V` is the one of `A` precomposed with the open immersion
of the preimage of `V`. -/
theorem isCrystalline_restrictOpen {A : Thickening S} (hA : IsCrystalline A)
    (V : A.thickening.target.scheme.Opens) : IsCrystalline (A.restrictOpen V) :=
  have := hA
  inferInstanceAs (IsOpenImmersion ((A.thickening.immersion ⁻¹ᵁ V).ι ≫ A.toX))

end Thickening

namespace CrystallineThickening

/-- **The restriction of an object of `Cris(X/S)` to an open of its ambient scheme.**  The
underlying object of the big crystalline category is restricted to that open. -/
noncomputable def restrictOpen (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens) : CrystallineThickening S :=
  ⟨A.obj.restrictOpen V, Thickening.isCrystalline_restrictOpen A.property V⟩

/-- The underlying object of the big crystalline category of the restriction of `A` to `V` is
the restriction of the underlying object of `A` to `V`. -/
@[simp]
theorem restrictOpen_obj (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens) :
    (A.restrictOpen V).obj = A.obj.restrictOpen V := rfl

/-- The structure morphism of the restriction of an object of `Cris(X/S)` to an open of its
ambient scheme, given by the open immersion of that open and the open immersion of its
preimage. -/
noncomputable def restrictOpenHom (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens) : A.restrictOpen V ⟶ A :=
  ObjectProperty.homMk (A.obj.restrictOpenHom V)

/-- The underlying morphism of the structure morphism of the restriction of `A` to `V` is the
structure morphism of the restriction of the underlying object of `A` to `V`. -/
@[simp]
theorem restrictOpenHom_hom (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens) :
    (A.restrictOpenHom V).hom = A.obj.restrictOpenHom V := rfl

/-- The family of restrictions of an object of `Cris(X/S)` to a family of opens of its ambient
scheme. -/
noncomputable def restrictOpenCover (A : CrystallineThickening S) {ι : Type (u + 1)}
    (V : ι → A.obj.thickening.target.scheme.Opens) : PreZeroHypercover.{u + 1} A where
  I₀ := ι
  X i := A.restrictOpen (V i)
  f i := A.restrictOpenHom (V i)

/-- **The restrictions of an object of `Cris(X/S)` to a family of opens covering its ambient
scheme form a Zariski covering family.**  Its image in the big crystalline category is the
corresponding family of restrictions of the underlying object. -/
theorem isZariskiCovering_restrictOpenCover (A : CrystallineThickening S) {ι : Type (u + 1)}
    (V : ι → A.obj.thickening.target.scheme.Opens)
    (hV : ∀ x : A.obj.thickening.target.scheme, ∃ i, x ∈ V i) :
    IsZariskiCovering (A.restrictOpenCover V) :=
  Thickening.isZariskiCovering_restrictOpenCover A.obj V hV

end CrystallineThickening

/-- **Stacks Project, Tag 07KL.**  Let `X' ⊆ X` and `S' ⊆ S` be open subschemes with `X'` mapping
into `S'`.  A divided power thickening of `X'` relative to `(S', I', γ')` whose structure map to
`X'` is an open immersion is one of `X` relative to `(S, I, γ)` whose structure map to `X` is an
open immersion; this is the functor `Cris(X'/S') ⥤ Cris(X/S)` cut out by change of divided power
base. -/
@[stacks 07KL "the functor Cris(X'/S') ⥤ Cris(X/S)"]
noncomputable def smallChangeBase (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    CrystallineThickening S ⥤ CrystallineThickening S' :=
  (Thickening.IsCrystalline (S := S')).lift
    (CrystallineThickening.ι S ⋙ changeBase S S' f g h) fun A ↦
      have := A.property
      inferInstanceAs (IsOpenImmersion (A.obj.toX ≫ g))

variable [IsOpenImmersion g]

/-- The underlying object of the image of `A` under `smallChangeBase` is the image of the
underlying object of `A` under `changeBase`. -/
@[simp]
theorem smallChangeBase_obj_obj (A : CrystallineThickening S) :
    ((smallChangeBase S S' f g h).obj A).obj = (changeBase S S' f g h).obj A.obj := rfl

/-- The underlying morphism of the image of `k` under `smallChangeBase` is the image of the
underlying morphism of `k` under `changeBase`. -/
@[simp]
theorem smallChangeBase_map_hom {A B : CrystallineThickening S} (k : A ⟶ B) :
    ((smallChangeBase S S' f g h).map k).hom = (changeBase S S' f g h).map k.hom := rfl

/-- The functor `Cris(X'/S') ⥤ Cris(X/S)` is faithful, change of divided power base being
faithful. -/
instance smallChangeBase_faithful : (smallChangeBase S S' f g h).Faithful :=
  inferInstanceAs ((Thickening.IsCrystalline (S := S')).lift
    (CrystallineThickening.ι S ⋙ changeBase S S' f g h) _).Faithful

/-- The functor `Cris(X'/S') ⥤ Cris(X/S)` is full: change of divided power base is full because
the two structure morphisms are open immersions, hence monomorphisms, and the inclusion of a full
subcategory is full. -/
instance smallChangeBase_full [IsOpenImmersion f.hom] : (smallChangeBase S S' f g h).Full :=
  have := changeBase_full (f := f) (g := g) (h := h)
    (DividedPowerScheme.mono_of_mono_hom inferInstance) inferInstance
  inferInstanceAs ((Thickening.IsCrystalline (S := S')).lift
    (CrystallineThickening.ι S ⋙ changeBase S S' f g h) _).Full

/-- **Stacks Project, Tag 07KL.**  The functor `Cris(X'/S') ⥤ Cris(X/S)` induced by open
immersions `X' ⊆ X` and `S' ⊆ S` is fully faithful. -/
@[stacks 07KL "the functor is fully faithful"]
noncomputable def smallChangeBaseFullyFaithful [IsOpenImmersion f.hom] :
    (smallChangeBase S S' f g h).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- **Cover lifting for the functor `Cris(X'/S') ⥤ Cris(X/S)`, for a sieve refined by a family of
restrictions.**  If a sieve on the image of `A` contains the images of the restrictions of `A` to
a family of opens covering its ambient scheme, then its pullback is a covering sieve of `A` in the
small crystalline site of `X'/S'`. -/
theorem smallChangeBase_functorPullback_mem_smallTopology {A : CrystallineThickening S}
    {T : Sieve ((smallChangeBase S S' f g h).obj A)} {ι : Type (u + 1)}
    (V : ι → A.obj.thickening.target.scheme.Opens)
    (hV : ∀ x : A.obj.thickening.target.scheme, ∃ i, x ∈ V i)
    (hVT : ∀ i, T.arrows ((smallChangeBase S S' f g h).map (A.restrictOpenHom (V i)))) :
    Sieve.functorPullback (smallChangeBase S S' f g h) T ∈ smallTopology S A := by
  refine (smallTopology S).superset_covering ?_
    (smallZariskiCovering_mem_smallTopology S (A.restrictOpenCover V)
      (CrystallineThickening.isZariskiCovering_restrictOpenCover A V hV))
  rw [Sieve.generate_le_iff]
  rintro W m ⟨i⟩
  exact hVT i

/-- **Cover lifting for the functor `Cris(X'/S') ⥤ Cris(X/S)`.**  Let `{Bᵢ ⟶ B}` be a Zariski
covering family in `Cris(X/S)` and let `p` be a morphism from the image of `A` to `B`.  The
restrictions of `A` to the opens `p⁻¹(Tᵢ)` of its ambient scheme form a Zariski covering family of
`A` in `Cris(X'/S')`, and each member factors through `Bᵢ`; so the pullback along `p` of the sieve
generated by the family pulls back to a covering sieve of `A`. -/
theorem smallChangeBase_functorPullback_pullback_mem_smallTopology
    {A : CrystallineThickening S} {B : CrystallineThickening S'}
    (p : (smallChangeBase S S' f g h).obj A ⟶ B) (E : PreZeroHypercover.{u + 1} B)
    (hE : CrystallineThickening.IsZariskiCovering E) :
    Sieve.functorPullback (smallChangeBase S S' f g h)
      ((Sieve.generate E.presieve₀).pullback p) ∈ smallTopology S A := by
  have hcart : ∀ i, Thickening.IsCartesian (E.f i).hom := hE.1
  have hE2 := hE.2
  simp only [Thickening.targetPresieve, Scheme.ofArrows_mem_precoverage_iff] at hE2
  have hsurj : ∀ x : B.obj.thickening.target.scheme,
      ∃ i, ∃ y, (E.f i).hom.targetHom.hom.base y = x := hE2.1
  have hoi : ∀ i, IsOpenImmersion (E.f i).hom.targetHom.hom := hE2.2
  refine smallChangeBase_functorPullback_mem_smallTopology
    (fun i ↦ Thickening.pullbackOpen (D := (changeBase S S' f g h).obj A.obj)
      (E.f i).hom p.hom) (fun x ↦ ?_) fun i ↦ ?_
  · obtain ⟨i, y, hy⟩ := hsurj (p.hom.targetHom.hom.base x)
    exact ⟨i, y, hy⟩
  · have : IsOpenImmersion (E.f i).hom.targetHom.hom := hoi i
    have hfac : (smallChangeBase S S' f g h).map (A.restrictOpenHom
          (Thickening.pullbackOpen (D := (changeBase S S' f g h).obj A.obj)
            (E.f i).hom p.hom)) ≫ p =
        ObjectProperty.homMk (changeBaseRestrictOpenHom (f := f) (g := g) (h := h) A.obj
          (Thickening.pullbackOpen (D := (changeBase S S' f g h).obj A.obj) (E.f i).hom p.hom) ≫
            Thickening.pullbackLiftHom (D := (changeBase S S' f g h).obj A.obj)
              (E.f i).hom p.hom (hcart i)) ≫ E.f i :=
      ObjectProperty.hom_ext (Thickening.IsCrystalline (S := S'))
        (((congrArg (fun m ↦ m ≫ p.hom)
              (changeBaseRestrictOpenHom_restrictOpenHom (f := f) (g := g) (h := h) A.obj
                (Thickening.pullbackOpen (D := (changeBase S S' f g h).obj A.obj)
                  (E.f i).hom p.hom))).symm.trans
            (Category.assoc _ _ _)).trans
          (congrArg (fun m ↦ changeBaseRestrictOpenHom (f := f) (g := g) (h := h) A.obj
              (Thickening.pullbackOpen (D := (changeBase S S' f g h).obj A.obj)
                (E.f i).hom p.hom) ≫ m)
            (Thickening.pullbackLiftHom_comp (D := (changeBase S S' f g h).obj A.obj)
              (E.f i).hom p.hom (hcart i))).symm)
    rw [Sieve.pullback_apply, hfac]
    exact Sieve.downward_closed _ (Sieve.le_generate E.presieve₀ _ _ ⟨i⟩) _

/-- **Stacks Project, Tag 07KL.**  The functor `Cris(X'/S') ⥤ Cris(X/S)` is cocontinuous for the
Zariski topologies of the small crystalline sites. -/
@[stacks 07KL "the functor is cocontinuous"]
instance smallChangeBase_isCocontinuous :
    (smallChangeBase S S' f g h).IsCocontinuous (smallTopology S) (smallTopology S') :=
  Functor.isCocontinuous_toGrothendieck _ _ _ fun A _ p R hR ↦ by
    obtain ⟨E, rfl, hE⟩ := hR
    exact smallChangeBase_functorPullback_pullback_mem_smallTopology p E hE

/-- **Stacks Project, Tag 07KL.**  The morphism of crystalline topoi
`(X'/S')_cris ⟶ (X/S)_cris` induced by open immersions `X' ⊆ X` and `S' ⊆ S`: its pushforward is
the sheaf pushforward along the cocontinuous functor `Cris(X'/S') ⥤ Cris(X/S)` and its inverse
image is the sheaf pullback, which is left exact. -/
@[stacks 07KL "the induced morphism of topoi", sga "4 III 2.3" "special case"]
noncomputable def smallChangeBaseMorphism (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    MorphismOfTopoi (smallTopos S) (smallTopos S') where
  pushforward := (smallChangeBase S S' f g h).sheafPushforwardCocontinuous
    (Type (u + 1)) (smallTopology S) (smallTopology S')
  inverseImage := (smallChangeBase S S' f g h).sheafPullbackCocontinuous
    (Type (u + 1)) (smallTopology S) (smallTopology S')
  adj := (smallChangeBase S S' f g h).sheafAdjunctionPullbackCocontinuous
    (Type (u + 1)) (smallTopology S) (smallTopology S')
  preservesFiniteLimits := inferInstance

/-- **Change of divided power base is full on the small crystalline sites as soon as the morphism
of divided power bases is a monomorphism.**  A morphism between the images of `A` and `B` has the
two components of a morphism `A ⟶ B`, and the inclusion of a full subcategory is full. -/
theorem smallChangeBase_full_of_mono (hf : Mono f) : (smallChangeBase S S' f g h).Full :=
  have := changeBase_full (f := f) (g := g) (h := h) hf inferInstance
  inferInstanceAs ((Thickening.IsCrystalline (S := S')).lift
    (CrystallineThickening.ι S ⋙ changeBase S S' f g h) _).Full

/-- **Change of divided power base along a monomorphism of divided power bases exhibits
`Cris(X/S)` as a full subcategory of `Cris(X/S')`.**  Change of base is always faithful, and it
is full because the morphism of divided power bases and the morphism of the underlying schemes
are both monomorphisms. -/
noncomputable def smallChangeBaseFullyFaithfulOfMono (hf : Mono f) :
    (smallChangeBase S S' f g h).FullyFaithful :=
  have := smallChangeBase_full_of_mono (f := f) (g := g) (h := h) hf
  Functor.FullyFaithful.ofFullyFaithful _

/-- **Change of divided power base along a closed immersion of divided power bases exhibits
`Cris(X/S)` as a full subcategory of `Cris(X/S')`.**  A closed immersion of schemes is a
monomorphism, and a morphism of divided power schemes whose underlying morphism of schemes is a
monomorphism is a monomorphism. -/
noncomputable def smallChangeBaseFullyFaithfulOfIsClosedImmersion [IsClosedImmersion f.hom] :
    (smallChangeBase S S' f g h).FullyFaithful :=
  smallChangeBaseFullyFaithfulOfMono (f := f) (g := g) (h := h)
    (DividedPowerScheme.mono_of_mono_hom inferInstance)

section EssentialImage

omit [IsOpenImmersion g] in
include h in
/-- **The ambient scheme of an object of `Cris(X/S)` lying over `X'` lies over `S'`.**  The
immersion of a divided power thickening is surjective on points, so the image of `T ⟶ S` is the
image of `U ↪ T ⟶ S`, which is the image of `U ⟶ X ⟶ S`; and if `U ⟶ X` factors through `X'`
then that image lies in the image of `S' ⟶ S`, because `X' ⟶ X ⟶ S` is `X' ⟶ S' ⟶ S`. -/
theorem range_toBase_subset_of_range_toX_subset [IsOpenImmersion g] (B : Thickening S')
    (hB : Set.range ⇑B.toX.base ⊆ Set.range ⇑g.base) :
    Set.range ⇑B.toBase.hom.base ⊆ Set.range ⇑f.hom.base := by
  rintro y ⟨t, rfl⟩
  obtain ⟨s, rfl⟩ := B.thickening.isThickening.2 t
  have key : B.toBase.hom.base (B.thickening.immersion.base s) =
      (B.toX ≫ sourceToBase S').base s := by
    rw [← Scheme.Hom.comp_apply, B.over_base]
  rw [key, ← IsOpenImmersion.lift_fac g B.toX hB, Category.assoc,
    comp_sourceToBase (h := h), ← Category.assoc]
  exact ⟨(IsOpenImmersion.lift g B.toX hB ≫ sourceToBase S).base s,
    (Scheme.Hom.comp_apply _ _ s).symm⟩

/-- **An object of `CRIS(X/S)` lying over `X'` read as one of `CRIS(X'/S')`.**  The divided power
thickening is unchanged; the map to `X` is factored through the open immersion `X' ⟶ X`, and the
map `T ⟶ S` of divided power schemes is factored through `S' ⟶ S`.  The second factorization
exists as a map of *schemes* by
`Crystalline.GlobalCrystallineSituation.range_toBase_subset_of_range_toX_subset`, and is a map of
divided power schemes by `Crystalline.DividedPowerScheme.inducedOpenLift`, which is where the
hypothesis that `S' ⟶ S` carry the induced divided power structure is used. -/
noncomputable def changeBaseDescend (hf : DividedPowerScheme.IsInducedOpen f) (B : Thickening S')
    (hB : Set.range ⇑B.toX.base ⊆ Set.range ⇑g.base) : Thickening S :=
  have := hf.isOpenImmersion
  { thickening := B.thickening
    toBase := DividedPowerScheme.inducedOpenLift f hf B.toBase
      (IsOpenImmersion.lift f.hom B.toBase.hom
        (range_toBase_subset_of_range_toX_subset (h := h) B hB))
      (IsOpenImmersion.lift_fac _ _ _)
    toX := IsOpenImmersion.lift g B.toX hB
    over_base := by
      have := hf.isOpenImmersion
      have hk : (DividedPowerScheme.inducedOpenLift f hf B.toBase
          (IsOpenImmersion.lift f.hom B.toBase.hom
            (range_toBase_subset_of_range_toX_subset (h := h) B hB))
          (IsOpenImmersion.lift_fac _ _ _)).hom ≫ f.hom = B.toBase.hom :=
        IsOpenImmersion.lift_fac _ _ _
      rw [← cancel_mono f.hom, Category.assoc, hk, B.over_base, Category.assoc,
        ← comp_sourceToBase (h := h),
        ← Category.assoc (IsOpenImmersion.lift g B.toX hB) g (sourceToBase S'),
        IsOpenImmersion.lift_fac] }

/-- The divided power thickening underlying `changeBaseDescend hf B hB` is that of `B`. -/
@[simp]
theorem changeBaseDescend_thickening (hf : DividedPowerScheme.IsInducedOpen f) (B : Thickening S')
    (hB : Set.range ⇑B.toX.base ⊆ Set.range ⇑g.base) :
    (changeBaseDescend (h := h) hf B hB).thickening = B.thickening := rfl

/-- The structure map of `changeBaseDescend hf B hB` to `X` is the lift of the structure map of
`B` through the open immersion `g`. -/
@[simp]
theorem changeBaseDescend_toX (hf : DividedPowerScheme.IsInducedOpen f) (B : Thickening S')
    (hB : Set.range ⇑B.toX.base ⊆ Set.range ⇑g.base) :
    (changeBaseDescend (h := h) hf B hB).toX = IsOpenImmersion.lift g B.toX hB := rfl

/-- The map to the smaller divided power base, composed back with `S' ⟶ S`, is the original map
to `S`; the two are equal already as morphisms of schemes, by the universal property of the open
immersion. -/
theorem changeBaseDescend_toBase_comp (hf : DividedPowerScheme.IsInducedOpen f)
    (B : Thickening S') (hB : Set.range ⇑B.toX.base ⊆ Set.range ⇑g.base) :
    (changeBaseDescend (h := h) hf B hB).toBase ≫ f = B.toBase :=
  have := hf.isOpenImmersion
  DividedPowerScheme.Hom.ext (IsOpenImmersion.lift_fac _ _ _)

/-- **Change of divided power base returns the object it was read from.**  Both components of the
comparison are identities, the underlying divided power thickening never having moved. -/
noncomputable def changeBaseDescendIso (hf : DividedPowerScheme.IsInducedOpen f)
    (B : Thickening S') (hB : Set.range ⇑B.toX.base ⊆ Set.range ⇑g.base) :
    (changeBase S S' f g h).obj (changeBaseDescend (h := h) hf B hB) ≅ B where
  hom :=
    { sourceHom := 𝟙 _
      targetHom := 𝟙 _
      immersion_naturality := by simp
      base_naturality :=
        (Category.id_comp _).trans (changeBaseDescend_toBase_comp (h := h) hf B hB).symm
      toX_naturality :=
        (Category.id_comp _).trans (IsOpenImmersion.lift_fac g B.toX hB).symm }
  inv :=
    { sourceHom := 𝟙 _
      targetHom := 𝟙 _
      immersion_naturality := by simp
      base_naturality :=
        (Category.id_comp _).trans (changeBaseDescend_toBase_comp (h := h) hf B hB)
      toX_naturality :=
        (Category.id_comp _).trans (IsOpenImmersion.lift_fac g B.toX hB) }
  hom_inv_id := by apply Thickening.Hom.ext <;> simp
  inv_hom_id := by apply Thickening.Hom.ext <;> simp

/-- The object read off over the smaller situation is again an object of the small crystalline
category: its map to `X'` is an open immersion because its composite with the open immersion
`X' ⟶ X` is the original open immersion to `X`. -/
theorem isCrystalline_changeBaseDescend (hf : DividedPowerScheme.IsInducedOpen f)
    {B : Thickening S'} (hBc : Thickening.IsCrystalline B)
    (hB : Set.range ⇑B.toX.base ⊆ Set.range ⇑g.base) :
    Thickening.IsCrystalline (changeBaseDescend (h := h) hf B hB) := by
  have : IsOpenImmersion B.toX := hBc
  change IsOpenImmersion (IsOpenImmersion.lift g B.toX hB)
  have : IsOpenImmersion (IsOpenImmersion.lift g B.toX hB ≫ g) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  exact IsOpenImmersion.of_comp _ g

/-- An object of `Cris(X/S)` lying over `X'`, read as an object of `Cris(X'/S')`. -/
noncomputable def smallChangeBaseDescend (hf : DividedPowerScheme.IsInducedOpen f)
    (B : CrystallineThickening S')
    (hB : Set.range ⇑B.obj.toX.base ⊆ Set.range ⇑g.base) : CrystallineThickening S :=
  ⟨changeBaseDescend (h := h) hf B.obj hB,
    isCrystalline_changeBaseDescend (h := h) hf B.property hB⟩

/-- **Change of divided power base hits every object of `Cris(X/S)` that lies over `X'`**, when
`S' ⟶ S` exhibits `S'` as an open divided power subscheme of `S`.  The preimage is
`Crystalline.GlobalCrystallineSituation.smallChangeBaseDescend`. -/
theorem smallChangeBase_essImage_of_range_toX_subset
    (hf : DividedPowerScheme.IsInducedOpen f) (B : CrystallineThickening S')
    (hB : Set.range ⇑B.obj.toX.base ⊆ Set.range ⇑g.base) :
    (smallChangeBase S S' f g h).essImage B :=
  ⟨smallChangeBaseDescend (h := h) hf B hB,
    ⟨(Thickening.IsCrystalline (S := S')).fullyFaithfulι.preimageIso
      (changeBaseDescendIso (h := h) hf B.obj hB)⟩⟩

/-- Everything change of divided power base hits lies over `X'`: an isomorphism of thickenings
factors the map to `X` through the map to `X` of the object it came from, which is a map to `X'`
followed by `X' ⟶ X`. -/
theorem range_toX_subset_of_smallChangeBase_essImage {B : CrystallineThickening S'}
    (hB : (smallChangeBase S S' f g h).essImage B) :
    Set.range ⇑B.obj.toX.base ⊆ Set.range ⇑g.base := by
  obtain ⟨A, ⟨e⟩⟩ := hB
  rintro y ⟨x, rfl⟩
  refine ⟨A.obj.toX.base (e.inv.hom.sourceHom.base x), ?_⟩
  calc g.base (A.obj.toX.base (e.inv.hom.sourceHom.base x))
      = ((smallChangeBase S S' f g h).obj A).obj.toX.base (e.inv.hom.sourceHom.base x) :=
        (Scheme.Hom.comp_apply A.obj.toX g _).symm
    _ = (e.inv.hom.sourceHom ≫ ((smallChangeBase S S' f g h).obj A).obj.toX).base x :=
        (Scheme.Hom.comp_apply _ _ x).symm
    _ = B.obj.toX.base x := by rw [e.inv.hom.toX_naturality]

/-- **The essential image of change of divided power base, for `S' ⟶ S` an open divided power
subscheme.**  An object of `Cris(X/S)` comes from `Cris(X'/S')` exactly when its structure map to
`X` factors through the open `X'`.  Together with
`Crystalline.GlobalCrystallineSituation.smallChangeBaseFullyFaithful` this says that change of
base identifies `Cris(X'/S')` with the full subcategory of `Cris(X/S)` on those objects, which is
the site of elements of the sheaf `u_{X/S}⁻¹h_{X'}^#`. -/
theorem smallChangeBase_essImage_iff (hf : DividedPowerScheme.IsInducedOpen f)
    (B : CrystallineThickening S') :
    (smallChangeBase S S' f g h).essImage B ↔
      Set.range ⇑B.obj.toX.base ⊆ Set.range ⇑g.base :=
  ⟨range_toX_subset_of_smallChangeBase_essImage,
    smallChangeBase_essImage_of_range_toX_subset (h := h) hf B⟩

end EssentialImage

end Crystalline.GlobalCrystallineSituation

end
