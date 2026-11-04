module

public import StacksFrontier.AlgebraicGeometry.Groupoids.CechDescentInvariantOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.MonoSubgroupoid

/-!
# The groupoid scheme carried by an invariant open of the object scheme

Let `G` be a groupoid scheme over `S` with object scheme `U` and arrow scheme `R`, and let
`V ⊆ U` be an open which is *invariant*: every arrow whose source lies in `V` has its target
there too.  Equivalently `s⁻¹(V) = t⁻¹(V)`.  Then `V`, together with the open `s⁻¹(V)` of `R`,
is again a groupoid scheme over `S`, and its inclusion into `G` is a morphism of groupoid
schemes. Its structure morphisms are those of `G` restricted along open immersions, so the two
maps on object and arrow schemes are open immersions with open ranges `V` and `s⁻¹(V)`. For an
invariant clopen decomposition of the object scheme, the open ranges of the two halves are
complementary.

## Main definitions

* `Stacks.Groupoids.openOver`, `Stacks.Groupoids.openOverι` and
  `Stacks.Groupoids.openOverLift` read an open subscheme of the underlying scheme of an object of
  `CategoryTheory.Over S` as an object of `CategoryTheory.Over S`, with its open immersion and
  the universal property of that immersion.
* `Stacks.Groupoids.invariantArrows` is the open `s⁻¹(V)` of the arrow scheme.
* `Stacks.Groupoids.invariantOpenSubgroupoid` is **the subgroupoid presentation** carried by an
  invariant open, in the sense of `Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid`.
* `Stacks.Groupoids.restrictInvariantOpen` is **the groupoid scheme** it presents and
  `Stacks.Groupoids.restrictInvariantOpenHom` **the morphism of groupoid schemes** into `G`.

## Main results

* `Stacks.Groupoids.opensRange_restrictInvariantOpenHom_mapObjects` and
  `Stacks.Groupoids.opensRange_restrictInvariantOpenHom_mapArrows`: the open ranges of the two
  maps are `V` and `s⁻¹(V)`.
* `Stacks.Groupoids.isInvariantOpen_of_isCompl`: the complement of an invariant open in an
  invariant clopen decomposition is again invariant, so one invariance hypothesis suffices for
  both halves.
* `Stacks.Groupoids.isCompl_opensRange_mapObjects` and
  `Stacks.Groupoids.isCompl_opensRange_mapArrows`: for an invariant clopen decomposition of the
  object scheme the two maps on object schemes, and the two maps on arrow schemes, have
  complementary open ranges.

## Implementation notes

Invariance is `Stacks.Groupoids.IsInvariantOpen`, the pointwise condition that an arrow starting
in `V` ends in `V`. By `Stacks.Groupoids.isInvariantOpen_iff_preimage_eq` this is the equality
`s⁻¹(V) = t⁻¹(V)` of scheme-theoretic inverse images; it makes `s⁻¹(V)` stable under the inverse
morphism, and lets the target morphism of `G` restrict to `s⁻¹(V) ⟶ V`.

Each restricted structure morphism is produced by the universal property of the open immersion
`V.ι` or `(s⁻¹ V).ι`, not by transport along the equality of opens, so the construction is free
of `eqToHom`. The five compatibility equations of
`Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid` are then instances of
`Stacks.Groupoids.openOverLift_comp_openOverι`, the factorisation property of that lift.

## References

* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
* [Stacks Project, Tag 03LO](https://stacks.math.columbia.edu/tag/03LO)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Groupoids

/-! ### Open subschemes of an object of the over category -/

section OpenOver

variable {S : Scheme.{u}}

/-- A morphism of schemes whose image lies in an open subscheme of its target has its range
inside the range of the immersion of that open. -/
theorem range_subset_range_ι {X Y : Scheme.{u}} (B : Y.Opens) (g : X ⟶ Y)
    (h : ∀ x, g.base x ∈ B) : Set.range ⇑g ⊆ Set.range ⇑B.ι := by
  rw [Scheme.Opens.range_ι]
  rintro y ⟨x, rfl⟩
  exact h x

/-- A morphism of schemes which factors through the immersion of an open subscheme takes every
point into that open. -/
theorem mem_of_eq_comp_ι {X Y : Scheme.{u}} {C : Y.Opens} {f : X ⟶ Y} (k : X ⟶ C.toScheme)
    (h : f = k ≫ C.ι) (x : X) : f.base x ∈ C := by
  subst h
  exact (k.base x).2

/-- An open subscheme of the underlying scheme of an object of `Over S`, read again as an object
of `Over S`. -/
abbrev openOver (X : Over S) (B : X.left.Opens) : Over S := Over.mk (B.ι ≫ X.hom)

/-- The open immersion of an open subobject into the object it came from. -/
def openOverι (X : Over S) (B : X.left.Opens) : openOver X B ⟶ X := Over.homMk B.ι

/-- The underlying morphism of schemes of `openOverι X B` is the open immersion `B.ι`. -/
@[simp]
theorem openOverι_left (X : Over S) (B : X.left.Opens) : (openOverι X B).left = B.ι := rfl

/-- The underlying morphism of schemes of `openOverι X B` is an open immersion. -/
instance isOpenImmersion_openOverι_left (X : Over S) (B : X.left.Opens) :
    IsOpenImmersion (openOverι X B).left := by
  rw [openOverι_left]
  infer_instance

/-- The inclusion `openOverι X B` of an open subobject is a monomorphism in `Over S`. -/
instance mono_openOverι (X : Over S) (B : X.left.Opens) : Mono (openOverι X B) :=
  Over.mono_of_mono_left _

/-- The open range of the underlying morphism of `openOverι X B` is `B`. -/
@[simp]
theorem opensRange_openOverι_left (X : Over S) (B : X.left.Opens) :
    (openOverι X B).left.opensRange = B := Scheme.Opens.opensRange_ι B

/-- The morphism of schemes produced by the universal property of the open immersion of an open
subscheme, for a morphism of `Over S` taking every point into that open. -/
def openOverLiftLeft {X Y : Over S} (f : X ⟶ Y) (B : Y.left.Opens)
    (h : ∀ x, f.left.base x ∈ B) : X.left ⟶ B.toScheme :=
  IsOpenImmersion.lift B.ι f.left (range_subset_range_ι B f.left h)

/-- `openOverLiftLeft f B h` followed by the immersion `B.ι` is the underlying morphism of `f`. -/
@[reassoc (attr := simp)]
theorem openOverLiftLeft_comp_ι {X Y : Over S} (f : X ⟶ Y) (B : Y.left.Opens)
    (h : ∀ x, f.left.base x ∈ B) : openOverLiftLeft f B h ≫ B.ι = f.left :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The universal property of an open subobject.**  A morphism of `Over S` whose underlying
morphism of schemes takes every point into an open subscheme of its target factors through that
open. -/
def openOverLift {X Y : Over S} (f : X ⟶ Y) (B : Y.left.Opens)
    (h : ∀ x, f.left.base x ∈ B) : X ⟶ openOver Y B :=
  Over.homMk (openOverLiftLeft f B h) (by
    rw [show (openOver Y B).hom = B.ι ≫ Y.hom from rfl, ← Category.assoc,
      openOverLiftLeft_comp_ι]
    exact Over.w f)

/-- The underlying morphism of schemes of `openOverLift f B h` is `openOverLiftLeft f B h`. -/
@[simp]
theorem openOverLift_left {X Y : Over S} (f : X ⟶ Y) (B : Y.left.Opens)
    (h : ∀ x, f.left.base x ∈ B) : (openOverLift f B h).left = openOverLiftLeft f B h := rfl

/-- The underlying morphism of `openOverLift f B h` followed by the immersion `B.ι` is the
underlying morphism of `f`. -/
@[reassoc (attr := simp)]
theorem openOverLift_left_comp_ι {X Y : Over S} (f : X ⟶ Y) (B : Y.left.Opens)
    (h : ∀ x, f.left.base x ∈ B) : (openOverLift f B h).left ≫ B.ι = f.left :=
  openOverLiftLeft_comp_ι f B h

/-- The factorisation of `Stacks.Groupoids.openOverLift`, in `Over S`. -/
@[simp]
theorem openOverLift_comp_openOverι {X Y : Over S} (f : X ⟶ Y) (B : Y.left.Opens)
    (h : ∀ x, f.left.base x ∈ B) : openOverLift f B h ≫ openOverι Y B = f :=
  Over.OverMorphism.ext (by rw [Over.comp_left, openOverι_left, openOverLift_left_comp_ι])

end OpenOver

/-! ### The arrow scheme of an invariant open -/

section InvariantOpen

variable {S : Scheme.{u}} (G : GroupoidScheme S) (V : G.objects.left.Opens)

/-- The open subscheme of the arrow scheme consisting of the arrows whose source lies in a given
open of the object scheme. -/
abbrev invariantArrows : G.arrows.left.Opens := G.source.left ⁻¹ᵁ V

/-- An arrow lies in `s⁻¹(V)` exactly when its source lies in `V`. -/
theorem mem_invariantArrows_iff (r : G.arrows.left) :
    r ∈ invariantArrows G V ↔ G.source.left.base r ∈ V := Iff.rfl

/-- For an invariant open `V`, an arrow lies in `s⁻¹(V)` exactly when its target lies in `V`. -/
theorem mem_invariantArrows_iff_target (hV : IsInvariantOpen G V) (r : G.arrows.left) :
    r ∈ invariantArrows G V ↔ G.target.left.base r ∈ V := by
  rw [mem_invariantArrows_iff]
  refine ⟨fun hr => hV r hr, fun hr => ?_⟩
  simpa [target_inverse_apply G] using
    hV (G.inverse.left.base r) (by simpa [source_inverse_apply G] using hr)

/-! ### The restricted structure morphisms -/

/-- The source morphism restricted to an open of the object scheme and its arrows. -/
def invariantSource : openOver G.arrows (invariantArrows G V) ⟶ openOver G.objects V :=
  openOverLift (openOverι G.arrows (invariantArrows G V) ≫ G.source) V fun x => x.2

/-- The target morphism restricted to an invariant open of the object scheme and its arrows. -/
def invariantTarget (hV : IsInvariantOpen G V) :
    openOver G.arrows (invariantArrows G V) ⟶ openOver G.objects V :=
  openOverLift (openOverι G.arrows (invariantArrows G V) ≫ G.target) V fun x => hV _ x.2

/-- The identity morphism restricted to an open of the object scheme and its arrows. -/
def invariantIdentity : openOver G.objects V ⟶ openOver G.arrows (invariantArrows G V) :=
  openOverLift (openOverι G.objects V ≫ G.identity) (invariantArrows G V) (by
    intro x
    change G.source.left.base (G.identity.left.base (V.ι.base x)) ∈ V
    rw [← Scheme.Hom.comp_apply, identity_left_comp_source_left G]
    exact x.2)

/-- The inverse morphism restricted to an invariant open of the object scheme and its arrows. -/
def invariantInverse (hV : IsInvariantOpen G V) :
    openOver G.arrows (invariantArrows G V) ⟶ openOver G.arrows (invariantArrows G V) :=
  openOverLift (openOverι G.arrows (invariantArrows G V) ≫ G.inverse) (invariantArrows G V) (by
    intro x
    change G.source.left.base (G.inverse.left.base ((invariantArrows G V).ι.base x)) ∈ V
    rw [source_inverse_apply G]
    exact hV _ x.2)

/-- The restricted source morphism is compatible with the source morphism of `G` along the two
open immersions. -/
@[simp]
theorem invariantSource_ι :
    invariantSource G V ≫ openOverι G.objects V =
      openOverι G.arrows (invariantArrows G V) ≫ G.source :=
  openOverLift_comp_openOverι _ _ _

/-- The restricted target morphism is compatible with the target morphism of `G` along the two
open immersions. -/
@[simp]
theorem invariantTarget_ι (hV : IsInvariantOpen G V) :
    invariantTarget G V hV ≫ openOverι G.objects V =
      openOverι G.arrows (invariantArrows G V) ≫ G.target :=
  openOverLift_comp_openOverι _ _ _

/-- The restricted identity morphism is compatible with the identity morphism of `G` along the
two open immersions. -/
@[simp]
theorem invariantIdentity_ι :
    invariantIdentity G V ≫ openOverι G.arrows (invariantArrows G V) =
      openOverι G.objects V ≫ G.identity :=
  openOverLift_comp_openOverι _ _ _

/-- The restricted inverse morphism is compatible with the inverse morphism of `G` along the
open immersion of `s⁻¹(V)`. -/
@[simp]
theorem invariantInverse_ι (hV : IsInvariantOpen G V) :
    invariantInverse G V hV ≫ openOverι G.arrows (invariantArrows G V) =
      openOverι G.arrows (invariantArrows G V) ≫ G.inverse :=
  openOverLift_comp_openOverι _ _ _

/-! ### The restricted composition morphism -/

/-- The comparison of the schemes of composable arrows. -/
def invariantComposables (hV : IsInvariantOpen G V) :
    pullback (invariantSource G V) (invariantTarget G V hV) ⟶ pullback G.source G.target :=
  pullback.map _ _ _ _ (openOverι G.arrows (invariantArrows G V))
    (openOverι G.arrows (invariantArrows G V)) (openOverι G.objects V)
    (invariantSource_ι G V) (invariantTarget_ι G V hV)

/-- The comparison `invariantComposables` is compatible with the second projections along the
open immersion of `s⁻¹(V)`. -/
theorem invariantComposables_snd (hV : IsInvariantOpen G V) :
    invariantComposables G V hV ≫ pullback.snd G.source G.target =
      pullback.snd (invariantSource G V) (invariantTarget G V hV) ≫
        openOverι G.arrows (invariantArrows G V) :=
  pullback.lift_snd _ _ _

/-- The source of a composite of composable arrows of the invariant open is the source of the
second arrow. -/
theorem invariantComposables_comp_comp_source (hV : IsInvariantOpen G V) :
    invariantComposables G V hV ≫ G.comp ≫ G.source =
      pullback.snd (invariantSource G V) (invariantTarget G V hV) ≫
        invariantSource G V ≫ openOverι G.objects V := by
  rw [G.source_comp, ← Category.assoc, invariantComposables_snd, Category.assoc,
    invariantSource_ι]

/-- `Stacks.Groupoids.invariantComposables_comp_comp_source` on underlying morphisms of
schemes. -/
theorem invariantComposables_comp_comp_source_left (hV : IsInvariantOpen G V) :
    (invariantComposables G V hV ≫ G.comp).left ≫ G.source.left =
      (pullback.snd (invariantSource G V) (invariantTarget G V hV) ≫
        invariantSource G V).left ≫ V.ι := by
  simpa only [Over.comp_left, openOverι_left, Category.assoc] using
    congrArg Over.Hom.left (invariantComposables_comp_comp_source G V hV)

/-- The composition morphism restricted to an invariant open of the object scheme and its
arrows. -/
def invariantComp (hV : IsInvariantOpen G V) :
    pullback (invariantSource G V) (invariantTarget G V hV) ⟶
      openOver G.arrows (invariantArrows G V) :=
  openOverLift (invariantComposables G V hV ≫ G.comp) (invariantArrows G V) (by
    intro x
    change ((invariantComposables G V hV ≫ G.comp).left ≫ G.source.left).base x ∈ V
    exact mem_of_eq_comp_ι _ (invariantComposables_comp_comp_source_left G V hV) x)

/-- The restricted composition morphism is compatible with the composition morphism of `G`. -/
@[simp]
theorem invariantComp_ι (hV : IsInvariantOpen G V) :
    invariantComp G V hV ≫ openOverι G.arrows (invariantArrows G V) =
      invariantComposables G V hV ≫ G.comp :=
  openOverLift_comp_openOverι _ _ _

/-! ### The groupoid scheme -/

/-- **The subgroupoid presentation carried by an invariant open of the object scheme.**  Its
objects are the invariant open `V`, its arrows the open `s⁻¹(V)` of the arrow scheme, and its
structure morphisms are those of `G` restricted along the two open immersions. -/
def invariantOpenSubgroupoid (hV : IsInvariantOpen G V) :
    GroupoidScheme.MonoSubgroupoid G where
  objects := openOver G.objects V
  arrows := openOver G.arrows (invariantArrows G V)
  ιObjects := openOverι G.objects V
  ιArrows := openOverι G.arrows (invariantArrows G V)
  mono_ιObjects := inferInstance
  mono_ιArrows := inferInstance
  source := invariantSource G V
  target := invariantTarget G V hV
  comp := invariantComp G V hV
  identity := invariantIdentity G V
  inverse := invariantInverse G V hV
  source_ι := invariantSource_ι G V
  target_ι := invariantTarget_ι G V hV
  identity_ι := invariantIdentity_ι G V
  inverse_ι := invariantInverse_ι G V hV
  comp_ι := invariantComp_ι G V hV

/-- **The groupoid scheme on an invariant open of the object scheme.** -/
def restrictInvariantOpen (hV : IsInvariantOpen G V) : GroupoidScheme S :=
  (invariantOpenSubgroupoid G V hV).toGroupoidScheme

/-- **The morphism of groupoid schemes from an invariant open into the whole groupoid.** -/
def restrictInvariantOpenHom (hV : IsInvariantOpen G V) :
    GroupoidScheme.Hom (restrictInvariantOpen G V hV) G :=
  (invariantOpenSubgroupoid G V hV).hom

/-- The object scheme of `restrictInvariantOpen G V hV` is the open `V`. -/
@[simp]
theorem restrictInvariantOpen_objects (hV : IsInvariantOpen G V) :
    (restrictInvariantOpen G V hV).objects = openOver G.objects V := rfl

/-- The arrow scheme of `restrictInvariantOpen G V hV` is the open `s⁻¹(V)`. -/
@[simp]
theorem restrictInvariantOpen_arrows (hV : IsInvariantOpen G V) :
    (restrictInvariantOpen G V hV).arrows = openOver G.arrows (invariantArrows G V) := rfl

/-- The map on object schemes of `restrictInvariantOpenHom G V hV` is the inclusion of `V`. -/
@[simp]
theorem restrictInvariantOpenHom_mapObjects (hV : IsInvariantOpen G V) :
    (restrictInvariantOpenHom G V hV).mapObjects = openOverι G.objects V := rfl

/-- The map on arrow schemes of `restrictInvariantOpenHom G V hV` is the inclusion of
`s⁻¹(V)`. -/
@[simp]
theorem restrictInvariantOpenHom_mapArrows (hV : IsInvariantOpen G V) :
    (restrictInvariantOpenHom G V hV).mapArrows =
      openOverι G.arrows (invariantArrows G V) := rfl

/-- The map on object schemes of `restrictInvariantOpenHom G V hV` is an open immersion. -/
instance isOpenImmersion_restrictInvariantOpenHom_mapObjects (hV : IsInvariantOpen G V) :
    IsOpenImmersion (restrictInvariantOpenHom G V hV).mapObjects.left :=
  isOpenImmersion_openOverι_left G.objects V

/-- The map on arrow schemes of `restrictInvariantOpenHom G V hV` is an open immersion. -/
instance isOpenImmersion_restrictInvariantOpenHom_mapArrows (hV : IsInvariantOpen G V) :
    IsOpenImmersion (restrictInvariantOpenHom G V hV).mapArrows.left :=
  isOpenImmersion_openOverι_left G.arrows (invariantArrows G V)

/-- **The open range of the map on object schemes is the invariant open itself.** -/
@[simp]
theorem opensRange_restrictInvariantOpenHom_mapObjects (hV : IsInvariantOpen G V) :
    (restrictInvariantOpenHom G V hV).mapObjects.left.opensRange = V :=
  Scheme.Opens.opensRange_ι V

/-- **The open range of the map on arrow schemes is the open `s⁻¹(V)` of the arrow scheme.** -/
@[simp]
theorem opensRange_restrictInvariantOpenHom_mapArrows (hV : IsInvariantOpen G V) :
    (restrictInvariantOpenHom G V hV).mapArrows.left.opensRange = invariantArrows G V :=
  Scheme.Opens.opensRange_ι (invariantArrows G V)

end InvariantOpen

/-! ### Invariant clopen decompositions -/

section Compl

variable {S : Scheme.{u}} (G : GroupoidScheme S) (V₁ V₂ : G.objects.left.Opens)

/-- Two complementary opens cover the object scheme. -/
theorem mem_or_mem_of_isCompl (h : IsCompl V₁ V₂) (x : G.objects.left) : x ∈ V₁ ∨ x ∈ V₂ := by
  have hx : x ∈ (V₁ ⊔ V₂ : G.objects.left.Opens) := by
    rw [h.sup_eq_top]
    trivial
  simpa using hx

/-- Two complementary opens are disjoint. -/
theorem not_mem_of_isCompl (h : IsCompl V₁ V₂) {x : G.objects.left} (h₁ : x ∈ V₁)
    (h₂ : x ∈ V₂) : False := by
  have hx : x ∈ (V₁ ⊓ V₂ : G.objects.left.Opens) := ⟨h₁, h₂⟩
  rw [h.inf_eq_bot] at hx
  exact hx

/-- **In a clopen decomposition of the object scheme, invariance of one half implies invariance
of the other.** -/
theorem isInvariantOpen_of_isCompl (h : IsCompl V₁ V₂) (hV₁ : IsInvariantOpen G V₁) :
    IsInvariantOpen G V₂ := by
  intro r hr
  refine (mem_or_mem_of_isCompl G V₁ V₂ h _).resolve_left fun h₁ => ?_
  exact not_mem_of_isCompl G V₁ V₂ h (x := G.source.left.base r)
    ((mem_invariantArrows_iff_target G V₁ hV₁ r).2 h₁) hr

/-- **Inverse images of complementary opens are complementary.** -/
theorem isCompl_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Y.Opens} (h : IsCompl A B) :
    IsCompl (f ⁻¹ᵁ A) (f ⁻¹ᵁ B) :=
  h.map (TopologicalSpace.Opens.comap f.base.hom)

/-- For complementary opens `V₁` and `V₂` of the object scheme, the opens `s⁻¹(V₁)` and `s⁻¹(V₂)`
of the arrow scheme are complementary. -/
theorem isCompl_invariantArrows (h : IsCompl V₁ V₂) :
    IsCompl (invariantArrows G V₁) (invariantArrows G V₂) :=
  isCompl_preimage G.source.left h

/-- **The two maps on object schemes of an invariant clopen decomposition have complementary
open ranges.** -/
theorem isCompl_opensRange_mapObjects (h : IsCompl V₁ V₂) (hV₁ : IsInvariantOpen G V₁) :
    IsCompl (restrictInvariantOpenHom G V₁ hV₁).mapObjects.left.opensRange
      (restrictInvariantOpenHom G V₂
        (isInvariantOpen_of_isCompl G V₁ V₂ h hV₁)).mapObjects.left.opensRange := by
  rwa [opensRange_restrictInvariantOpenHom_mapObjects,
    opensRange_restrictInvariantOpenHom_mapObjects]

/-- **The two maps on arrow schemes of an invariant clopen decomposition have complementary open
ranges.** -/
theorem isCompl_opensRange_mapArrows (h : IsCompl V₁ V₂) (hV₁ : IsInvariantOpen G V₁) :
    IsCompl (restrictInvariantOpenHom G V₁ hV₁).mapArrows.left.opensRange
      (restrictInvariantOpenHom G V₂
        (isInvariantOpen_of_isCompl G V₁ V₂ h hV₁)).mapArrows.left.opensRange := by
  rw [opensRange_restrictInvariantOpenHom_mapArrows,
    opensRange_restrictInvariantOpenHom_mapArrows]
  exact isCompl_invariantArrows G V₁ V₂ h

end Compl

end Stacks.Groupoids

end

end
