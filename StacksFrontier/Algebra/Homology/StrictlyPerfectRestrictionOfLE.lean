module

public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction

/-!
# Restriction of sheaves of modules along an inclusion of opens, and its exactness

Let `(X, O_X)` be a ringed space and let `V ≤ U` be opens of `X`. This file constructs the
restriction functor from `O_{X|U}`-modules to `O_{X|V}`-modules, together with the
comparison isomorphism identifying "restrict to `U`, then to `V`" with "restrict to `V`",
and proves that restriction along an open embedding — in particular both of these
restriction functors — is exact.

## Main definitions

* `Stacks.SheafOfModules.inclusionOfLE`: the inclusion `V ⟶ U` of opens as a map of spaces.
* `Stacks.SheafOfModules.functorCompIsoOfLE`: taking the image in `U` of an open of `V` and
  then the image in `Z` is taking the image in `Z` directly.
* `Stacks.SheafOfModules.restrictSheafOfRingsHomOfLE`,
  `Stacks.SheafOfModules.pushforwardSheafOfRingsHom`,
  `Stacks.SheafOfModules.pushforwardSheafOfRingsHomOfLE`: the comparison morphisms of
  sheaves of rings that the three pushforward functors below are taken along.
* `Stacks.SheafOfModules.restrictSheafOfModulesOfLE`: restriction of sheaves of modules
  along `V ≤ U`, for a sheaf of rings on an arbitrary space.
* `StrictlyPerfect.restrictModulesOfLE`: the special case of `O_X`-modules on a ringed
  space, and `StrictlyPerfect.restrictComplexOfLE` the induced functor on cochain complexes.

## Main results

* `Stacks.SheafOfModules.restrictSheafOfModulesOfLEIso` and
  `StrictlyPerfect.restrictModulesOfLEIso`, `StrictlyPerfect.restrictComplexOfLEIso`:
  restricting to `U` and then along `V ≤ U` is restricting to `V`.
* `Stacks.SheafOfModules.preservesFiniteLimits_pushforward`: the pushforward of sheaves of
  modules along *any* continuous functor of sites is left exact.
* `Stacks.SheafOfModules.restrictSheafOfModulesAdj`,
  `Stacks.SheafOfModules.restrictSheafOfModulesOfLEAdj`: restriction along an open embedding
  of spaces, and restriction along `V ≤ U`, are left adjoints.
* `Stacks.SheafOfModules.preservesFiniteColimits_restrictSheafOfModules` and
  `..._restrictSheafOfModulesOfLE`: hence both are right exact, so exact, so
  `Functor.PreservesHomology` holds for them by instance search.
* `StrictlyPerfect.isZero_homology_restrictComplex`,
  `StrictlyPerfect.isZero_homology_restrictComplexOfLE`,
  `StrictlyPerfect.isIso_homologyMap_restrictComplexOfLE`: the consequences used by the
  local arguments — restriction preserves vanishing of a cohomology sheaf, and preserves
  the property of inducing an isomorphism on one.

## Implementation notes

**The comparison is cheap because `Opens Z` is a poset.** `SheafOfModules.pushforwardComp`
is `Iso.refl`, so restricting to `U` and then along `V ≤ U` is *definitionally* the
pushforward along the composite functor of sites `Opens V ⥤ Opens U ⥤ Opens Z`. That
composite and `Opens V ⥤ Opens Z` are two functors with the *same* source and target, so
`SheafOfModules.pushforwardCongr₂` applies, and the natural isomorphism it wants is
objectwise `eqToIso` with naturality by `Subsingleton.elim`: the images
`ι_U '' (g '' O)` and `ι_V '' O` are equal sets, and `Opens Z` is thin. Nothing has to be
transported through a homeomorphism of subspaces. For the same reason every equation of
morphisms of sheaves of rings below reduces, after `← Functor.map_comp`, to
`Subsingleton.elim` in `Opens Z` — the proofs never inspect a section.

**Left exactness is proved on presheaves, right exactness by an adjunction.** Limits of
sheaves of modules are computed on the underlying presheaves of modules, and there on the
underlying presheaves of abelian groups, where the pushforward is precomposition; since
`SheafOfModules.forget` and `PresheafOfModules.toPresheaf` reflect isomorphisms, this gives
left exactness of `SheafOfModules.pushforward φ` for an arbitrary `φ`. Colimits are *not*
computed on presheaves, so right exactness is obtained instead from
`SheafOfModules.pushforwardPushforwardAdj` applied to `IsOpenMap.adjunction`, the adjunction
between taking images and taking preimages of opens; its two hypotheses are the equations
described above. Mathlib's own `SheafOfModules.pullbackPushforwardAdjunction` is not usable
here: the `IsRightAdjoint` instance it rests on is stated for sites that are *small in the
ring universe*, which would force the space universe to equal the ring universe.

**Universes.** Everything here is polymorphic in three independent universes: the space
`Z : TopCat.{t}` (resp. `X : RingedSpace.{r, t}`, whose *first* universe is the ring one),
the sheaf of rings `RingCat.{r}`, and the modules `SheafOfModules.{w}`. In particular
`StrictlyPerfect.OXMod.{r, w, t}` takes three universes — ring, module, carrier, in that
order — so a bare `OXMod.{r}` sets the *ring* universe and leaves the module and carrier
ones to be inferred; all three are written out below. No universe is
narrowed anywhere in this file, and the sheafification instances that force
`RingedSpace.{r, r}` at Stacks 08C6 are not used: the exactness proofs need none of them.

## References

* [Stacks Project, Tag 08C6](https://stacks.math.columbia.edu/tag/08C6)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Cohomology, Section 46](https://stacks.math.columbia.edu/tag/08C3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Opposite

universe w r t v₁ v₂ u₁ u₂

namespace Stacks.SheafOfModules

section LeftExact

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {Fun : C ⥤ D}
  {S : Sheaf J RingCat.{r}} {Rg : Sheaf K RingCat.{r}} [Functor.IsContinuous Fun J K]
  (φ : S ⟶ (Fun.sheafPushforwardContinuous RingCat.{r} J K).obj Rg)

/-- The pushforward of presheaves of modules along a functor of sites is left exact:
on underlying presheaves of abelian groups it is precomposition, and limits of presheaves
of modules are computed on those. -/
instance preservesFiniteLimits_presheafPushforward :
    PreservesFiniteLimits (PresheafOfModules.pushforward.{w} φ.hom) := by
  have : PreservesFiniteLimits (PresheafOfModules.toPresheaf.{w}
      ((sheafToPresheaf K RingCat.{r}).obj Rg) ⋙
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ _).obj Fun.op) :=
    Limits.comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits
      (PresheafOfModules.pushforward.{w} φ.hom ⋙ PresheafOfModules.toPresheaf S.obj) :=
    Limits.preservesFiniteLimits_of_natIso
      (PresheafOfModules.pushforwardCompToPresheaf φ.hom).symm
  exact ⟨fun _ _ _ => Limits.preservesLimitsOfShape_of_reflects_of_preserves _
    (PresheafOfModules.toPresheaf S.obj)⟩

/-- The pushforward of sheaves of modules along a continuous functor of sites is left exact:
limits of sheaves of modules are computed on the underlying presheaves of modules, where
the pushforward is `preservesFiniteLimits_presheafPushforward`. -/
instance preservesFiniteLimits_pushforward :
    PreservesFiniteLimits (_root_.SheafOfModules.pushforward.{w} φ) := by
  have h0 : PreservesFiniteLimits (PresheafOfModules.pushforward.{w} φ.hom) :=
    preservesFiniteLimits_presheafPushforward φ
  have : PreservesFiniteLimits (_root_.SheafOfModules.forget.{w} Rg ⋙
      PresheafOfModules.pushforward.{w} φ.hom) :=
    Limits.comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits
      (_root_.SheafOfModules.pushforward.{w} φ ⋙ _root_.SheafOfModules.forget.{w} S) :=
    Limits.preservesFiniteLimits_of_natIso
      (Iso.refl (_root_.SheafOfModules.forget.{w} Rg ⋙
        PresheafOfModules.pushforward.{w} φ.hom))
  exact ⟨fun _ _ _ => Limits.preservesLimitsOfShape_of_reflects_of_preserves _
    (_root_.SheafOfModules.forget.{w} S)⟩

end LeftExact

section RightExact

variable {Y Z : TopCat.{t}} {f : Z ⟶ Y} (hf : IsOpenEmbedding f)
  (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{r})

/-- The unit-side comparison of sheaves of rings for the adjunction between restriction
along an open embedding and the pushforward of sheaves of modules. -/
def pushforwardSheafOfRingsHom :
    letI : Functor.IsContinuous (Opens.map f) (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology Z) := inferInstance
    R ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{r}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology Z)).obj
      (restrictSheafOfRings hf R) :=
  ObjectProperty.homMk
    (Functor.whiskerRight (NatTrans.op hf.isOpenMap.adjunction.counit) R.obj)

/-- Restriction along an open embedding is a left adjoint: its right adjoint is the
pushforward along the preimage functor of opens. -/
def restrictSheafOfModulesAdj :
    letI : Functor.IsContinuous (Opens.map f) (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology Z) := inferInstance
    letI := hf.functor_isContinuous
    restrictSheafOfModules.{w} hf R ⊣
      _root_.SheafOfModules.pushforward.{w} (pushforwardSheafOfRingsHom hf R) := by
  letI i1 : Functor.IsContinuous (Opens.map f) (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology Z) := inferInstance
  letI i2 : Functor.IsContinuous hf.functor (Opens.grothendieckTopology Z)
      (Opens.grothendieckTopology Y) := hf.functor_isContinuous
  refine _root_.SheafOfModules.pushforwardPushforwardAdj hf.isOpenMap.adjunction
    (𝟙 (restrictSheafOfRings hf R)) (pushforwardSheafOfRingsHom hf R) ?_ ?_
  · exact NatTrans.ext (funext fun _ => (Category.comp_id _).symm)
  · refine NatTrans.ext (funext fun W => ?_)
    change 𝟙 _ ≫ R.obj.map _ ≫ R.obj.map _ = 𝟙 _
    rw [Category.id_comp, ← Functor.map_comp]
    convert R.obj.map_id (hf.functor.op.obj W) using 2
    exact Subsingleton.elim _ _

/-- Restriction of sheaves of modules along an open embedding preserves finite limits. -/
lemma preservesFiniteLimits_restrictSheafOfModules :
    PreservesFiniteLimits (restrictSheafOfModules.{w} hf R) := by
  let i2 : Functor.IsContinuous hf.functor (Opens.grothendieckTopology Z)
      (Opens.grothendieckTopology Y) := hf.functor_isContinuous
  exact preservesFiniteLimits_pushforward (𝟙 (restrictSheafOfRings hf R))

/-- Restriction of sheaves of modules along an open embedding preserves finite colimits. -/
lemma preservesFiniteColimits_restrictSheafOfModules :
    PreservesFiniteColimits (restrictSheafOfModules.{w} hf R) :=
  ⟨fun _ _ _ =>
    (restrictSheafOfModulesAdj.{w} hf R).leftAdjoint_preservesColimits.preservesColimitsOfShape⟩

end RightExact

section OfLE

variable {Z : TopCat.{t}} {V U : Opens Z}

/-- The inclusion of the open `V` into the open `U`, for `V ≤ U`, as a map of spaces. -/
abbrev inclusionOfLE (h : V ≤ U) :
    (Opens.toTopCat Z).obj V ⟶ (Opens.toTopCat Z).obj U :=
  (Opens.toTopCat Z).map (homOfLE h)

/-- The inclusion of `V` into `U` followed by the inclusion of `U` into `Z` is the inclusion
of `V` into `Z`. -/
lemma inclusionOfLE_comp (h : V ≤ U) :
    inclusionOfLE h ≫ U.inclusion' = V.inclusion' := rfl

/-- The inclusion of the open `V` into the open `U`, for `V ≤ U`, is an open embedding. -/
lemma isOpenEmbedding_inclusionOfLE (h : V ≤ U) :
    IsOpenEmbedding (inclusionOfLE h) :=
  (IsOpenEmbedding.of_comp_iff _ (Opens.isOpenEmbedding U)).mp (Opens.isOpenEmbedding V)

/-- Taking the image in `U` of an open of `V` and then the image in `Z` is taking the image
in `Z` directly. -/
def functorCompIsoOfLE (h : V ≤ U) :
    (isOpenEmbedding_inclusionOfLE h).functor ⋙ U.isOpenEmbedding.functor ≅
      V.isOpenEmbedding.functor :=
  NatIso.ofComponents (fun O => eqToIso (by
    refine TopologicalSpace.Opens.ext ?_
    change (U.inclusion' : _ → _) '' ((inclusionOfLE h : _ → _) '' (O : Set _)) = _
    rw [Set.image_image]
    rfl)) (fun _ => Subsingleton.elim _ _)

variable (R : Sheaf (Opens.grothendieckTopology Z) RingCat.{r})

/-- The comparison morphism of sheaves of rings witnessing that restricting `R` to `V`
agrees with restricting it to `U` and then along `V ≤ U`. -/
def restrictSheafOfRingsHomOfLE (h : V ≤ U) :
    letI := (isOpenEmbedding_inclusionOfLE h).functor_isContinuous
    restrictSheafOfRings V.isOpenEmbedding R ⟶
      (((isOpenEmbedding_inclusionOfLE h).functor).sheafPushforwardContinuous RingCat.{r}
        (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V))
        (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U))).obj
        (restrictSheafOfRings U.isOpenEmbedding R) :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op (functorCompIsoOfLE h).hom) R.obj)

/-- Restriction of sheaves of modules along an inclusion `V ≤ U` of opens. -/
def restrictSheafOfModulesOfLE (h : V ≤ U) :
    _root_.SheafOfModules.{w} (restrictSheafOfRings U.isOpenEmbedding R) ⥤
      _root_.SheafOfModules.{w} (restrictSheafOfRings V.isOpenEmbedding R) :=
  letI := (isOpenEmbedding_inclusionOfLE h).functor_isContinuous
  _root_.SheafOfModules.pushforward (restrictSheafOfRingsHomOfLE R h)

/-- Restricting to `U` and then along `V ≤ U` is restricting to `V`. -/
def restrictSheafOfModulesOfLEIso (h : V ≤ U) :
    restrictSheafOfModules.{w} U.isOpenEmbedding R ⋙ restrictSheafOfModulesOfLE.{w} R h ≅
      restrictSheafOfModules.{w} V.isOpenEmbedding R := by
  letI i1 : Functor.IsContinuous (isOpenEmbedding_inclusionOfLE h).functor
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V))
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U)) :=
    (isOpenEmbedding_inclusionOfLE h).functor_isContinuous
  letI i2 : Functor.IsContinuous U.isOpenEmbedding.functor
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U))
      (Opens.grothendieckTopology Z) :=
    U.isOpenEmbedding.functor_isContinuous
  letI i3 : Functor.IsContinuous V.isOpenEmbedding.functor
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V))
      (Opens.grothendieckTopology Z) :=
    V.isOpenEmbedding.functor_isContinuous
  letI i4 : Functor.IsContinuous
      ((isOpenEmbedding_inclusionOfLE h).functor ⋙ U.isOpenEmbedding.functor)
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V))
      (Opens.grothendieckTopology Z) :=
    Functor.isContinuous_comp _ _ (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V))
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U)) (Opens.grothendieckTopology Z)
  refine (_root_.SheafOfModules.pushforwardComp
    (restrictSheafOfRingsHomOfLE R h) (𝟙 (restrictSheafOfRings U.isOpenEmbedding R))).trans ?_
  refine _root_.SheafOfModules.pushforwardCongr₂ _
      (ψ := 𝟙 (restrictSheafOfRings V.isOpenEmbedding R)) (functorCompIsoOfLE h).symm ?_
  refine Sheaf.hom_ext (NatTrans.ext (funext fun O => ?_))
  change R.obj.map ((functorCompIsoOfLE h).hom.app O.unop).op ≫
      R.obj.map ((functorCompIsoOfLE h).inv.app O.unop).op = 𝟙 _
  rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id]
  exact R.obj.map_id _

/-- Restriction of sheaves of modules along `V ≤ U` is an additive functor. -/
instance (h : V ≤ U) : (restrictSheafOfModulesOfLE.{w} R h).Additive where
  map_add := by intros; ext; rfl

/-! ### Exactness of restriction along `V ≤ U` -/

/-- The preimage in `V` of an open of `U`, pushed forward to `Z`, is contained in the
image in `Z` of that open of `U`. -/
def imageMapOfLE (h : V ≤ U) :
    Opens.map (inclusionOfLE h) ⋙ V.isOpenEmbedding.functor ⟶
      U.isOpenEmbedding.functor where
  app W := homOfLE (by
    rintro x ⟨v, hv, rfl⟩
    exact ⟨inclusionOfLE h v, hv, rfl⟩)
  naturality _ _ _ := Subsingleton.elim _ _

/-- The unit-side comparison of sheaves of rings for the adjunction between restriction
along `V ≤ U` and the pushforward along the preimage functor of opens. -/
def pushforwardSheafOfRingsHomOfLE (h : V ≤ U) :
    letI : Functor.IsContinuous (Opens.map (inclusionOfLE h))
        (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U))
        (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V)) := inferInstance
    restrictSheafOfRings U.isOpenEmbedding R ⟶
      ((Opens.map (inclusionOfLE h)).sheafPushforwardContinuous RingCat.{r}
        (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U))
        (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V))).obj
        (restrictSheafOfRings V.isOpenEmbedding R) :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op (imageMapOfLE h)) R.obj)

/-- Restriction along `V ≤ U` is a left adjoint: its right adjoint is the pushforward
along the preimage functor of opens. -/
def restrictSheafOfModulesOfLEAdj (h : V ≤ U) :
    letI : Functor.IsContinuous (Opens.map (inclusionOfLE h))
        (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U))
        (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V)) := inferInstance
    restrictSheafOfModulesOfLE.{w} R h ⊣
      _root_.SheafOfModules.pushforward.{w} (pushforwardSheafOfRingsHomOfLE R h) := by
  letI i1 : Functor.IsContinuous (Opens.map (inclusionOfLE h))
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U))
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V)) := inferInstance
  letI i2 : Functor.IsContinuous (isOpenEmbedding_inclusionOfLE h).functor
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V))
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U)) :=
    (isOpenEmbedding_inclusionOfLE h).functor_isContinuous
  refine _root_.SheafOfModules.pushforwardPushforwardAdj
    (isOpenEmbedding_inclusionOfLE h).isOpenMap.adjunction
    (restrictSheafOfRingsHomOfLE R h) (pushforwardSheafOfRingsHomOfLE R h) ?_ ?_
  · refine NatTrans.ext (funext fun W => ?_)
    change R.obj.map _ = R.obj.map _ ≫ R.obj.map _
    rw [← Functor.map_comp]
    congr 1
  · refine NatTrans.ext (funext fun W => ?_)
    change R.obj.map _ ≫ R.obj.map _ ≫ R.obj.map _ = 𝟙 _
    rw [← Functor.map_comp, ← Functor.map_comp]
    convert R.obj.map_id _ using 2
    exact Subsingleton.elim _ _

/-- Restriction of sheaves of modules along `V ≤ U` preserves finite limits. -/
lemma preservesFiniteLimits_restrictSheafOfModulesOfLE (h : V ≤ U) :
    PreservesFiniteLimits (restrictSheafOfModulesOfLE.{w} R h) := by
  let i2 : Functor.IsContinuous (isOpenEmbedding_inclusionOfLE h).functor
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V))
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U)) :=
    (isOpenEmbedding_inclusionOfLE h).functor_isContinuous
  exact preservesFiniteLimits_pushforward (restrictSheafOfRingsHomOfLE R h)

/-- Restriction of sheaves of modules along `V ≤ U` preserves finite colimits. -/
lemma preservesFiniteColimits_restrictSheafOfModulesOfLE (h : V ≤ U) :
    PreservesFiniteColimits (restrictSheafOfModulesOfLE.{w} R h) :=
  ⟨fun _ _ _ => (restrictSheafOfModulesOfLEAdj.{w} R
    h).leftAdjoint_preservesColimits.preservesColimitsOfShape⟩

end OfLE

end Stacks.SheafOfModules

namespace StrictlyPerfect

open Stacks.SheafOfModules

variable {X : RingedSpace.{r, t}} {V U : Opens X.carrier}

/-- Restriction of `O_X`-modules from the open `U` to a smaller open `V`. -/
def restrictModulesOfLE (h : V ≤ U) :
    OXMod.{r, w, t} (X.restrict U.isOpenEmbedding) ⥤
      OXMod.{r, w, t} (X.restrict V.isOpenEmbedding) :=
  restrictSheafOfModulesOfLE (structureSheafOfRings X) h

/-- Restriction of `O_X`-modules from `U` to `V ≤ U` is an additive functor. -/
instance (h : V ≤ U) : (restrictModulesOfLE.{w} h (X := X)).Additive :=
  inferInstanceAs (restrictSheafOfModulesOfLE (structureSheafOfRings X) h).Additive

/-- Restricting to `U` and then to `V ≤ U` is restricting to `V`. -/
def restrictModulesOfLEIso (h : V ≤ U) :
    restrictModules.{w} X U ⋙ restrictModulesOfLE.{w} h ≅ restrictModules.{w} X V :=
  restrictSheafOfModulesOfLEIso (structureSheafOfRings X) h

/-- Restriction of a complex of `O_X`-modules from the open `U` to a smaller open `V`. -/
def restrictComplexOfLE (h : V ≤ U)
    (E : CochainComplex (OXMod.{r, w, t} (X.restrict U.isOpenEmbedding)) ℤ) :
    CochainComplex (OXMod.{r, w, t} (X.restrict V.isOpenEmbedding)) ℤ :=
  ((restrictModulesOfLE.{w} h).mapHomologicalComplex (ComplexShape.up ℤ)).obj E

/-- Restricting a complex to `U` and then to `V ≤ U` is restricting it to `V`. -/
def restrictComplexOfLEIso (h : V ≤ U) (E : CochainComplex (OXMod.{r, w, t} X) ℤ) :
    restrictComplexOfLE.{w} h (restrictComplex.{w} E U) ≅ restrictComplex.{w} E V :=
  (NatIso.mapHomologicalComplex (restrictModulesOfLEIso.{w} h) (ComplexShape.up ℤ)).app E

/-! ### Exactness -/

/-- Restriction of `O_X`-modules to an open `U` preserves finite limits. -/
lemma preservesFiniteLimits_restrictModules (U : Opens X.carrier) :
    PreservesFiniteLimits (restrictModules.{w} X U) :=
  preservesFiniteLimits_restrictSheafOfModules U.isOpenEmbedding (structureSheafOfRings X)

/-- Restriction of `O_X`-modules to an open `U` preserves finite colimits. -/
lemma preservesFiniteColimits_restrictModules (U : Opens X.carrier) :
    PreservesFiniteColimits (restrictModules.{w} X U) :=
  preservesFiniteColimits_restrictSheafOfModules U.isOpenEmbedding (structureSheafOfRings X)

/-- Restriction of `O_X`-modules from `U` to `V ≤ U` preserves finite limits. -/
lemma preservesFiniteLimits_restrictModulesOfLE (h : V ≤ U) :
    PreservesFiniteLimits (restrictModulesOfLE.{w} h (X := X)) :=
  preservesFiniteLimits_restrictSheafOfModulesOfLE (structureSheafOfRings X) h

/-- Restriction of `O_X`-modules from `U` to `V ≤ U` preserves finite colimits. -/
lemma preservesFiniteColimits_restrictModulesOfLE (h : V ≤ U) :
    PreservesFiniteColimits (restrictModulesOfLE.{w} h (X := X)) :=
  preservesFiniteColimits_restrictSheafOfModulesOfLE (structureSheafOfRings X) h

/-- Restriction to an open is exact, so it preserves the vanishing of a cohomology
sheaf. -/
lemma isZero_homology_restrictComplex [CategoryWithHomology (OXMod.{r, w, t} X)]
    [CategoryWithHomology (OXMod.{r, w, t} (X.restrict U.isOpenEmbedding))]
    (E : CochainComplex (OXMod.{r, w, t} X) ℤ) (i : ℤ) (hE : IsZero (E.homology i)) :
    IsZero ((restrictComplex.{w} E U).homology i) := by
  have h1 := preservesFiniteLimits_restrictModules.{w} (X := X) U
  have h2 := preservesFiniteColimits_restrictModules.{w} (X := X) U
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((HomologicalComplex.exactAt_iff_isZero_homology E i).2 hE).map
    (restrictModules.{w} X U)

/-- Restriction along `V ≤ U` is exact, so it preserves the vanishing of a cohomology
sheaf. -/
lemma isZero_homology_restrictComplexOfLE (h : V ≤ U)
    [CategoryWithHomology (OXMod.{r, w, t} (X.restrict U.isOpenEmbedding))]
    [CategoryWithHomology (OXMod.{r, w, t} (X.restrict V.isOpenEmbedding))]
    (E : CochainComplex (OXMod.{r, w, t} (X.restrict U.isOpenEmbedding)) ℤ) (i : ℤ)
    (hE : IsZero (E.homology i)) :
    IsZero ((restrictComplexOfLE.{w} h E).homology i) := by
  have h1 := preservesFiniteLimits_restrictModulesOfLE.{w} (X := X) h
  have h2 := preservesFiniteColimits_restrictModulesOfLE.{w} (X := X) h
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((HomologicalComplex.exactAt_iff_isZero_homology E i).2 hE).map
    (restrictModulesOfLE.{w} h)

/-- Restriction along `V ≤ U` is exact, so it preserves the property of inducing an
isomorphism on a cohomology sheaf. -/
lemma isIso_homologyMap_restrictComplexOfLE (h : V ≤ U)
    [CategoryWithHomology (OXMod.{r, w, t} (X.restrict U.isOpenEmbedding))]
    [CategoryWithHomology (OXMod.{r, w, t} (X.restrict V.isOpenEmbedding))]
    {E F : CochainComplex (OXMod.{r, w, t} (X.restrict U.isOpenEmbedding)) ℤ} (α : E ⟶ F)
    (i : ℤ) (hα : IsIso (HomologicalComplex.homologyMap α i)) :
    IsIso (HomologicalComplex.homologyMap
      ((restrictModulesOfLE.{w} h).mapHomologicalComplex (ComplexShape.up ℤ) |>.map α) i) := by
  have h1 := preservesFiniteLimits_restrictModulesOfLE.{w} (X := X) h
  have h2 := preservesFiniteColimits_restrictModulesOfLE.{w} (X := X) h
  have : QuasiIsoAt α i := (quasiIsoAt_iff_isIso_homologyMap α i).2 hα
  exact (quasiIsoAt_iff_isIso_homologyMap _ i).1 inferInstance

end StrictlyPerfect

end
