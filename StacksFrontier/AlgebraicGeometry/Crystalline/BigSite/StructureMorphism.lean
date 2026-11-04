module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.PresheafComp
public import StacksFrontier.CategoryTheory.Sites.CoverLifting

/-!
# The structure morphism of the big crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`.  Forgetting the ambient divided power
thickening is a cocontinuous functor `CRIS(X/S) ⥤ Sch/X`: a Zariski covering of the thickened
scheme `U` of an object `(U, T, δ)` is the restriction of a Zariski covering of the ambient scheme
`T`, because the immersion `U ↪ T` is a thickening and therefore a homeomorphism on points.  Hence
there is a morphism of topoi `U_{X/S} : (X/S)_CRIS ⟶ Sh((Sch/X)_Zar)` from the big crystalline
topos to the big Zariski topos of `X`.

Composing the forgetful functor with `Over.map` along the structure morphism `X ⟶ S` gives the
cocontinuous functor `(U, T, δ)/S ↦ U/S`, and so the *structure morphism*
`(X/S)_CRIS ⟶ Sh((Sch/S)_Zar)` of the big crystalline site.  When `p` is locally nilpotent on the
closed fibre `S₀ = V(I)`, the closed fibre is itself a global crystalline situation over
`(S, I, γ)`, the site `CRIS(S₀/S)` exists, and the structure morphism of `X` factors through it:
the square built from `f_CRIS`, `U_{X/S}`, `U_{S₀/S}` and `f_big` commutes, the two big Zariski
arrows out of `Sh((Sch/X)_Zar)` compose to the one along `X ⟶ S`, and the resulting composite is
the structure morphism.

The same argument applied to a change of divided power base shows that the structure morphisms are
compatible with `f_CRIS`: for a morphism `(S, I, γ) ⟶ (S', I', γ')` and a morphism `X ⟶ Y` over the
closed fibres, the square with vertical arrows the structure morphisms and horizontal arrows
`f_CRIS` and `f_big` commutes.

## Main definitions

* `CategoryTheory.Functor.sheafPushforwardCocontinuousComp` — the sheaf pushforward along a
  composite of cocontinuous functors is the composite of the sheaf pushforwards, the content of
  [Stacks, Tag 03L5] for sites of arbitrary size, and
  `CategoryTheory.Functor.sheafPushforwardCocontinuousCongr` the same for equal functors.
* `AlgebraicGeometry.zariskiOverMorphism` — the morphism of big Zariski topoi
  `Sh((Sch/X)_Zar) ⟶ Sh((Sch/Y)_Zar)` induced by a morphism of schemes `X ⟶ Y`.
* `Crystalline.GlobalCrystallineSituation.zariskiComparison` — the morphism of topoi
  `U_{X/S} : (X/S)_CRIS ⟶ Sh((Sch/X)_Zar)`, [Stacks, Tag 07ID].
* `Crystalline.GlobalCrystallineSituation.structureFunctor` — the cocontinuous functor
  `CRIS(X/S) ⥤ Sch/S`, `(U, T, δ)/S ↦ U/S`, and
  `Crystalline.GlobalCrystallineSituation.structureMorphism` the structure morphism
  `(X/S)_CRIS ⟶ Sh((Sch/S)_Zar)` it induces, [Stacks, Tag 07IE].
* `Crystalline.GlobalCrystallineSituation.closedFiberSituation` — the closed fibre `S₀ = V(I)` as a
  global crystalline situation over `(S, I, γ)`, and
  `Crystalline.GlobalCrystallineSituation.closedFiberMorphism` the morphism of crystalline topoi
  `(X/S)_CRIS ⟶ (S₀/S)_CRIS` induced by the structure morphism `X ⟶ S₀`, [Stacks, Tag 07IE].

## Main results

* `Crystalline.GlobalCrystallineSituation.forget_isCocontinuous` — the forgetful functor
  `CRIS(X/S) ⥤ Sch/X` is cocontinuous for the Zariski topologies, [Stacks, Tag 07ID].
* `Crystalline.GlobalCrystallineSituation.changeBaseZariskiSquare` and
  `Crystalline.GlobalCrystallineSituation.comparisonSquare` — the square formed by the two
  crystalline-to-Zariski comparisons, a change of base and the induced big Zariski morphism
  commutes up to a canonical isomorphism, [Stacks, Tag 07IE].
* `Crystalline.GlobalCrystallineSituation.zariskiStructureTriangle` and
  `Crystalline.GlobalCrystallineSituation.structureTriangle` — the two big Zariski arrows
  `Sh((Sch/X)_Zar) ⟶ Sh((Sch/S₀)_Zar) ⟶ Sh((Sch/S)_Zar)` compose to the one along `X ⟶ S`, and
  that one composed with `U_{X/S}` is the structure morphism, [Stacks, Tag 07IE].
* `Crystalline.GlobalCrystallineSituation.closedFiberStructureTriangle` — the structure morphism is
  the route through `(S₀/S)_CRIS` and the big Zariski topos of `S₀`, [Stacks, Tag 07IE].
* `Crystalline.GlobalCrystallineSituation.changeBase_comp_structureFunctor` and
  `Crystalline.GlobalCrystallineSituation.changeBaseStructureSquare` — the square of sites formed
  by a change of base, the two functors `(U, T, δ)/S ↦ U/S` and `Over.map` along `S ⟶ S'` commutes
  on the nose, and hence so does the square of topoi it induces, [Stacks, Tag 07MG].

## Implementation notes

The big Zariski site `(Sch/X)_Zar` is Mathlib's `Scheme.zariskiTopology.over X`, the Zariski
topology on the slice over `X` of the category of *all* schemes; this is forced by
`Crystalline.GlobalCrystallineSituation.forget`, which lands in that slice.

A commutative diagram of morphisms of topoi is recorded as an isomorphism of the composite
pushforward functors, i.e. an invertible 2-morphism in the sense of [Stacks, Tag 04IA]; the
companion isomorphism of inverse images is then its mate under the two adjunctions, so no
information is lost.  In each case the underlying square of sites commutes on the nose, which is
what `Crystalline.GlobalCrystallineSituation.changeBase_comp_forget` and
`Crystalline.GlobalCrystallineSituation.changeBase_comp_structureFunctor` record.

[Stacks, Tag 07IE] and [Stacks, Tag 07MG] say *ringed* topoi, and **that is an error in the
source**, which is why every attribute below says "as topoi" instead.  A morphism of ringed topoi
would need `τ^{-1} 𝒪 ⟶ 𝒪_{X/S}`, and the canonical comparison runs the other way: it is the
surjection `𝒪_{X/S} ↠ \underline{𝐆_a} = τ^{-1}𝒪` with kernel `J_{X/S}` that the source itself
displays in its section on the structure sheaf.  A map in the required direction would be a
canonical splitting of a divided power thickening, and there is none: with `S = Spec 𝐙_p`,
`I = (p)`, `X = Spec 𝐅_p`, the object `(Spec 𝐅_p, Spec 𝐙/p², δ)` and `V = 𝐀¹_S`, the
`S`-automorphism `t ↦ t + p` of `V` fixes the map `U → V` given by `t ↦ 0`, so naturality together
with multiplicativity would force `p = 0` in `𝐙/p²`.

The Stacks Project has acknowledged this on [Stacks, Tag 07IM] — Berthelot's
*Cohomologie cristalline* III, Remarque 3.2.5 is cited in the comments there, and the body of 07IM
now reads "commutative diagram of topoi" — but the correction was not propagated to 07IE or 07MG,
which still carry the stale wording.  So the squares recorded here, as squares of topoi, are the
corrected statements of those two tags and not a weakening of them.

The diagrams of [Stacks, Tag 07IE] and [Stacks, Tag 07MG] are diagrams of *ringed* topoi.  The
ring structures are not carried in this file, but they are not missing from the library: both
the big crystalline topos and the big Zariski topos are equipped with a sheaf of rings, and the
big crystalline structure sheaf is a sheaf, not merely a presheaf, of rings.  The big crystalline
structure sheaf `𝒪_{X/S}` is a sheaf of rings,
`Crystalline.GlobalCrystallineSituation.crystallineStructureSheaf` of [Stacks, Tag 07IX], and
is a sheaf of commutative rings too,
`Crystalline.GlobalCrystallineSituation.structureSheaf_isSheaf`; and the big Zariski topos of a
scheme is a ringed topos, `AlgebraicGeometry.zariskiOverRingedTopos`.  The ringed form of the
diagram of [Stacks, Tag 07IE] -- its corners as ringed topoi, and `U_{X/S}` and the structure
morphism as morphisms of ringed topoi -- is
`StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.RingedStructureMorphism`, which imports this
file.  Note that the structure sheaf it puts on `(X/S)_CRIS` is `U_{X/S}⁻¹𝒪`, the sheaf
`\underline{𝐆_a} : (U, T, δ) ↦ Γ(U, 𝒪_U)` of [Stacks, Tag 07IN], and not `𝒪_{X/S}`; the reason
is recorded there.

## References

* [Stacks Project, Tag 03L5](https://stacks.math.columbia.edu/tag/03L5)
* [Stacks Project, Tag 07ID](https://stacks.math.columbia.edu/tag/07ID)
* [Stacks Project, Tag 07IE](https://stacks.math.columbia.edu/tag/07IE)
* [Stacks Project, Tag 07MG](https://stacks.math.columbia.edu/tag/07MG)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe v₁ v₂ v₃ w w' u₁ u₂ u₃ u

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] (A : Type w) [Category.{w'} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)

/-- **Equal cocontinuous functors have the same sheaf pushforward.**  Being cocontinuous is a
proposition, so the two pushforwards agree once the functors do. -/
noncomputable def sheafPushforwardCocontinuousCongr (F F' : C ⥤ D)
    [F.IsCocontinuous J K] [F'.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, F'.op.HasPointwiseRightKanExtension P] (h : F = F') :
    F.sheafPushforwardCocontinuous A J K ≅ F'.sheafPushforwardCocontinuous A J K := by
  subst h
  exact Iso.refl _

/-- **The sheaf pushforward along a composite of cocontinuous functors is the composite of the
sheaf pushforwards.**  Transporting the comparison of right Kan extensions along the fully
faithful inclusion of sheaves into presheaves.

This is the statement of [Stacks, Tag 03L5] for sites whose underlying categories need not be
small and whose coefficients need not lie in the same universe. -/
@[sga "4 III 4.4" "partial", sga "4 IV 4.7" "partial"]
noncomputable def sheafPushforwardCocontinuousComp (F : C ⥤ D) (G : D ⥤ E)
    [F.IsCocontinuous J K] [G.IsCocontinuous K L]
    [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]
    [∀ P : Dᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, (F ⋙ G).op.HasPointwiseRightKanExtension P] :
    letI := CategoryTheory.isCocontinuous_comp F G J K (L := L)
    (F ⋙ G).sheafPushforwardCocontinuous A J L ≅
      F.sheafPushforwardCocontinuous A J K ⋙ G.sheafPushforwardCocontinuous A K L :=
  let := CategoryTheory.isCocontinuous_comp F G J K (L := L)
  have : ∀ P : Cᵒᵖ ⥤ A, (F.op ⋙ G.op).HasPointwiseRightKanExtension P := fun P ↦
    inferInstanceAs ((F ⋙ G).op.HasPointwiseRightKanExtension P)
  Functor.fullyFaithfulCancelRight (sheafToPresheaf L A)
    (Functor.isoWhiskerLeft (sheafToPresheaf J A) (Functor.ranCompIsoOfAdjunctions A F.op G.op))

end CategoryTheory.Functor

namespace AlgebraicGeometry

/-- **The morphism of big Zariski topoi induced by a morphism of schemes `f : X ⟶ Y`.**  Its
pushforward is the sheaf pushforward along the cocontinuous functor `Over.map f`, and its inverse
image is the sheaf pullback, which is left exact. -/
@[sga "4 III 2.3" "special case"]
noncomputable def zariskiOverMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismOfTopoi (Sheaf (Scheme.zariskiTopology.over X) (Type (u + 1)))
      (Sheaf (Scheme.zariskiTopology.over Y) (Type (u + 1))) where
  pushforward := (Over.map f).sheafPushforwardCocontinuous (Type (u + 1))
    (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y)
  inverseImage := (Over.map f).sheafPullbackCocontinuous (Type (u + 1))
    (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y)
  adj := (Over.map f).sheafAdjunctionPullbackCocontinuous (Type (u + 1))
    (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y)
  preservesFiniteLimits := inferInstance

/-- **The morphisms of big Zariski topoi compose.**  Both composites are the sheaf pushforward
along `Over.map` of the composite morphism of schemes. -/
noncomputable def zariskiOverMorphismComp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    ((zariskiOverMorphism b).comp (zariskiOverMorphism a)).pushforward ≅
      (zariskiOverMorphism (a ≫ b)).pushforward :=
  have : (Over.map a ⋙ Over.map b).IsCocontinuous (Scheme.zariskiTopology.over X)
      (Scheme.zariskiTopology.over Z) :=
    CategoryTheory.isCocontinuous_comp _ _ _ (Scheme.zariskiTopology.over Y)
  (Functor.sheafPushforwardCocontinuousComp (Type (u + 1))
      (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y)
      (Scheme.zariskiTopology.over Z) (Over.map a) (Over.map b)).symm ≪≫
    Functor.sheafPushforwardCocontinuousCongr (Type (u + 1))
      (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Z)
      (Over.map a ⋙ Over.map b) (Over.map (a ≫ b)) (Over.mapComp_eq a b).symm

end AlgebraicGeometry

namespace Crystalline.GlobalCrystallineSituation

open Thickening
open _root_.Crystalline.Stacks.Thickenings

/-- **Stacks Project, Tag 07ID.**  The forgetful functor `CRIS(X/S) ⥤ Sch/X` is cocontinuous for
the Zariski topologies.  A Zariski covering of the thickened scheme `U` of an object `(U, T, δ)`
is, up to refinement by its members' images, the family of opens of `T` matching the images of its
members: the immersion `U ↪ T` is a thickening, hence a homeomorphism on points, and restricting
`(U, T, δ)` to those opens of `T` is a Zariski covering family of `CRIS(X/S)` whose image under
the forgetful functor refines the given one. -/
@[stacks 07ID "cocontinuity of the forgetful functor"]
instance forget_isCocontinuous (S : GlobalCrystallineSituation.{u}) :
    (forget S).IsCocontinuous (topology S) (Scheme.zariskiTopology.over S.X) := by
  constructor
  intro A R hR
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  have hi : Stacks.Thickenings.IsThickening A.thickening.immersion := A.thickening.isThickening
  set idx : ULift.{u + 1, u} 𝒰.I₀ → 𝒰.I₀ := ULift.down
  set W : ULift.{u + 1, u} 𝒰.I₀ → A.thickening.target.scheme.Opens :=
    fun i ↦ hi.opensCongr (𝒰.f (idx i)).opensRange
  have hpre (i : ULift.{u + 1, u} 𝒰.I₀) :
      A.thickening.immersion ⁻¹ᵁ W i = (𝒰.f (idx i)).opensRange :=
    hi.preimage_opensCongr _
  have hcov : ∀ x : A.thickening.target.scheme, ∃ i, x ∈ W i := by
    intro x
    obtain ⟨y, rfl⟩ := hi.2 x
    obtain ⟨i, z, hz⟩ := 𝒰.exists_eq y
    refine ⟨ULift.up i, ?_⟩
    change y ∈ A.thickening.immersion ⁻¹ᵁ W (ULift.up i)
    rw [hpre]
    exact ⟨z, hz⟩
  refine (topology S).superset_covering ?_
    (zariskiCovering_mem_topology S (A.restrictOpenCover W)
      (isZariskiCovering_restrictOpenCover A W hcov))
  rw [Sieve.generate_le_iff]
  rintro B g ⟨i⟩
  change R.arrows ((forget S).map (A.restrictOpenHom (W i)))
  have h𝒰i : (Sieve.overEquiv ((forget S).obj A) R).arrows (𝒰.f (idx i)) :=
    h𝒰 _ _ (Presieve.ofArrows.mk (idx i))
  have hrange : Set.range ((A.thickening.immersion ⁻¹ᵁ W i).ι).base =
      Set.range (𝒰.f (idx i)).base := by
    rw [Scheme.Opens.range_ι, hpre i]
    exact Scheme.Hom.coe_opensRange _
  have hmem : (Sieve.overEquiv ((forget S).obj A) R).arrows
      ((forget S).map (A.restrictOpenHom (W i))).left := by
    rw [forget_map_left, restrictOpenHom_sourceHom,
      ← @IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _ (A.thickening.immersion ⁻¹ᵁ W i).ι
        (𝒰.f (idx i)) inferInstance (𝒰.map_prop _) hrange]
    exact (Sieve.overEquiv ((forget S).obj A) R).downward_closed h𝒰i _
  rwa [Sieve.overEquiv_iff] at hmem

/-- **Stacks Project, Tag 07ID.**  The comparison morphism of topoi
`U_{X/S} : (X/S)_CRIS ⟶ Sh((Sch/X)_Zar)` from the big crystalline topos of `X/S` to the big
Zariski topos of `X`, induced by the cocontinuous forgetful functor `CRIS(X/S) ⥤ Sch/X`. -/
@[stacks 07ID "the morphism of topoi"]
noncomputable def zariskiComparison (S : GlobalCrystallineSituation.{u}) :
    MorphismOfTopoi (topos S) (Sheaf (Scheme.zariskiTopology.over S.X) (Type (u + 1))) where
  pushforward := (forget S).sheafPushforwardCocontinuous (Type (u + 1)) (topology S)
    (Scheme.zariskiTopology.over S.X)
  inverseImage := (forget S).sheafPullbackCocontinuous (Type (u + 1)) (topology S)
    (Scheme.zariskiTopology.over S.X)
  adj := (forget S).sheafAdjunctionPullbackCocontinuous (Type (u + 1)) (topology S)
    (Scheme.zariskiTopology.over S.X)
  preservesFiniteLimits := inferInstance

/-- **Stacks Project, Tag 07IE.**  The functor `CRIS(X/S) ⥤ Sch/S`, `(U, T, δ)/S ↦ U/S`: forget
the ambient divided power thickening and read the resulting scheme over `X` as a scheme over
`S`. -/
@[stacks 07IE "the functor (U, T, δ)/S ↦ U/S"]
noncomputable def structureFunctor (S : GlobalCrystallineSituation.{u}) :
    Thickening S ⥤ Over S.S.scheme :=
  forget S ⋙ Over.map (sourceToBase S)

/-- **Stacks Project, Tag 07IE.**  The functor `(U, T, δ)/S ↦ U/S` is cocontinuous, being the
composite of the cocontinuous forgetful functor with `Over.map` along `X ⟶ S`. -/
@[stacks 07IE "cocontinuity of (U, T, δ)/S ↦ U/S"]
instance structureFunctor_isCocontinuous (S : GlobalCrystallineSituation.{u}) :
    (structureFunctor S).IsCocontinuous (topology S)
      (Scheme.zariskiTopology.over S.S.scheme) :=
  CategoryTheory.isCocontinuous_comp _ _ _ (Scheme.zariskiTopology.over S.X)

/-- **Stacks Project, Tag 07IE.**  The structure morphism
`(X/S)_CRIS ⟶ Sh((Sch/S)_Zar)` of the big crystalline site, the morphism of topoi attached to the
cocontinuous functor `(U, T, δ)/S ↦ U/S`.  It is defined whether or not `p` is locally nilpotent
on the closed fibre `S₀ = V(I)`. -/
@[stacks 07IE "the structure morphism"]
noncomputable def structureMorphism (S : GlobalCrystallineSituation.{u}) :
    MorphismOfTopoi (topos S)
      (Sheaf (Scheme.zariskiTopology.over S.S.scheme) (Type (u + 1))) where
  pushforward := (structureFunctor S).sheafPushforwardCocontinuous (Type (u + 1)) (topology S)
    (Scheme.zariskiTopology.over S.S.scheme)
  inverseImage := (structureFunctor S).sheafPullbackCocontinuous (Type (u + 1)) (topology S)
    (Scheme.zariskiTopology.over S.S.scheme)
  adj := (structureFunctor S).sheafAdjunctionPullbackCocontinuous (Type (u + 1)) (topology S)
    (Scheme.zariskiTopology.over S.S.scheme)
  preservesFiniteLimits := inferInstance

section Compatibility

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}

/-- **Change of divided power base commutes with the forgetful functors.**  Change of base leaves
the underlying thickening untouched and composes the map to `X` with `X ⟶ Y`, which is exactly what
`Over.map` along `X ⟶ Y` does to the image of the forgetful functor. -/
theorem changeBase_comp_forget :
    changeBase S S' f g h ⋙ forget S' = forget S ⋙ Over.map g := rfl

include h in
/-- **The structure morphisms to the divided power bases are compatible.**  The composite
`X ⟶ Y ⟶ S'` agrees with `X ⟶ S ⟶ S'` because the square of closed fibres commutes and the
inclusion of a closed fibre is natural. -/
theorem comp_sourceToBase : g ≫ sourceToBase S' = sourceToBase S ≫ f.hom := by
  rw [sourceToBase, sourceToBase, Category.assoc,
    ← DividedPowerScheme.closedFiberMap_comp_closedFiberι f, ← Category.assoc, ← h,
    Category.assoc]

/-- **The square of sites underlying [Stacks, Tag 07MG] commutes on the nose.**  Both composites
send `(U, T, δ)/S` to `U` read as a scheme over `S'`. -/
theorem changeBase_comp_structureFunctor :
    changeBase S S' f g h ⋙ structureFunctor S' = structureFunctor S ⋙ Over.map f.hom := by
  rw [structureFunctor, structureFunctor, ← Functor.assoc, changeBase_comp_forget,
    Functor.assoc, Functor.assoc, ← Over.mapComp_eq, ← Over.mapComp_eq,
    comp_sourceToBase (h := h)]

end Compatibility

/-- **Stacks Project, Tag 07IE.**  Change of divided power base and the crystalline-to-Zariski
comparisons form a commutative square: the composite
`(X/S)_CRIS ⟶ (Y/S')_CRIS ⟶ Sh((Sch/Y)_Zar)` is isomorphic to
`(X/S)_CRIS ⟶ Sh((Sch/X)_Zar) ⟶ Sh((Sch/Y)_Zar)`, both being the morphism of topoi attached to
the cocontinuous functor `(U, T, δ) ↦ U/Y`. -/
@[stacks 07IE "the crystalline-Zariski square, as topoi"]
noncomputable def changeBaseZariskiSquare (S S' : GlobalCrystallineSituation.{u})
    (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    ((zariskiOverMorphism g).comp (zariskiComparison S)).pushforward ≅
      ((zariskiComparison S').comp (changeBaseMorphism S S' f g h)).pushforward :=
  have : (forget S ⋙ Over.map g).IsCocontinuous (topology S)
      (Scheme.zariskiTopology.over S'.X) :=
    CategoryTheory.isCocontinuous_comp _ _ _ (Scheme.zariskiTopology.over S.X)
  have : (changeBase S S' f g h ⋙ forget S').IsCocontinuous (topology S)
      (Scheme.zariskiTopology.over S'.X) :=
    CategoryTheory.isCocontinuous_comp _ _ _ (topology S')
  (Functor.sheafPushforwardCocontinuousComp (Type (u + 1)) (topology S)
      (Scheme.zariskiTopology.over S.X) (Scheme.zariskiTopology.over S'.X)
      (forget S) (Over.map g)).symm ≪≫
    Functor.sheafPushforwardCocontinuousCongr (Type (u + 1)) (topology S)
      (Scheme.zariskiTopology.over S'.X) (forget S ⋙ Over.map g)
      (changeBase S S' f g h ⋙ forget S') (changeBase_comp_forget (h := h)).symm ≪≫
    Functor.sheafPushforwardCocontinuousComp (Type (u + 1)) (topology S) (topology S')
      (Scheme.zariskiTopology.over S'.X) (changeBase S S' f g h) (forget S')

/-- **Stacks Project, Tag 07IE.**  The closed fibre `S₀ = V(I)` of a divided power scheme on which
`p` is locally nilpotent is itself a global crystalline situation over `(S, I, γ)`, with the
identity as its structure morphism to the closed fibre.  In particular the big crystalline site
`CRIS(S₀/S)` is available. -/
@[stacks 07IE "the crystalline situation on the closed fibre"]
noncomputable abbrev closedFiberSituation (S : GlobalCrystallineSituation.{u})
    (hp : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x)) :
    GlobalCrystallineSituation.{u} where
  p := S.p
  S := S.S
  X := DividedPowerScheme.closedFiber S.S
  toClosedFiber := 𝟙 _
  prime_locallyNilpotent := hp

/-- The structure morphism `X ⟶ S₀` is a morphism over the closed fibre of the identity of the
divided power base. -/
theorem closedFiberSituation_comm (S : GlobalCrystallineSituation.{u})
    (hp : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x)) :
    S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap (𝟙 S.S) =
      S.toClosedFiber ≫ (closedFiberSituation S hp).toClosedFiber := by
  simp

/-- **Stacks Project, Tag 07IE.**  The morphism of crystalline topoi
`f_CRIS : (X/S)_CRIS ⟶ (S₀/S)_CRIS` attached to the structure morphism `f : X ⟶ S₀`, obtained from
change of divided power base along the identity of `(S, I, γ)`. -/
@[stacks 07IE "the crystalline arrow of the diagram"]
noncomputable def closedFiberMorphism (S : GlobalCrystallineSituation.{u})
    (hp : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x)) :
    MorphismOfTopoi (topos S) (topos (closedFiberSituation S hp)) :=
  changeBaseMorphism S (closedFiberSituation S hp) (𝟙 S.S) S.toClosedFiber
    (closedFiberSituation_comm S hp)

/-- **Stacks Project, Tag 07IE.**  The square of the diagram: `U_{S₀/S} ∘ f_CRIS` is isomorphic to
`f_big ∘ U_{X/S}`, for `f : X ⟶ S₀` the structure morphism. -/
@[stacks 07IE "the square of the diagram, as topoi"]
noncomputable def comparisonSquare (S : GlobalCrystallineSituation.{u})
    (hp : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x)) :
    ((zariskiOverMorphism S.toClosedFiber).comp (zariskiComparison S)).pushforward ≅
      ((zariskiComparison (closedFiberSituation S hp)).comp
        (closedFiberMorphism S hp)).pushforward :=
  changeBaseZariskiSquare S (closedFiberSituation S hp) (𝟙 S.S) S.toClosedFiber
    (closedFiberSituation_comm S hp)

/-- **Stacks Project, Tag 07IE.**  The lower triangle of the diagram: the big Zariski morphisms
along `X ⟶ S₀` and `S₀ ⟶ S` compose to the one along `X ⟶ S`. -/
@[stacks 07IE "the big Zariski triangle of the diagram, as topoi"]
noncomputable def zariskiStructureTriangle (S : GlobalCrystallineSituation.{u}) :
    ((zariskiOverMorphism (DividedPowerScheme.closedFiberι S.S)).comp
        (zariskiOverMorphism S.toClosedFiber)).pushforward ≅
      (zariskiOverMorphism (sourceToBase S)).pushforward :=
  zariskiOverMorphismComp S.toClosedFiber (DividedPowerScheme.closedFiberι S.S)

/-- **Stacks Project, Tag 07IE.**  The structure morphism is the composite of the
crystalline-to-Zariski comparison `U_{X/S}` with the big Zariski morphism along `X ⟶ S`. -/
@[stacks 07IE "the structure morphism through the big Zariski topos of X, as topoi"]
noncomputable def structureTriangle (S : GlobalCrystallineSituation.{u}) :
    ((zariskiOverMorphism (sourceToBase S)).comp (zariskiComparison S)).pushforward ≅
      (structureMorphism S).pushforward :=
  (Functor.sheafPushforwardCocontinuousComp (Type (u + 1)) (topology S)
    (Scheme.zariskiTopology.over S.X) (Scheme.zariskiTopology.over S.S.scheme)
    (forget S) (Over.map (sourceToBase S))).symm

/-- **Stacks Project, Tag 07IE.**  The structure morphism of the big crystalline site is the route
through `(S₀/S)_CRIS` and the big Zariski topos of `S₀`, which is the composition the remark takes
as the definition of the structure morphism when `p` is locally nilpotent on `S₀`. -/
@[stacks 07IE "the structure morphism through the crystalline topos of the closed fibre, as topoi"]
noncomputable def closedFiberStructureTriangle (S : GlobalCrystallineSituation.{u})
    (hp : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x)) :
    ((zariskiOverMorphism (DividedPowerScheme.closedFiberι S.S)).comp
        ((zariskiComparison (closedFiberSituation S hp)).comp
          (closedFiberMorphism S hp))).pushforward ≅
      (structureMorphism S).pushforward :=
  Functor.isoWhiskerRight (comparisonSquare S hp).symm
      (zariskiOverMorphism (DividedPowerScheme.closedFiberι S.S)).pushforward ≪≫
    Functor.isoWhiskerLeft (zariskiComparison S).pushforward
      (zariskiStructureTriangle S) ≪≫
    structureTriangle S

/-- **Stacks Project, Tag 07MG.**  The structure morphisms of the big crystalline sites are
compatible with change of divided power base: the composite
`(X/S)_CRIS ⟶ (Y/S')_CRIS ⟶ Sh((Sch/S')_Zar)` is isomorphic to
`(X/S)_CRIS ⟶ Sh((Sch/S)_Zar) ⟶ Sh((Sch/S')_Zar)`, the square of sites underlying it commuting on
the nose. -/
@[stacks 07MG "the square of structure morphisms, as topoi"]
noncomputable def changeBaseStructureSquare (S S' : GlobalCrystallineSituation.{u})
    (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    ((zariskiOverMorphism f.hom).comp (structureMorphism S)).pushforward ≅
      ((structureMorphism S').comp (changeBaseMorphism S S' f g h)).pushforward :=
  have : (structureFunctor S ⋙ Over.map f.hom).IsCocontinuous (topology S)
      (Scheme.zariskiTopology.over S'.S.scheme) :=
    CategoryTheory.isCocontinuous_comp _ _ _ (Scheme.zariskiTopology.over S.S.scheme)
  have : (changeBase S S' f g h ⋙ structureFunctor S').IsCocontinuous (topology S)
      (Scheme.zariskiTopology.over S'.S.scheme) :=
    CategoryTheory.isCocontinuous_comp _ _ _ (topology S')
  (Functor.sheafPushforwardCocontinuousComp (Type (u + 1)) (topology S)
      (Scheme.zariskiTopology.over S.S.scheme) (Scheme.zariskiTopology.over S'.S.scheme)
      (structureFunctor S) (Over.map f.hom)).symm ≪≫
    Functor.sheafPushforwardCocontinuousCongr (Type (u + 1)) (topology S)
      (Scheme.zariskiTopology.over S'.S.scheme) (structureFunctor S ⋙ Over.map f.hom)
      (changeBase S S' f g h ⋙ structureFunctor S')
      (changeBase_comp_structureFunctor (h := h)).symm ≪≫
    Functor.sheafPushforwardCocontinuousComp (Type (u + 1)) (topology S) (topology S')
      (Scheme.zariskiTopology.over S'.S.scheme) (changeBase S S' f g h) (structureFunctor S')

end Crystalline.GlobalCrystallineSituation

end
