module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CategoryOfPrincipalHomogeneousSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence

/-!
# `G-Torsors` is `G-Principal` when `G` is flat and locally of finite presentation

Let `B` be an algebraic space over a scheme `S` and let `G` be a group algebraic space over `B`.
The categories `G-Torsors` of Stacks 04UR and `G-Principal` of Stacks 04UN differ only in the
topology for which the total space of an object is required to be locally trivial: fppf for the
first, fpqc for the second.  An fppf covering is an fpqc covering (Stacks 0DFQ), so there is a
canonical functor `G-Torsors ⥤ G-Principal` over the big fppf site of `S`, and it is always
fully faithful.

**Stacks 0CQJ**, last sentence: if `G ⟶ B` is flat and locally of finite presentation then that
functor is an equivalence over the site, because then every principal homogeneous space is
already an fppf torsor.  The reason is that a principal homogeneous space `X` over `B` is itself
an fppf covering of `B` which trivializes `X`: the shear map identifies `G ×_B X` with `X ×_B X`,
so `X ⟶ B` inherits from `G ⟶ B` every property which is stable under base change and local on
the base for the fpqc topology — surjectivity (Stacks 041Q), flatness (Stacks 041W) and local
finite presentation (Stacks 041T) — and `X ⟶ B` is trivialized by itself by the diagonal.

## Main definitions

* `AlgebraicGeometry.Space.TorsorsFor.ofLe`: the functor between two categories of torsors
  induced by weakening the trivializing covering property.
* `AlgebraicGeometry.Space.FppfTorsors.toPrincipal`: the canonical functor
  `G-Torsors ⥤ G-Principal`.

## Main results

* `AlgebraicGeometry.Space.isFppfTorsor_of_isPrincipalHomogeneousSpace`: a principal homogeneous
  space under a flat group algebraic space locally of finite presentation is an fppf torsor.
* `AlgebraicGeometry.Space.FppfTorsors.isEquivalenceOverPrincipal`: the last clause of
  **Stacks 0CQJ**, that the canonical functor `G-Torsors ⥤ G-Principal` is an equivalence over
  the big fppf site of `S` when `G ⟶ B` is flat and locally of finite presentation.

## Implementation notes

Nothing here carries the tag `0CQJ` itself. The equivalence proved here is the last clause of
that lemma, and it is assembled with the other legs (`[B/G] ≌ [[B/G]] ≌ G-Torsors ≌
𝒢/ℬ-Torsors`) in `AlgebraicGeometry.Space.classifyingStackEquivalences`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/ClassifyingStackEquivalences.lean`.

`AlgebraicGeometry.Space.TorsorsFor` already carries the trivializing covering property as an
argument, so the functor `G-Torsors ⥤ G-Principal` changes nothing but the proof field of an
object: it is the identity on the base, the classifying morphism, the total space and the
action, and the identity on both components of a morphism.  That makes it fully faithful and
strictly a functor over the site without any computation, and leaves exactly one thing to prove,
namely that it hits every object up to a vertical isomorphism.  Being surjective on objects on
the nose, the vertical isomorphism supplied is an identity.

The source argues local triviality of `X ⟶ U` by choosing a scheme `W` with `W ⟶ X` surjective
étale and using `{W ⟶ U}`; here a covering family of the fppf topology on algebraic spaces is
already a family of algebraic spaces (`AlgebraicGeometry.Space.IsFppfCovering`), so the
one-member family `{X ⟶ U}` serves directly and no étale chart of `X` is needed.

## References

* [Stacks Project, Tag 0CQJ](https://stacks.math.columbia.edu/tag/0CQJ)
* [Stacks Project, Tag 04UN](https://stacks.math.columbia.edu/tag/04UN)
* [Stacks Project, Tag 04UR](https://stacks.math.columbia.edu/tag/04UR)
* [Stacks Project, Tag 041Q](https://stacks.math.columbia.edu/tag/041Q)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-! ### Weakening the trivializing covering property -/

namespace TorsorsFor

variable (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB)
  {P Q : CoveringPredicate 𝒞 S hS}

/-- The functor between categories of torsors induced by weakening the trivializing covering
property: a torsor trivialized by a family satisfying `P` is trivialized by that same family,
which satisfies `Q`.  The base, the classifying morphism, the total space and the action are
unchanged, and so are both components of a morphism. -/
def ofLe (hPQ : ∀ T I Bᵢ f, P T I Bᵢ f → Q T I Bᵢ f) :
    TorsorsFor hB G P ⥤ TorsorsFor hB G Q where
  obj T :=
    { base := T.base
      sec := T.sec
      total := T.total
      isAlgebraicSpace := T.isAlgebraicSpace
      action := T.action
      isTorsor := by
        obtain ⟨hpseudo, I, Bᵢ, f, hBᵢ, hP, hsec⟩ := T.isTorsor
        exact ⟨hpseudo, I, Bᵢ, f, hBᵢ, hPQ _ _ _ _ hP, hsec⟩ }
  map φ :=
    { base := φ.base
      comp_sec := φ.comp_sec
      map := φ.map
      isPullback := φ.isPullback
      smul_comp := φ.smul_comp }
  map_id _ := Hom.ext rfl rfl
  map_comp _ _ := Hom.ext rfl rfl

variable {hB G}

/-- The functor `ofLe` does not change the base of a torsor. -/
@[simp]
theorem ofLe_obj_base (hPQ : ∀ T I Bᵢ f, P T I Bᵢ f → Q T I Bᵢ f) (T : TorsorsFor hB G P) :
    ((ofLe hB G hPQ).obj T).base = T.base :=
  rfl

/-- The functor `ofLe` does not change the base component of a morphism of torsors. -/
@[simp]
theorem ofLe_map_base (hPQ : ∀ T I Bᵢ f, P T I Bᵢ f → Q T I Bᵢ f) {T T' : TorsorsFor hB G P}
    (φ : T ⟶ T') : ((ofLe hB G hPQ).map φ).base = φ.base :=
  rfl

/-- Weakening the trivializing covering property does not move the base, so the functor it
induces is strictly a functor over the big fppf site of `S`. -/
theorem ofLe_comp_projection (hPQ : ∀ T I Bᵢ f, P T I Bᵢ f → Q T I Bᵢ f) :
    ofLe hB G hPQ ⋙ projection hB G Q = projection hB G P :=
  rfl

/-- The functor `ofLe` induced by weakening the trivializing covering property is full. -/
instance ofLe_full (hPQ : ∀ T I Bᵢ f, P T I Bᵢ f → Q T I Bᵢ f) : (ofLe hB G hPQ).Full where
  map_surjective {_ _} φ :=
    ⟨{ base := φ.base
       comp_sec := φ.comp_sec
       map := φ.map
       isPullback := φ.isPullback
       smul_comp := φ.smul_comp }, Hom.ext rfl rfl⟩

/-- The functor `ofLe` induced by weakening the trivializing covering property is faithful. -/
instance ofLe_faithful (hPQ : ∀ T I Bᵢ f, P T I Bᵢ f → Q T I Bᵢ f) :
    (ofLe hB G hPQ).Faithful where
  map_injective {_ _ φ ψ} h :=
    Hom.ext (show φ.base = ψ.base from congrArg (fun k => k.base) h)
      (show φ.map = ψ.map from congrArg (fun k => k.map) h)

end TorsorsFor

/-! ### A principal homogeneous space under a flat group of finite presentation -/

section Principal

universe u₁ v₁ w

/-- A property of morphisms which is stable under base change and local at the target for a
precoverage `K` holds for `f : X ⟶ Y` as soon as it holds for the second projection of
`X ×_Y X` and `f` admits a section after each member of a `K`-covering family of `Y`: the base
change of `f` to such a member is a base change of `pullback.snd f f` along that section. -/
private theorem property_of_local_sections {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
    (P : MorphismProperty C) (K : Precoverage C)
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget K]
    {X Y : C} (f : X ⟶ Y) {I : Type w} (U : I → C) (g : ∀ i, U i ⟶ Y)
    (hg : Presieve.ofArrows U g ∈ K Y)
    (hs : ∀ i, ∃ s : U i ⟶ X, s ≫ f = g i)
    (hf : P (pullback.snd f f)) : P f := by
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hg
  rintro _ _ _ ⟨i⟩
  obtain ⟨s, hs⟩ := hs i
  have sq := (IsPullback.of_hasPullback (pullback.snd f f) s).paste_horiz
    (IsPullback.of_hasPullback f f)
  rw [hs] at sq
  rw [← sq.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp P _ _ (P.pullback_snd _ _ hf)

/-- A section of the restriction of `X` along `f : F ⟶ B` is a factorization of `f` through the
structure morphism of `X`. -/
private theorem section_factor {F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (X : Over B) (f : F ⟶ B) (s : 𝟙_ (Over F) ⟶ (Over.pullback f).obj X) :
    ∃ t : F ⟶ X.left, t ≫ X.hom = f := by
  refine ⟨s.left ≫ pullback.fst X.hom f, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    show s.left ≫ pullback.snd X.hom f = 𝟙 F from s.w, Category.id_comp]

/-- The second projection of `X ×_B X` is, through the shear map, a base change of `G ⟶ B`, so
it inherits from `G ⟶ B` any property stable under base change. -/
private theorem property_selfPullback (hB : IsAlgebraicSpace 𝒞 S hS B) (G X : Over B) [GrpObj G]
    [ModObj G X] (hG : IsAlgebraicSpace 𝒞 S hS G.left) (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (hpseudo : AlgebraicGeometry.IsPseudoTorsor G X)
    (P : MorphismProperty (AlgebraicSpaces 𝒞 S hS)) [P.IsStableUnderBaseChange]
    (hP : P (ObjectProperty.homMk G.hom : ⟨G.left, hG⟩ ⟶ ⟨B, hB⟩)) :
    P (pullback.snd (ObjectProperty.homMk X.hom : ⟨X.left, hX⟩ ⟶ ⟨B, hB⟩)
      (ObjectProperty.homMk X.hom : ⟨X.left, hX⟩ ⟶ ⟨B, hB⟩)) := by
  let G₀ : AlgebraicSpaces 𝒞 S hS := ⟨G.left, hG⟩
  let X₀ : AlgebraicSpaces 𝒞 S hS := ⟨X.left, hX⟩
  let A : AlgebraicSpaces 𝒞 S hS :=
    ⟨(G ⊗ X).left, AlgebraicGeometry.isAlgebraicSpace_pullback 𝒞 S hS G.hom X.hom hG hX hB⟩
  let C : AlgebraicSpaces 𝒞 S hS :=
    ⟨(X ⊗ X).left, AlgebraicGeometry.isAlgebraicSpace_pullback 𝒞 S hS X.hom X.hom hX hX hB⟩
  let pA : A ⟶ X₀ := ObjectProperty.homMk (CartesianMonoidalCategory.snd G X).left
  let pC : C ⟶ X₀ := ObjectProperty.homMk (CartesianMonoidalCategory.snd X X).left
  have hpA : P pA := MorphismProperty.of_isPullback
    (AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct 𝒞 S hS
      (ObjectProperty.homMk G.hom : G₀ ⟶ ⟨B, hB⟩)
      (ObjectProperty.homMk X.hom : X₀ ⟶ ⟨B, hB⟩)) hP
  have : IsIso (ModObj.leftSMul G X) := hpseudo
  let e : A ≅ C := ObjectProperty.isoMk _
    ((Over.forget B).mapIso (asIso (ModObj.leftSMul G X)))
  have he : e.hom ≫ pC = pA :=
    ObjectProperty.hom_ext _ (congrArg Over.Hom.left (ModObj.leftSMul_snd (M := G) (X := X)))
  have hpc : P pC := by
    have he' : e.inv ≫ pA = pC := by rw [← he, Iso.inv_hom_id_assoc]
    rw [← he']
    exact MorphismProperty.RespectsIso.precomp P _ _ hpA
  have sq := AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct 𝒞 S hS
    (ObjectProperty.homMk X.hom : X₀ ⟶ ⟨B, hB⟩)
    (ObjectProperty.homMk X.hom : X₀ ⟶ ⟨B, hB⟩)
  rw [← sq.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp P _ _ hpc

/-- The structure morphism of a principal homogeneous space inherits from that of the acting
group every property which is stable under base change and local at the target for the fpqc
topology: the trivializing fpqc covering gives sections, and the second projection of the
self-fibre-product is a base change of `G ⟶ B` by the shear map. -/
@[sga "3 XII 7.13" "partial"]
private theorem principal_property (hB : IsAlgebraicSpace 𝒞 S hS B) (G X : Over B) [GrpObj G]
    [ModObj G X] (hG : IsAlgebraicSpace 𝒞 S hS G.left) (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (hprincipal : IsPrincipalHomogeneousSpace 𝒞 S hS B hB G X hG hX)
    (P : MorphismProperty (AlgebraicSpaces 𝒞 S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Topology.fpqc.precoverage.{u, u + 1} 𝒞 S hS)]
    (hP : P (ObjectProperty.homMk G.hom : ⟨G.left, hG⟩ ⟶ ⟨B, hB⟩)) :
    P (ObjectProperty.homMk X.hom : ⟨X.left, hX⟩ ⟶ ⟨B, hB⟩) := by
  obtain ⟨hpseudo, I, Y, f, hY, hcover, hsections⟩ := hprincipal
  let Y₀ : I → AlgebraicSpaces 𝒞 S hS := fun i => ⟨Y i, hY i⟩
  let f₀ : ∀ i, Y₀ i ⟶ (⟨B, hB⟩ : AlgebraicSpaces 𝒞 S hS) := fun i => ObjectProperty.homMk (f i)
  refine property_of_local_sections P (Topology.fpqc.precoverage 𝒞 S hS)
    (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpaces 𝒞 S hS) ⟶ ⟨B, hB⟩) Y₀ f₀
    ⟨I, Y₀, f₀, rfl, hB, hY, hcover⟩ (fun i => ?_) (property_selfPullback hB G X hG hX hpseudo P hP)
  obtain ⟨t, ht⟩ := section_factor X (f i) (hsections i).some
  exact ⟨ObjectProperty.homMk t, ObjectProperty.hom_ext _ ht⟩

/-- A morphism of presheaves with a section is surjective on points. -/
private theorem surjective_of_section {X Y : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) : IsSurjective 𝒞 S hS f := by
  have hc : pointsMap 𝒞 S hS Y (s ≫ f) =
      pointsMap 𝒞 S hS X f ∘ pointsMap 𝒞 S hS Y s := by
    funext x
    induction x using Quot.inductionOn with | h p => rfl
  have hi : pointsMap 𝒞 S hS Y (𝟙 Y) = id := by
    funext x
    induction x using Quot.inductionOn with | h p => rfl
  intro y
  exact ⟨pointsMap 𝒞 S hS Y s y, by
    simpa only [hs, hi, Function.comp_apply, id_eq] using congrFun hc.symm y⟩

/-- **Stacks 0CQJ**, the last step of the proof.  A principal homogeneous space under a group
algebraic space which is flat and locally of finite presentation over the base is an fppf
torsor: its own structure morphism is then a surjective, flat, locally finitely presented
morphism, so the one-member family consisting of it is an fppf covering of the base, and the
diagonal is a section of the restriction of the space to itself. -/
theorem isFppfTorsor_of_isPrincipalHomogeneousSpace (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G X : Over B) [GrpObj G] [ModObj G X] (hG : IsAlgebraicSpace 𝒞 S hS G.left)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (hprincipal : IsPrincipalHomogeneousSpace 𝒞 S hS B hB G X hG hX)
    (hflat : IsFlat 𝒞 S hS G.hom)
    (hlfp : IsLocallyOfFinitePresentation 𝒞 S hS G.hom) :
    IsFppfTorsor 𝒞 S hS B hB G X hG hX := by
  let P₁ : MorphismProperty (AlgebraicSpaces 𝒞 S hS) :=
    fun _ _ f => IsSurjective 𝒞 S hS f.hom
  let P₂ : MorphismProperty (AlgebraicSpaces 𝒞 S hS) := fun _ _ f => IsFlat 𝒞 S hS f.hom
  let P₃ : MorphismProperty (AlgebraicSpaces 𝒞 S hS) :=
    fun _ _ f => IsLocallyOfFinitePresentation 𝒞 S hS f.hom
  have : P₁.IsStableUnderBaseChange := surjectiveMorphismProperty_isStableUnderBaseChange 𝒞 S hS
  have : P₂.IsStableUnderBaseChange := isFlat_isStableUnderBaseChange 𝒞 S hS
  have : P₃.IsStableUnderBaseChange :=
    isLocallyOfFinitePresentation_isStableUnderBaseChange 𝒞 S hS
  have : (P₂ ⊓ P₃).IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf (P := P₂) (Q := P₃)
  have : (P₁ ⊓ (P₂ ⊓ P₃)).IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf (P := P₁) (Q := P₂ ⊓ P₃)
  have hsurj : IsSurjective 𝒞 S hS G.hom :=
    surjective_of_section G.hom (η[G]).left (η[G]).w
  have hP := principal_property hB G X hG hX hprincipal (P₁ ⊓ (P₂ ⊓ P₃)) ⟨hsurj, hflat, hlfp⟩
  refine ⟨hprincipal.1, PUnit.{u + 2}, (fun _ => X.left), (fun _ => X.hom), (fun _ => hX), ?_, ?_⟩
  · refine ⟨hB, (fun _ => hX), (fun _ => hP.2.1), (fun _ => hP.2.2), ?_⟩
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨x, hx⟩ := hP.1 y
    exact ⟨PUnit.unit, x, hx⟩
  · exact fun _ => ⟨Over.homMk (pullback.lift (𝟙 X.left) (𝟙 X.left) (by simp))
      (pullback.lift_snd (𝟙 X.left) (𝟙 X.left) (by simp))⟩

end Principal

namespace FppfTorsors

variable (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB)

/-- **Stacks 0CQJ.** The canonical functor `G-Torsors ⥤ G-Principal`: an fppf torsor is a
principal homogeneous space, because an fppf covering is an fpqc covering. -/
def toPrincipal : FppfTorsors hB G ⥤ PrincipalHomogeneousSpaces hB G :=
  TorsorsFor.ofLe hB G fun _ _ Bᵢ f h => isFpqcCovering_of_isFppfCovering 𝒞 S hS Bᵢ f h

/-- The canonical functor `G-Torsors ⥤ G-Principal` lies over the big fppf site of `S`. -/
theorem toPrincipal_comp_projection :
    toPrincipal hB G ⋙ PrincipalHomogeneousSpaces.projection hB G = projection hB G :=
  rfl

/-- The canonical functor `G-Torsors ⥤ G-Principal` is full. -/
instance : (toPrincipal hB G).Full := TorsorsFor.ofLe_full _

/-- The canonical functor `G-Torsors ⥤ G-Principal` is faithful. -/
instance : (toPrincipal hB G).Faithful := TorsorsFor.ofLe_faithful _

section FlatFinitePresentation

variable (hflat : IsFlat 𝒞 S hS G.obj.X.hom)
  (hlfp : IsLocallyOfFinitePresentation 𝒞 S hS G.obj.X.hom)

/-- The acting group `G_U` of an object of a category of torsors is the base change of `G` along
the classifying morphism, so it inherits from `G ⟶ B` any property stable under base change. -/
private theorem property_group (P : MorphismProperty (AlgebraicSpaces 𝒞 S hS))
    [P.IsStableUnderBaseChange] {Q : CoveringPredicate 𝒞 S hS} (T : TorsorsFor hB G Q)
    (hP : P (ObjectProperty.homMk G.obj.X.hom :
      (⟨G.obj.X.left, G.property⟩ : AlgebraicSpaces 𝒞 S hS) ⟶ ⟨B, hB⟩)) :
    P (ObjectProperty.homMk T.group.hom :
      (⟨T.group.left, (fppfPullbackGroup hB G T.base T.sec).property⟩ :
        AlgebraicSpaces 𝒞 S hS) ⟶ ⟨yoneda.obj T.base, isAlgebraicSpace_yoneda 𝒞 S hS T.base⟩) :=
  MorphismProperty.of_isPullback
    (AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct 𝒞 S hS
      (ObjectProperty.homMk G.obj.X.hom :
        (⟨G.obj.X.left, G.property⟩ : AlgebraicSpaces 𝒞 S hS) ⟶ ⟨B, hB⟩)
      (ObjectProperty.homMk T.sec :
        (⟨yoneda.obj T.base, isAlgebraicSpace_yoneda 𝒞 S hS T.base⟩ :
          AlgebraicSpaces 𝒞 S hS) ⟶ ⟨B, hB⟩)) hP

include hflat in
/-- The acting group `G_U` of an object of a category of torsors is the base change of `G` along
the classifying morphism, so it is flat whenever `G ⟶ B` is. -/
theorem isFlat_group {P : CoveringPredicate 𝒞 S hS} (T : TorsorsFor hB G P) :
    IsFlat 𝒞 S hS T.group.hom :=
  have := isFlat_isStableUnderBaseChange 𝒞 S hS
  property_group hB G (fun _ _ f => IsFlat 𝒞 S hS f.hom) T hflat

include hlfp in
/-- The acting group `G_U` of an object of a category of torsors is the base change of `G` along
the classifying morphism, so it is locally of finite presentation whenever `G ⟶ B` is. -/
theorem isLocallyOfFinitePresentation_group {P : CoveringPredicate 𝒞 S hS}
    (T : TorsorsFor hB G P) : IsLocallyOfFinitePresentation 𝒞 S hS T.group.hom :=
  have := isLocallyOfFinitePresentation_isStableUnderBaseChange 𝒞 S hS
  property_group hB G (fun _ _ f => IsLocallyOfFinitePresentation 𝒞 S hS f.hom) T hlfp

include hflat hlfp

/-- The object of `G-Torsors` underlying an object of `G-Principal`, when `G ⟶ B` is flat and
locally of finite presentation: the acting group `G_U` is then a base change of `G`, hence again
flat and locally of finite presentation, so the total space is already an fppf torsor. -/
def ofPrincipal (T : PrincipalHomogeneousSpaces hB G) : FppfTorsors hB G where
  base := T.base
  sec := T.sec
  total := T.total
  isAlgebraicSpace := T.isAlgebraicSpace
  action := T.action
  isTorsor := isFppfTorsor_of_isPrincipalHomogeneousSpace
    (isAlgebraicSpace_yoneda 𝒞 S hS T.base) T.group T.total
    (fppfPullbackGroup hB G T.base T.sec).property T.isAlgebraicSpace T.isPrincipal
    (isFlat_group hB G hflat T) (isLocallyOfFinitePresentation_group hB G hlfp T)

/-- The canonical functor `G-Torsors ⥤ G-Principal` returns an object of `G-Principal`
unchanged: the two objects differ only in the proposition they carry about the total space. -/
theorem toPrincipal_obj_ofPrincipal (T : PrincipalHomogeneousSpaces hB G) :
    (toPrincipal hB G).obj (ofPrincipal hB G hflat hlfp T) = T :=
  rfl

/-- When `G ⟶ B` is flat and locally of finite presentation, every object of `G-Principal` is
in the image of the canonical functor from `G-Torsors` on the nose, so the vertical isomorphism
witnessing essential surjectivity on fibres is an identity. -/
theorem hasVerticalPreimages_toPrincipal :
    Functor.HasVerticalPreimages (projection hB G)
      (PrincipalHomogeneousSpaces.projection hB G) (toPrincipal hB G) := by
  intro T
  have hobj := toPrincipal_obj_ofPrincipal hB G hflat hlfp T
  refine ⟨ofPrincipal hB G hflat hlfp T, rfl, eqToIso hobj.symm, ?_⟩
  refine IsHomLift.of_fac' _ _ _ rfl
    (congrArg (PrincipalHomogeneousSpaces.projection hB G).obj hobj) ?_
  rw [eqToIso.hom, eqToHom_map]
  simp

/-- **Stacks 0CQJ**, the last clause.  If `G ⟶ B` is flat and locally of finite presentation
then the canonical functor `G-Torsors ⥤ G-Principal` is an equivalence over the big fppf site
of `S`: it is fully faithful because it changes nothing but a proof field, and essentially
surjective because a principal homogeneous space under such a `G` is already an fppf torsor. -/
def isEquivalenceOverPrincipal :
    Functor.IsEquivalenceOver (projection hB G) (PrincipalHomogeneousSpaces.projection hB G)
      (toPrincipal hB G) :=
  Functor.isEquivalenceOver_of_exists_vertical_iso (toPrincipal_comp_projection hB G)
    (hasVerticalPreimages_toPrincipal hB G hflat hlfp)

end FlatFinitePresentation

end FppfTorsors

end AlgebraicGeometry.Space

end
