module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# The transition morphism of a quasi-coherent module on a groupoid is invertible

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` and let
`(ℱ, α)` be a quasi-coherent module on it, so that `α : t^*ℱ ⟶ s^*ℱ`. Then `α` is an
isomorphism.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseArrow` is the inversion `i : R ⟶ R` of a
  groupoid in algebraic spaces, read as a morphism of algebraic spaces.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowInverse` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseArrowPair` are the two morphisms
  `(1, i)` and `(i, 1) : R ⟶ R ×_{s, U, t} R`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseArrow_comp_source` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseArrow_comp_target`: the inversion
  exchanges the source and the target.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowInverse_comp_comp` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseArrowPair_comp_comp`: composing an arrow
  with its inverse on either side gives the unit arrow at the target, resp. at the source.
* `AlgebraicGeometry.Space.QuasicoherentModule.isIso_alpha`: the transition morphism of a
  quasi-coherent module on a groupoid in algebraic spaces is an isomorphism.

## Implementation notes

The inversion is `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidInverse`, and the two
composition identities above are its inverse laws
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_inverseLeft` and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_inverseRight` at the generalized
arrow `𝟙 R`.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 077W](https://stacks.math.columbia.edu/tag/077W)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

variable {D : Type*} [Category D]

/-- A left factor of a split monomorphism is a split monomorphism. -/
theorem IsSplitMono.of_comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) [IsSplitMono (f ≫ g)] :
    IsSplitMono f := by
  obtain ⟨r⟩ := IsSplitMono.exists_splitMono (f := f ≫ g)
  exact IsSplitMono.mk' ⟨g ≫ r.retraction, by simpa only [Category.assoc] using r.id⟩

/-- If a composite with an isomorphism on the left is a split monomorphism, so is the middle
factor. -/
private theorem isSplitMono_of_isIso_comp_isSplitMono {W X Y Z : D} (a : W ⟶ X) (f : X ⟶ Y)
    (b : Y ⟶ Z) [IsIso a] [h : IsSplitMono (a ≫ f ≫ b)] : IsSplitMono f := by
  have h' : IsSplitMono (inv a ≫ a ≫ f ≫ b) := inferInstance
  have : IsSplitMono (f ≫ b) := by simpa only [IsIso.inv_hom_id_assoc] using h'
  exact IsSplitMono.of_comp f b

/-- Being a split monomorphism is unchanged by composing with isomorphisms on either side. -/
theorem isSplitMono_iso_comp_iff {W X Y Z : D} (l : W ⟶ X) (f : X ⟶ Y) (r : Y ⟶ Z)
    [IsIso l] [IsIso r] : IsSplitMono (l ≫ f ≫ r) ↔ IsSplitMono f := by
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  exact isSplitMono_of_isIso_comp_isSplitMono l f r

/-- Two isomorphic functors agree on which morphisms they send to split monomorphisms. -/
theorem isSplitMono_map_iff_of_natIso {E : Type*} [Category E] {F H : D ⥤ E} (e : F ≅ H)
    {X Y : D} (f : X ⟶ Y) : IsSplitMono (F.map f) ↔ IsSplitMono (H.map f) := by
  rw [← NatIso.naturality_2 e f, isSplitMono_iso_comp_iff]

/-- Two isomorphic functors agree on which morphisms they send to epimorphisms. -/
theorem epi_map_iff_of_natIso {E : Type*} [Category E] {F H : D ⥤ E} (e : F ≅ H) {X Y : D}
    (f : X ⟶ Y) : Epi (F.map f) ↔ Epi (H.map f) := by
  rw [← NatIso.naturality_2 e f, epi_comp_iff_of_epi, epi_comp_iff_of_isIso]

/-- A morphism which becomes an isomorphism after composing with an isomorphism on the left and
an arbitrary morphism on the right is a split monomorphism. -/
theorem isSplitMono_of_isIso_comp {W X Y Z : D} (a : W ⟶ X) (f : X ⟶ Y) (b : Y ⟶ Z) [IsIso a]
    (h : IsIso (a ≫ f ≫ b)) : IsSplitMono f := by
  have := h
  exact isSplitMono_of_isIso_comp_isSplitMono a f b

/-- A morphism which becomes an isomorphism after composing with arbitrary morphisms on the left
and an isomorphism on the right is an epimorphism. -/
theorem epi_of_isIso_comp {V W X Y Z T : D} (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y) (f : Y ⟶ Z)
    (e : Z ⟶ T) [IsIso e] (h : IsIso (a ≫ b ≫ c ≫ f ≫ e)) : Epi f := by
  have := h
  have : Epi (b ≫ c ≫ f ≫ e) := epi_of_epi a _
  have : Epi (c ≫ f ≫ e) := epi_of_epi b _
  have : Epi (f ≫ e) := epi_of_epi c _
  exact (epi_comp_iff_of_isIso f e).mp inferInstance

/-- If a functor sends a five-fold composite to an isomorphism, the composite of the images of
the factors is an isomorphism. -/
private theorem isIso_map_five {E : Type*} [Category E] (Φ : D ⥤ E)
    {N₀ N₅ M₁ M₂ M₃ M₄ : D} {u : N₀ ⟶ N₅} {a : N₀ ⟶ M₁} {f : M₁ ⟶ M₂} {c : M₂ ⟶ M₃}
    {d : M₃ ⟶ M₄} {e : M₄ ⟶ N₅} (he : u = comp₃ a (comp₃ f c d) e) (h : IsIso (Φ.map u)) :
    IsIso (Φ.map a ≫ Φ.map f ≫ Φ.map c ≫ Φ.map d ≫ Φ.map e) := by
  subst he
  simpa only [comp₃, Functor.map_comp, Category.assoc] using h

/-- A morphism identified with a five-fold composite goes, under a functor, to a split
monomorphism in its second factor, provided the functor sends the first factor to an
isomorphism. -/
theorem isSplitMono_map_of_eq_comp₃_comp₃ {E : Type*} [Category E] (Φ : D ⥤ E)
    {N₀ N₅ M₁ M₂ M₃ M₄ : D} {u : N₀ ⟶ N₅} (a : N₀ ⟶ M₁) (f : M₁ ⟶ M₂) (c : M₂ ⟶ M₃)
    (d : M₃ ⟶ M₄) (e : M₄ ⟶ N₅) (he : u = comp₃ a (comp₃ f c d) e) [IsIso (Φ.map a)]
    (h : IsIso (Φ.map u)) : IsSplitMono (Φ.map f) := by
  exact isSplitMono_of_isIso_comp _ _ _ (isIso_map_five Φ he h)

/-- The epimorphism form of `CategoryTheory.isSplitMono_map_of_eq_comp₃_comp₃`: the functor
sends the fourth factor of the composite to an epimorphism, provided it sends the fifth to an
isomorphism. -/
theorem epi_map_of_eq_comp₃_comp₃ {E : Type*} [Category E] (Φ : D ⥤ E)
    {N₀ N₅ M₁ M₂ M₃ M₄ : D} {u : N₀ ⟶ N₅} (a : N₀ ⟶ M₁) (f : M₁ ⟶ M₂) (c : M₂ ⟶ M₃)
    (d : M₃ ⟶ M₄) (e : M₄ ⟶ N₅) (he : u = comp₃ a (comp₃ f c d) e) [IsIso (Φ.map e)]
    (h : IsIso (Φ.map u)) : Epi (Φ.map d) := by
  exact epi_of_isIso_comp _ _ _ _ _ (isIso_map_five Φ he h)

end CategoryTheory

namespace AlgebraicGeometry

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {A : AlgebraicSpaces 𝒞 S hS}

namespace GroupoidInAlgebraicSpaces

/-- The inversion `i : R ⟶ R` of a groupoid in algebraic spaces, read as a morphism of
algebraic spaces: `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidInverse` in the full
subcategory of algebraic spaces. -/
def inverseArrow (G : GroupoidInAlgebraicSpaces 𝒞 S hS A) : G.arrows ⟶ G.arrows :=
  ObjectProperty.homMk (groupoidInverse G)

/-- The inverse of an arrow has as source the target of the arrow. -/
@[simp]
theorem inverseArrow_comp_source (G : GroupoidInAlgebraicSpaces 𝒞 S hS A) :
    inverseArrow G ≫ G.source = G.target :=
  ObjectProperty.hom_ext _ (groupoidInverse_source G)

/-- The inverse of an arrow has as target the source of the arrow. -/
@[simp]
theorem inverseArrow_comp_target (G : GroupoidInAlgebraicSpaces 𝒞 S hS A) :
    inverseArrow G ≫ G.target = G.source :=
  ObjectProperty.hom_ext _ (groupoidInverse_target G)

/-- The morphism `(1, i) : R ⟶ R ×_{s, U, t} R` pairing an arrow with its inverse. -/
def arrowInverse (G : GroupoidInAlgebraicSpaces 𝒞 S hS A) :
    G.arrows ⟶ AlgebraicSpaces.fiberProduct 𝒞 S hS G.source G.target :=
  ObjectProperty.homMk (pullback.lift (𝟙 G.arrows.obj) (groupoidInverse G)
    (by rw [Category.id_comp, groupoidInverse_target]))

/-- The morphism `(i, 1) : R ⟶ R ×_{s, U, t} R` pairing the inverse of an arrow with the
arrow. -/
def inverseArrowPair (G : GroupoidInAlgebraicSpaces 𝒞 S hS A) :
    G.arrows ⟶ AlgebraicSpaces.fiberProduct 𝒞 S hS G.source G.target :=
  ObjectProperty.homMk (pullback.lift (groupoidInverse G) (𝟙 G.arrows.obj)
    (by rw [Category.id_comp, groupoidInverse_source]))

/-- The first arrow of the pair `(1, i)` is the arrow itself. -/
@[simp]
theorem arrowInverse_comp_firstArrow (G : GroupoidInAlgebraicSpaces 𝒞 S hS A) :
    arrowInverse G ≫ firstArrow G = 𝟙 G.arrows :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- The second arrow of the pair `(1, i)` is the inverse of the arrow. -/
@[simp]
theorem arrowInverse_comp_secondArrow (G : GroupoidInAlgebraicSpaces 𝒞 S hS A) :
    arrowInverse G ≫ secondArrow G = inverseArrow G :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

/-- The first arrow of the pair `(i, 1)` is the inverse of the arrow. -/
@[simp]
theorem inverseArrowPair_comp_firstArrow (G : GroupoidInAlgebraicSpaces 𝒞 S hS A) :
    inverseArrowPair G ≫ firstArrow G = inverseArrow G :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- The second arrow of the pair `(i, 1)` is the arrow itself. -/
@[simp]
theorem inverseArrowPair_comp_secondArrow (G : GroupoidInAlgebraicSpaces 𝒞 S hS A) :
    inverseArrowPair G ≫ secondArrow G = 𝟙 G.arrows :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

/-- An arrow composed after its inverse is the unit arrow at its target. -/
theorem arrowInverse_comp_comp (G : GroupoidInAlgebraicSpaces 𝒞 S hS A) :
    arrowInverse G ≫ G.comp = G.target ≫ identityArrow G := by
  apply ObjectProperty.hom_ext
  have w : (𝟙 G.arrows.obj) ≫ G.source.hom = groupoidInverse G ≫ G.target.hom := by
    rw [Category.id_comp, groupoidInverse_target]
  have h := groupoidCompose_inverseLeft G (𝟙 G.arrows.obj)
  rw [groupoidCompose_congr G _ w rfl (Category.id_comp _)] at h
  change pullback.lift (𝟙 G.arrows.obj) (groupoidInverse G) w ≫ G.comp.hom = _
  refine h.trans ?_
  simp only [identityAfterTarget, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom]

/-- The inverse of an arrow composed after the arrow is the unit arrow at its source. -/
theorem inverseArrowPair_comp_comp (G : GroupoidInAlgebraicSpaces 𝒞 S hS A) :
    inverseArrowPair G ≫ G.comp = G.source ≫ identityArrow G := by
  apply ObjectProperty.hom_ext
  have w : groupoidInverse G ≫ G.source.hom = (𝟙 G.arrows.obj) ≫ G.target.hom := by
    rw [Category.id_comp, groupoidInverse_source]
  have h := groupoidCompose_inverseRight G (𝟙 G.arrows.obj)
  rw [groupoidCompose_congr G _ w (Category.id_comp _) rfl] at h
  change pullback.lift (groupoidInverse G) (𝟙 G.arrows.obj) w ≫ G.comp.hom = _
  refine h.trans ?_
  simp only [identityAfterSource, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom]

end GroupoidInAlgebraicSpaces

namespace Space

open GroupoidInAlgebraicSpaces

variable {G : GroupoidInAlgebraicSpaces 𝒞 S hS A}

/-- Transporting a module along an equality of morphisms is an isomorphism. -/
instance isIso_pullbackTransport {T X : AlgebraicSpaces 𝒞 S hS}
    (M : Modules.{u, u} 𝒞 S hS X.1 X.2) {f g : T ⟶ X} (h : f = g) :
    IsIso (pullbackTransport M h) := by
  rw [show pullbackTransport M h =
    (eqToIso (congrArg (fun k : T ⟶ X => (modulePullback 𝒞 S hS k).obj M) h)).hom from rfl]
  infer_instance

/-- The inverse image of modules along `q` distributes over a five-fold composite. -/
theorem modulePullback_map_comp_five {X Y : AlgebraicSpaces 𝒞 S hS} (q : X ⟶ Y)
    {M₀ M₁ M₂ M₃ M₄ M₅ : Modules.{u, u} 𝒞 S hS Y.1 Y.2}
    (a : M₀ ⟶ M₁) (f : M₁ ⟶ M₂) (c : M₂ ⟶ M₃) (d : M₃ ⟶ M₄) (e : M₄ ⟶ M₅) :
    (modulePullback 𝒞 S hS q).map (a ≫ (f ≫ c ≫ d) ≫ e) =
      (modulePullback 𝒞 S hS q).map a ≫ (modulePullback 𝒞 S hS q).map f ≫
        (modulePullback 𝒞 S hS q).map c ≫ (modulePullback 𝒞 S hS q).map d ≫
        (modulePullback 𝒞 S hS q).map e := by
  simp only [Functor.map_comp, Category.assoc]

/-- The inverse image of modules along `q` distributes over a five-fold composite written as a
`CategoryTheory.comp₃` of a `comp₃`. -/
theorem modulePullback_map_comp₃_comp₃ {X Y : AlgebraicSpaces 𝒞 S hS} (q : X ⟶ Y)
    {M₀ M₁ M₂ M₃ M₄ M₅ : Modules.{u, u} 𝒞 S hS Y.1 Y.2}
    (a : M₀ ⟶ M₁) (f : M₁ ⟶ M₂) (c : M₂ ⟶ M₃) (d : M₃ ⟶ M₄) (e : M₄ ⟶ M₅) :
    (modulePullback 𝒞 S hS q).map (comp₃ a (comp₃ f c d) e) =
      (modulePullback 𝒞 S hS q).map a ≫ (modulePullback 𝒞 S hS q).map f ≫
        (modulePullback 𝒞 S hS q).map c ≫ (modulePullback 𝒞 S hS q).map d ≫
        (modulePullback 𝒞 S hS q).map e :=
  modulePullback_map_comp_five q a f c d e

namespace QuasicoherentModule

/-- Taking the inverse image along `q` of the reindexing of the transition morphism along `f`
is, up to the comparisons of Stacks 03LU, taking its inverse image along `q ≫ f`; so the two
are isomorphisms together. -/
theorem isIso_map_groupoidPullbackTransition_iff (M : QuasicoherentModule 𝒞 S hS G)
    {X Y : AlgebraicSpaces 𝒞 S hS} (q : X ⟶ Y) (f : Y ⟶ G.arrows) :
    IsIso ((modulePullback 𝒞 S hS q).map
        (groupoidPullbackTransition 𝒞 S hS G M.F.obj M.alpha f)) ↔
      IsIso ((modulePullback 𝒞 S hS (q ≫ f)).map M.alpha) := by
  simp only [groupoidPullbackTransition, Functor.map_comp,
    isIso_comp_left_iff, isIso_comp_right_iff]
  exact NatIso.isIso_map_iff (modulePullbackCompIso 𝒞 S hS q f) M.alpha

/-- The split-monomorphism form of
`AlgebraicGeometry.Space.QuasicoherentModule.isIso_map_groupoidPullbackTransition_iff`. -/
theorem isSplitMono_map_groupoidPullbackTransition_iff (M : QuasicoherentModule 𝒞 S hS G)
    {X Y : AlgebraicSpaces 𝒞 S hS} (q : X ⟶ Y) (f : Y ⟶ G.arrows) :
    IsSplitMono ((modulePullback 𝒞 S hS q).map
        (groupoidPullbackTransition 𝒞 S hS G M.F.obj M.alpha f)) ↔
      IsSplitMono ((modulePullback 𝒞 S hS (q ≫ f)).map M.alpha) := by
  simp only [groupoidPullbackTransition, Functor.map_comp, isSplitMono_iso_comp_iff]
  exact isSplitMono_map_iff_of_natIso (modulePullbackCompIso 𝒞 S hS q f) M.alpha

/-- The epimorphism form of
`AlgebraicGeometry.Space.QuasicoherentModule.isIso_map_groupoidPullbackTransition_iff`. -/
theorem epi_map_groupoidPullbackTransition_iff (M : QuasicoherentModule 𝒞 S hS G)
    {X Y : AlgebraicSpaces 𝒞 S hS} (q : X ⟶ Y) (f : Y ⟶ G.arrows) :
    Epi ((modulePullback 𝒞 S hS q).map
        (groupoidPullbackTransition 𝒞 S hS G M.F.obj M.alpha f)) ↔
      Epi ((modulePullback 𝒞 S hS (q ≫ f)).map M.alpha) := by
  simp only [groupoidPullbackTransition, Functor.map_comp]
  rw [epi_comp_iff_of_epi, epi_comp_iff_of_isIso]
  exact epi_map_iff_of_natIso (modulePullbackCompIso 𝒞 S hS q f) M.alpha

/-- The inverse image of the transition morphism along a morphism factoring through the unit
arrow is an isomorphism: this is the unit condition of Stacks 0441. -/
theorem isIso_map_comp_identityArrow (M : QuasicoherentModule 𝒞 S hS G)
    {X : AlgebraicSpaces 𝒞 S hS} (q : X ⟶ G.objects) :
    IsIso ((modulePullback 𝒞 S hS (q ≫ identityArrow G)).map M.alpha) := by
  have h : IsIso (groupoidPullbackTransition 𝒞 S hS G M.F.obj M.alpha (identityArrow G)) := by
    rw [M.unit]; infer_instance
  have h' : IsIso ((modulePullback 𝒞 S hS (identityArrow G)).map M.alpha) := by
    simpa only [groupoidPullbackTransition, transitionReindex, isIso_comp_left_iff,
      isIso_comp_right_iff] using h
  exact (NatIso.isIso_map_iff
    (modulePullbackCompIso 𝒞 S hS q (identityArrow G)) M.alpha).mp (by dsimp; infer_instance)

/-- From the cocycle condition: if the inverse image of the transition along `q ≫ c` is an
isomorphism then its inverse image along `q ≫ pr₁` is a split monomorphism. -/
theorem isSplitMono_map_comp_firstArrow (M : QuasicoherentModule 𝒞 S hS G)
    {X : AlgebraicSpaces 𝒞 S hS} (q : X ⟶ AlgebraicSpaces.fiberProduct 𝒞 S hS G.source G.target)
    (h : IsIso ((modulePullback 𝒞 S hS (q ≫ G.comp)).map M.alpha)) :
    IsSplitMono ((modulePullback 𝒞 S hS (q ≫ firstArrow G)).map M.alpha) :=
  (isSplitMono_map_groupoidPullbackTransition_iff M q (firstArrow G)).mp
    (isSplitMono_map_of_eq_comp₃_comp₃ (modulePullback 𝒞 S hS q)
      (pullbackTransport M.F.obj (comp_comp_target G))
      (groupoidPullbackTransition 𝒞 S hS G M.F.obj M.alpha (firstArrow G))
      (pullbackTransport M.F.obj (firstArrow_comp_source G))
      (groupoidPullbackTransition 𝒞 S hS G M.F.obj M.alpha (secondArrow G))
      (pullbackTransport M.F.obj (comp_comp_source G).symm) M.cocycle
      ((isIso_map_groupoidPullbackTransition_iff M q G.comp).mpr h))

/-- From the cocycle condition: if the inverse image of the transition along `q ≫ c` is an
isomorphism then its inverse image along `q ≫ pr₂` is an epimorphism. -/
theorem epi_map_comp_secondArrow (M : QuasicoherentModule 𝒞 S hS G)
    {X : AlgebraicSpaces 𝒞 S hS} (q : X ⟶ AlgebraicSpaces.fiberProduct 𝒞 S hS G.source G.target)
    (h : IsIso ((modulePullback 𝒞 S hS (q ≫ G.comp)).map M.alpha)) :
    Epi ((modulePullback 𝒞 S hS (q ≫ secondArrow G)).map M.alpha) :=
  (epi_map_groupoidPullbackTransition_iff M q (secondArrow G)).mp
    (epi_map_of_eq_comp₃_comp₃ (modulePullback 𝒞 S hS q)
      (pullbackTransport M.F.obj (comp_comp_target G))
      (groupoidPullbackTransition 𝒞 S hS G M.F.obj M.alpha (firstArrow G))
      (pullbackTransport M.F.obj (firstArrow_comp_source G))
      (groupoidPullbackTransition 𝒞 S hS G M.F.obj M.alpha (secondArrow G))
      (pullbackTransport M.F.obj (comp_comp_source G).symm) M.cocycle
      ((isIso_map_groupoidPullbackTransition_iff M q G.comp).mpr h))

/-- The transition morphism `α : t^*ℱ ⟶ s^*ℱ` of a quasi-coherent module on a groupoid in
algebraic spaces is an isomorphism. -/
@[stacks 077W]
theorem isIso_alpha (M : QuasicoherentModule 𝒞 S hS G) : IsIso M.alpha := by
  have hs : IsSplitMono ((modulePullback 𝒞 S hS (𝟙 G.arrows)).map M.alpha) := by
    have h := isSplitMono_map_comp_firstArrow M (arrowInverse G)
      (by rw [arrowInverse_comp_comp]; exact isIso_map_comp_identityArrow M G.target)
    rwa [arrowInverse_comp_firstArrow] at h
  have he : Epi ((modulePullback 𝒞 S hS (𝟙 G.arrows)).map M.alpha) := by
    have h := epi_map_comp_secondArrow M (inverseArrowPair G)
      (by rw [inverseArrowPair_comp_comp]; exact isIso_map_comp_identityArrow M G.source)
    rwa [inverseArrowPair_comp_secondArrow] at h
  exact (NatIso.isIso_map_iff (modulePullbackIdIso 𝒞 S hS G.arrows) M.alpha).mp
    (isIso_of_epi_of_isSplitMono ((modulePullback 𝒞 S hS (𝟙 G.arrows)).map M.alpha))

end QuasicoherentModule

end Space

end AlgebraicGeometry

end
