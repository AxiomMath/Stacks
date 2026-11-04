module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Cofiltered limits of closed immersions

A morphism of cofiltered inverse systems of schemes with affine transition morphisms whose
components are all closed immersions induces a closed immersion on the limits.

## Main results

* `AlgebraicGeometry.isClosedImmersion_of_isLimit`: the affine case, where the content is that a
  filtered colimit of surjections of rings is a surjection.
* `AlgebraicGeometry.isClosedImmersion_of_isLimit_of_isAffineHom`: the general case, reduced to
  the affine one over the affine opens of a single stage.

## Implementation notes

Both statements are phrased for arbitrary limit cones rather than for `limMap`, so that a caller
who already has a cone in hand need not transport along a comparison isomorphism.

The reduction of the general case to the affine one avoids global sections entirely: the preimage
of an affine open `V` of one stage `Y i₀` is, on both sides, the vertex of the cone
`AlgebraicGeometry.opensCone` over the diagram of preimages of `V`, those preimages are affine,
and the lift produced by the affine case is identified with the restriction of the original
morphism through `AlgebraicGeometry.Scheme.Hom.resLE`.

## References

* [Stacks Project, Tag 0CUH](https://stacks.math.columbia.edu/tag/0CUH)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- **A limit of closed immersions of affine schemes is a closed immersion.** If `η : X ⟶ Y` is
a morphism of cofiltered diagrams of affine schemes whose every component is a closed immersion,
then the induced morphism `lim X ⟶ lim Y` between the limits is a closed immersion.

The mathematical content is that a filtered colimit of surjections of rings is a surjection:
`lim X` and `lim Y` are affine with `Γ(lim X, ⊤) = colim Γ(Xᵢ, ⊤)` and
`Γ(lim Y, ⊤) = colim Γ(Yᵢ, ⊤)`, and every element of `Γ(lim X, ⊤)` comes from some stage. -/
public theorem isClosedImmersion_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {X Y : I ⥤ Scheme.{u}} (η : X ⟶ Y)
    [∀ i, IsAffine (X.obj i)] [∀ i, IsAffine (Y.obj i)]
    {cX : Cone X} (hX : IsLimit cX) {cY : Cone Y} (hY : IsLimit cY)
    (hη : ∀ i, IsClosedImmersion (η.app i)) :
    IsClosedImmersion (hY.lift ((Cone.postcompose η).obj cX)) := by
  have hcX : IsAffine cX.pt := Scheme.isAffine_of_isLimit cX hX
  have hcY : IsAffine cY.pt := Scheme.isAffine_of_isLimit cY hY
  have : IsAffine ((Cone.postcompose η).obj cX).pt := hcX
  refine IsClosedImmersion.of_surjective_of_isAffine _ fun a ↦ ?_
  obtain ⟨i, s, hs⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit X cX hX a
  have := hη i
  obtain ⟨t, ht⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine (η.app i)).2 s
  refine ⟨(cY.π.app i).appTop t, ?_⟩
  have h2 : hY.lift ((Cone.postcompose η).obj cX) ≫ cY.π.app i = cX.π.app i ≫ η.app i :=
    hY.fac ((Cone.postcompose η).obj cX) i
  have h3 : (cY.π.app i).appTop ≫ (hY.lift ((Cone.postcompose η).obj cX)).appTop
      = (η.app i).appTop ≫ (cX.π.app i).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h2]
  have h4 := ConcreteCategory.congr_hom h3 t
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ht] at h4
  rw [h4, hs]

/-- Two restrictions of equal morphisms to the same pair of opens agree. -/
private lemma resLE_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) {U : B.Opens}
    {V : A.Opens} (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    f.resLE U V e = g.resLE U V e' := by
  subst h; rfl

/-- A commuting square of morphisms of schemes restricts to a commuting square of the
restrictions to compatible opens. -/
private lemma resLE_comm {A A' B B' : Scheme.{u}} {a : A ⟶ A'} {b : A ⟶ B} {b' : A' ⟶ B'}
    {c : B ⟶ B'} (h : a ≫ b' = b ≫ c) {U : B'.Opens} {V : A'.Opens} {W : A.Opens}
    {T : B.Opens} (e₁ : W ≤ a ⁻¹ᵁ V) (e₂ : V ≤ b' ⁻¹ᵁ U) (e₃ : W ≤ b ⁻¹ᵁ T)
    (e₄ : T ≤ c ⁻¹ᵁ U) :
    a.resLE V W e₁ ≫ b'.resLE U V e₂ = b.resLE T W e₃ ≫ c.resLE U T e₄ := by
  rw [Scheme.Hom.resLE_comp_resLE, Scheme.Hom.resLE_comp_resLE]
  exact resLE_congr_hom h _ _

/-- Preimages of an open along the two sides of a commuting square agree. -/
private lemma preimage_eq_of_comp_eq {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D}
    {c : A ⟶ C} {d : C ⟶ D} (h : a ≫ b = c ≫ d) (U : D.Opens) :
    a ⁻¹ᵁ (b ⁻¹ᵁ U) = c ⁻¹ᵁ (d ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h]

/-- For a morphism `η : X ⟶ Y` of diagrams of schemes, an index `i₀` and an open `V` of `Y i₀`,
the preimage of `V` in `X j` along `X j ⟶ X i₀ ⟶ Y i₀` agrees with its preimage along
`X j ⟶ Y j ⟶ Y i₀`. -/
private lemma opensDiagram_preimage {I : Type u} [Category.{u} I] {X Y : I ⥤ Scheme.{u}}
    (η : X ⟶ Y) (i₀ : I) (V : (Y.obj i₀).Opens) (j : Over i₀) :
    X.map j.hom ⁻¹ᵁ (η.app i₀ ⁻¹ᵁ V) = η.app j.left ⁻¹ᵁ (Y.map j.hom ⁻¹ᵁ V) := by
  exact preimage_eq_of_comp_eq (η.naturality j.hom) V

/-- The morphism of diagrams `(X j ∩ η i₀ ⁻¹ V) ⟶ (Y j ∩ V)` of preimages of an open `V` of
`Y i₀` induced by a morphism `η : X ⟶ Y` of diagrams of schemes. -/
@[simps]
private noncomputable def opensDiagramMap {I : Type u} [Category.{u} I]
    {X Y : I ⥤ Scheme.{u}} (η : X ⟶ Y) (i₀ : I) (V : (Y.obj i₀).Opens) :
    opensDiagram X i₀ (η.app i₀ ⁻¹ᵁ V) ⟶ opensDiagram Y i₀ V where
  app j := (η.app j.left).resLE _ _ (opensDiagram_preimage η i₀ V j).le
  naturality _j _k g := resLE_comm (η.naturality g.left) _ _ _ _

/-- **A limit of closed immersions is a closed immersion.** If `η : X ⟶ Y` is a morphism of
cofiltered inverse systems of schemes with affine transition morphisms whose every component is
a closed immersion, then the induced morphism `lim X ⟶ lim Y` is a closed immersion.

The general case is reduced to the affine case `isClosedImmersion_of_isLimit` by restricting to
the affine opens `V` of a single stage `Y i₀`: the preimage of `V` in `lim Y` is the limit of the
preimages of `V` in the `Y j`, which are affine, and likewise on the `X` side. -/
public theorem isClosedImmersion_of_isLimit_of_isAffineHom
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {X Y : I ⥤ Scheme.{u}} (η : X ⟶ Y)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f)]
    {cX : Cone X} (hX : IsLimit cX) {cY : Cone Y} (hY : IsLimit cY)
    (hη : ∀ i, IsClosedImmersion (η.app i)) :
    IsClosedImmersion (hY.lift ((Cone.postcompose η).obj cX)) := by
  set f := hY.lift ((Cone.postcompose η).obj cX)
  have h2 : ∀ i, f ≫ cY.π.app i = cX.π.app i ≫ η.app i := fun i ↦
    hY.fac ((Cone.postcompose η).obj cX) i
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun V : (Y.obj i₀).affineOpens ↦ cY.π.app i₀ ⁻¹ᵁ V.1) ?_ fun V ↦ ?_
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  have hVa : IsAffineOpen V.1 := V.2
  have := hη i₀
  have : ∀ j : Over i₀, IsAffine ((opensDiagram X i₀ (η.app i₀ ⁻¹ᵁ V.1)).obj j) := fun j ↦
    (hVa.preimage (η.app i₀)).preimage (X.map j.hom)
  have : ∀ j : Over i₀, IsAffine ((opensDiagram Y i₀ V.1).obj j) := fun j ↦
    hVa.preimage (Y.map j.hom)
  have hη' : ∀ j : Over i₀, IsClosedImmersion ((opensDiagramMap η i₀ V.1).app j) := fun j ↦ by
    rw [opensDiagramMap_app]
    refine (Scheme.Hom.resLE_congr (η.app j.left) le_rfl rfl
      (opensDiagram_preimage η i₀ V.1 j).symm @IsClosedImmersion).mp ?_
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact IsZariskiLocalAtTarget.restrict (hη j.left) _
  have hUeq := preimage_eq_of_comp_eq (h2 i₀) V.1
  have hY' := isLimitOpensCone Y cY hY i₀ V.1
  have key := isClosedImmersion_of_isLimit (opensDiagramMap η i₀ V.1)
    (isLimitOpensCone X cX hX i₀ (η.app i₀ ⁻¹ᵁ V.1)) hY' hη'
  have hlift : hY'.lift ((Cone.postcompose (opensDiagramMap η i₀ V.1)).obj
      (opensCone X cX i₀ (η.app i₀ ⁻¹ᵁ V.1))) = f.resLE _ _ hUeq.ge :=
    hY'.hom_ext fun j ↦ (hY'.fac _ j).trans (resLE_comm (h2 j.left).symm _ _ _ _)
  rw [hlift] at key
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact (Scheme.Hom.resLE_congr f le_rfl rfl hUeq @IsClosedImmersion).mpr key

end AlgebraicGeometry

end
