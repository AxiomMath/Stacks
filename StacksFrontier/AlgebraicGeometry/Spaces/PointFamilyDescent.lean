module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationAtlasDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationAtlasFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensorComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent

/-!
# Morphisms of quasi-coherent modules from their restrictions to the scheme points

Let `X` be an algebraic space and `G`, `H` quasi-coherent `𝒪_X`-modules.  A morphism `g : G ⟶ H`
restricts, along every scheme point `x : T ⟶ X` (an object `T` of the site), to a morphism
`x^*g : x^*G ⟶ x^*H`, and these restrictions are compatible: for `τ : T' ⟶ T`, the inverse image
`τ^*(x^*g)` is `(x ∘ τ)^*g` through the comparison `τ^*x^* ≅ (x ∘ τ)^*` of Stacks 03LU.

Conversely, **a family `χ_x : x^*G ⟶ x^*H` indexed by the scheme points of `X` and compatible in
this sense comes from a morphism `g : G ⟶ H`**: on the atlas `φ : U ⟶ X` of a presentation
`X = U/R`, the compatibility along the two projections `R ⇉ U` is the compatibility of `χ_φ` with
the canonical transition morphisms, so `χ_φ` descends (Stacks 03M3,
`AlgebraicGeometry.Space.presentationAtlasDescendedHom`), and the restriction of `g` to the atlas
is `χ_φ`, which determines `g`.

This is the form in which a morphism of modules on an algebraic space is built from its
restrictions to scheme points, as the source does for the map `θ` of Stacks 0D2Z.

## Main definitions

* `AlgebraicGeometry.Space.PullbackTransportSquare`: the square of two morphisms between inverse
  images along `x` and `x' = f ≫ x`.
* `AlgebraicGeometry.Space.PointFamilyNatural`: the compatibility of a family of morphisms
  indexed by the scheme points.
* `AlgebraicGeometry.Space.pointFamilyDescendedHom`: **the morphism `G ⟶ H` of a compatible
  family.**

## Main results

* `AlgebraicGeometry.Space.pullbackTransportSquare_modulePullback_map`,
  `AlgebraicGeometry.Space.pointFamilyNatural_modulePullback_map`: the restrictions of a morphism
  form a compatible family.
* `AlgebraicGeometry.Space.modulePullback_map_eq_iff_of_pullbackTransportSquare`: along a square,
  a morphism restricts to the member at `x'` exactly when it does so after pulling back the member
  at `x`.
* `AlgebraicGeometry.Space.transitionCommutes_of_pullbackTransportSquares`: two squares along the
  target and the source of a groupoid give the compatibility of Stacks 03M3.
* `AlgebraicGeometry.Space.transitionCommutes_of_pointFamilyNatural`: a compatible family, read on
  the atlas of a presentation, carries the canonical transition morphisms to each other.
* `AlgebraicGeometry.Space.modulePullback_map_presentationAtlas_pointFamilyDescendedHom`: the
  restriction of the morphism of a compatible family to the atlas is the member at the atlas;
  `AlgebraicGeometry.Space.pointFamilyDescendedHom_unique`: that determines it.
* `AlgebraicGeometry.Space.modulePullback_map_pointHom_pointFamilyDescendedHom`: **the restriction
  of the morphism of a compatible family to every scheme point is the member there**;
  `AlgebraicGeometry.Space.eq_pointFamilyDescendedHom_of_modulePullback_map_pointHom`: a morphism
  with these restrictions is the morphism of the family.

## Implementation notes

The squares are a structure (`AlgebraicGeometry.Space.PullbackTransportSquare`) rather than a
`Prop`-valued definition: the body of a definition has its nested proofs (the algebraicity of the
spaces inside the categories of modules) abstracted into auxiliary lemmas, and comparing that
body with the same equation written in a statement exhausts the kernel.  The represented spaces
of the scheme points are passed explicitly as `AlgebraicGeometry.Space.yonedaSpace`, the spelling
of the domain of `AlgebraicGeometry.Space.pointHom`.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

section Generic

variable {Y Z : AlgebraicSpaces B S hS}

/-- **The square of a morphism `c : x^*G ⟶ x^*H` and a morphism `c' : x'^*G ⟶ x'^*H` along
`f : Z ⟶ Y` with `f ≫ x = x'`**: `f^*c` is `c'` through the comparison `f^*x^* ≅ (f ≫ x)^*` of
Stacks 03LU and the transport along `f ≫ x = x'`. -/
structure PullbackTransportSquare (f : Z ⟶ Y) (x : Y ⟶ X) (x' : Z ⟶ X) (h : f ≫ x = x')
    (G H : Modules.{u, u} B S hS X.1 X.2)
    (c : (modulePullback B S hS x).obj G ⟶ (modulePullback B S hS x).obj H)
    (c' : (modulePullback B S hS x').obj G ⟶ (modulePullback B S hS x').obj H) : Prop where
  /-- The square. -/
  eq : (modulePullback B S hS f).map c ≫
      ((modulePullbackCompIso B S hS f x).hom.app H ≫ pullbackTransport H h) =
    ((modulePullbackCompIso B S hS f x).hom.app G ≫ pullbackTransport G h) ≫ c'

/-- **The inverse images of a morphism `g : G ⟶ H` along `x` and along `x' = f ≫ x` form a
square** (the naturality of the comparison of Stacks 03LU). -/
theorem pullbackTransportSquare_modulePullback_map (f : Z ⟶ Y) (x : Y ⟶ X) (x' : Z ⟶ X)
    (h : f ≫ x = x') {G H : Modules.{u, u} B S hS X.1 X.2} (g : G ⟶ H) :
    PullbackTransportSquare f x x' h G H ((modulePullback B S hS x).map g)
      ((modulePullback B S hS x').map g) := by
  refine ⟨?_⟩
  subst h
  have h1 := (modulePullbackCompIso B S hS f x).hom.naturality g
  simp only [Functor.comp_map] at h1
  simp only [pullbackTransport, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact h1

/-- Given a square of `c` and `c'` along `f`, a morphism `g : G ⟶ H` has inverse image `c'` along
`x'` exactly when its inverse image along `x`, pulled back along `f`, is `f^*c`. -/
theorem modulePullback_map_eq_iff_of_pullbackTransportSquare (f : Z ⟶ Y) (x : Y ⟶ X)
    (x' : Z ⟶ X) (h : f ≫ x = x') {G H : Modules.{u, u} B S hS X.1 X.2}
    {c : (modulePullback B S hS x).obj G ⟶ (modulePullback B S hS x).obj H}
    {c' : (modulePullback B S hS x').obj G ⟶ (modulePullback B S hS x').obj H}
    (hc : PullbackTransportSquare f x x' h G H c c') (g : G ⟶ H) :
    (modulePullback B S hS x').map g = c' ↔
      (modulePullback B S hS f).map ((modulePullback B S hS x).map g) =
        (modulePullback B S hS f).map c := by
  have hg := (pullbackTransportSquare_modulePullback_map f x x' h g).eq
  have hc := hc.eq
  subst h
  simp only [pullbackTransport, eqToIso_refl, Iso.refl_hom, Category.comp_id] at hc hg
  constructor
  · intro e
    rw [← Iso.cancel_iso_hom_right _ _ ((modulePullbackCompIso B S hS f x).app H)]
    exact hg.trans ((congrArg (_ ≫ ·) e).trans hc.symm)
  · intro e
    rw [← Iso.cancel_iso_hom_left ((modulePullbackCompIso B S hS f x).app G)]
    exact hg.symm.trans ((congrArg (· ≫ _) e).trans hc)

/-- Composition with the comparison `f^*x^* ≅ (f ≫ x)^*` of Stacks 03LU followed by the transport
along `f ≫ x = x'` is injective. -/
theorem eq_of_comp_modulePullbackCompIso_hom_app_comp_eq (f : Z ⟶ Y) (x : Y ⟶ X) (x' : Z ⟶ X)
    (h : f ≫ x = x') {M : Modules.{u, u} B S hS Z.1 Z.2} {H : Modules.{u, u} B S hS X.1 X.2}
    (a b : M ⟶ (modulePullback B S hS f).obj ((modulePullback B S hS x).obj H))
    (e : a ≫ ((modulePullbackCompIso B S hS f x).hom.app H ≫ pullbackTransport H h) =
      b ≫ ((modulePullbackCompIso B S hS f x).hom.app H ≫ pullbackTransport H h)) :
    a = b := by
  subst h
  simpa [pullbackTransport] using congrArg (· ≫ (modulePullbackCompIso B S hS f x).inv.app H) e

variable {A : AlgebraicSpaces B S hS} (Γ : GroupoidInAlgebraicSpaces B S hS A)

variable (φ : Γ.objects ⟶ X) (hφ : Γ.target ≫ φ = Γ.source ≫ φ) (x' : Γ.arrows ⟶ X)
  (ht : Γ.target ≫ φ = x') (hs : Γ.source ≫ φ = x') {G H : Modules.{u, u} B S hS X.1 X.2}
  {c : (modulePullback B S hS φ).obj G ⟶ (modulePullback B S hS φ).obj H}
  {c' : (modulePullback B S hS x').obj G ⟶ (modulePullback B S hS x').obj H}

/-- The computation behind
`AlgebraicGeometry.Space.transitionCommutes_of_pullbackTransportSquares`: both sides of the
compatibility, followed by the comparison along the source, are the comparison along the target
followed by `c'`. -/
theorem spaceBaseDescent_comp_eq_of_pullbackTransportSquares
    (hct : PullbackTransportSquare Γ.target φ x' ht G H c c')
    (hcs : PullbackTransportSquare Γ.source φ x' hs G H c c') :
    (spaceBaseDescent B S hS Γ φ hφ G ≫ (modulePullback B S hS Γ.source).map c) ≫
        ((modulePullbackCompIso B S hS Γ.source φ).hom.app H ≫ pullbackTransport H hs) =
      ((modulePullback B S hS Γ.target).map c ≫ spaceBaseDescent B S hS Γ φ hφ H) ≫
        ((modulePullbackCompIso B S hS Γ.source φ).hom.app H ≫ pullbackTransport H hs) := by
  have hct := hct.eq
  have hcs := hcs.eq
  unfold spaceBaseDescent
  have e1 := modulePullbackUnflatten_comp_modulePullbackCompIso_hom_app Γ.target Γ.source φ G
    (pullbackTransport G hφ)
  have e2 := modulePullbackUnflatten_comp_modulePullbackCompIso_hom_app Γ.target Γ.source φ H
    (pullbackTransport H hφ)
  have tG := pullbackTransport_comp G hφ hs ht
  have tH := pullbackTransport_comp H hφ hs ht
  simp only [Category.assoc] at hct hcs ⊢
  rw [hcs, reassoc_of% e1, reassoc_of% tG, reassoc_of% e2, tH, hct]

/-- **Two squares along the target and the source of a groupoid with a common corner give the
compatibility of Stacks 03M3 with the canonical transition morphisms**: if `c : φ^*G ⟶ φ^*H` for
`φ : U ⟶ X` with `t ≫ φ = s ≫ φ` has squares with one `c' : x'^*G ⟶ x'^*H` along `t` and along `s`,
then `c` carries the canonical transition morphism of `φ^*G` to that of `φ^*H`. -/
theorem transitionCommutes_of_pullbackTransportSquares
    (hct : PullbackTransportSquare Γ.target φ x' ht G H c c')
    (hcs : PullbackTransportSquare Γ.source φ x' hs G H c c') :
    TransitionCommutes B S hS (U := Γ.objects) (V := Γ.arrows) (a := Γ.target) (b := Γ.source)
      (spaceBaseDescent B S hS Γ φ hφ G) (spaceBaseDescent B S hS Γ φ hφ H) c :=
  eq_of_comp_modulePullbackCompIso_hom_app_comp_eq Γ.source φ x' hs
    (spaceBaseDescent B S hS Γ φ hφ G ≫ (modulePullback B S hS Γ.source).map c)
    ((modulePullback B S hS Γ.target).map c ≫ spaceBaseDescent B S hS Γ φ hφ H)
    (spaceBaseDescent_comp_eq_of_pullbackTransportSquares Γ φ hφ x' ht hs hct hcs)

end Generic

section Family

variable (G H : Modules.{u, u} B S hS X.1 X.2)

/-- **A family of morphisms `χ_x : x^*G ⟶ x^*H` indexed by the scheme points of `X` is
compatible** when, for every `τ : T' ⟶ T` of the site and scheme points `x` of `X` at `T` and
`x' = x ∘ τ` at `T'`, the inverse image `τ^*χ_x` is `χ_{x'}` through the comparison
`τ^*x^* ≅ (x ∘ τ)^*` of Stacks 03LU and the transport along `x ∘ τ = x'`
(`AlgebraicGeometry.Space.PullbackTransportSquare`). -/
structure PointFamilyNatural
    (χ : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (modulePullback B S hS (pointHom x)).obj G ⟶ (modulePullback B S hS (pointHom x)).obj H) :
    Prop where
  /-- The square along `τ : T' ⟶ T`. -/
  square : ∀ ⦃T T' : BigFppfOver B S hS⦄ (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)
    (x' : yoneda.obj T' ⟶ X.1) (hx : yoneda.map τ ≫ x = x'),
    PullbackTransportSquare (Y := yonedaSpace B S hS T) (Z := yonedaSpace B S hS T')
      (representedSpaceMap B S hS τ) (pointHom x) (pointHom x') (pointHom_comp τ hx) G H
      (χ T x) (χ T' x')

variable {G H}

/-- **The restrictions of a morphism `g : G ⟶ H` to the scheme points form a compatible
family.** -/
theorem pointFamilyNatural_modulePullback_map (g : G ⟶ H) :
    PointFamilyNatural G H (fun _ x => (modulePullback B S hS (pointHom x)).map g) :=
  ⟨fun _ _ τ x x' hx => pullbackTransportSquare_modulePullback_map
    (Y := yonedaSpace B S hS _) (Z := yonedaSpace B S hS _)
    (representedSpaceMap B S hS τ) (pointHom x) (pointHom x') (pointHom_comp τ hx) g⟩

end Family

/-- `AlgebraicGeometry.Space.presentationAtlas_map_injective` with the atlas read as a morphism
into the algebraic space `Y` itself (rather than into `⟨Y.obj, Y.property⟩`), the spelling of the
inverse images along scheme points. -/
theorem presentationAtlas_map_injective_of_space {Y : AlgebraicSpaces B S hS}
    (P' : Presentation B S hS Y.obj Y.property) {G H : Modules.{u, u} B S hS Y.obj Y.property}
    [G.IsQuasicoherentOnSite] [H.IsQuasicoherentOnSite] {φ ψ : G ⟶ H}
    (h : (modulePullback B S hS (X := (presentationGroupoid P').objects) (Y := Y)
      (presentationAtlas P')).map φ =
      (modulePullback B S hS (X := (presentationGroupoid P').objects) (Y := Y)
      (presentationAtlas P')).map ψ) :
    φ = ψ := by
  have key := presentationAtlas_map_injective (φ := φ) (ψ := ψ) P'
  obtain ⟨F, hF⟩ := Y
  dsimp only at key h ⊢
  exact key h

/-- Two morphisms of quasi-coherent modules with the same inverse image along the scheme point
`U ⟶ X` of the atlas of a presentation are equal. -/
private theorem eq_of_modulePullback_map_pointHom_toSpace_eq_aux
    (P : Presentation B S hS X.obj X.property) {M N : Modules.{u, u} B S hS X.1 X.2}
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] {φ ψ : M ⟶ N}
    (h : (modulePullback B S hS (pointHom (X := X) P.toSpace)).map φ =
      (modulePullback B S hS (pointHom (X := X) P.toSpace)).map ψ) :
    φ = ψ := by
  refine presentationAtlas_map_injective_of_space P ?_
  obtain ⟨F, hF⟩ := X
  dsimp only [presentationAtlas, presentationGroupoid, representedAlgebraicSpace, yonedaSpace,
    pointHom] at h ⊢
  exact h

section Descent

variable (P : Presentation B S hS X.obj X.property)
  {G H : QuasicoherentSheaves.{u, u} B S hS X.obj X.property}
  {χ : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (modulePullback B S hS (pointHom x)).obj G.obj ⟶
        (modulePullback B S hS (pointHom x)).obj H.obj}
  (hχ : PointFamilyNatural G.obj H.obj χ)

include hχ in
/-- **A compatible family, read on the atlas of a presentation, carries the canonical transition
morphisms to each other**: `χ_φ` for the atlas `φ : U ⟶ X` satisfies the compatibility of
Stacks 03M3 along the two projections `R ⇉ U`. -/
theorem transitionCommutes_of_pointFamilyNatural :
    TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) G.obj)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
        (presentationAtlas_comm P) H.obj) (χ P.U P.toSpace) :=
  transitionCommutes_of_pullbackTransportSquares (presentationGroupoid P) (presentationAtlas P)
    (presentationAtlas_comm P) (pointHom (yoneda.map P.target ≫ P.toSpace))
    (pointHom_comp P.target rfl)
    (pointHom_comp P.source (congrArg (fun k => k.hom) (presentationAtlas_comm P).symm))
    (hχ.square P.target P.toSpace (yoneda.map P.target ≫ P.toSpace) rfl)
    (hχ.square P.source P.toSpace (yoneda.map P.target ≫ P.toSpace)
      (congrArg (fun k => k.hom) (presentationAtlas_comm P).symm))

/-- **The morphism `G ⟶ H` of quasi-coherent `𝒪_X`-modules of a compatible family of morphisms
`χ_x : x^*G ⟶ x^*H` indexed by the scheme points of `X`**: the descent along the atlas of the
presentation `P` (Stacks 03M3) of the member of the family at the atlas. -/
def pointFamilyDescendedHom : G.obj ⟶ H.obj :=
  presentationAtlasDescendedHom P (χ P.U P.toSpace)
    (transitionCommutes_of_pointFamilyNatural P hχ)

/-- The restriction of the morphism of a compatible family to the atlas is the member of the
family at the atlas. -/
theorem modulePullback_map_presentationAtlas_pointFamilyDescendedHom :
    (modulePullback B S hS (presentationAtlas P)).map (pointFamilyDescendedHom P hχ) =
      χ P.U P.toSpace :=
  modulePullback_map_presentationAtlasDescendedHom P _ _

/-- **The morphism of a compatible family is unique**: a morphism `G ⟶ H` whose restriction to
the atlas of `P` is the member of the family at the atlas is the morphism of the family. -/
theorem pointFamilyDescendedHom_unique (g : G.obj ⟶ H.obj)
    (hg : (modulePullback B S hS (presentationAtlas P)).map g = χ P.U P.toSpace) :
    g = pointFamilyDescendedHom P hχ :=
  presentationAtlasDescendedHom_unique P _ _ g hg

/-- The restriction of the morphism of a compatible family to the atlas, read along the scheme
point `U ⟶ X` of the atlas. -/
theorem modulePullback_map_pointHom_toSpace_pointFamilyDescendedHom :
    (modulePullback B S hS (pointHom (X := X) P.toSpace)).map (pointFamilyDescendedHom P hχ) =
      χ P.U P.toSpace := by
  have h := modulePullback_map_presentationAtlas_pointFamilyDescendedHom P hχ
  obtain ⟨F, hF⟩ := X
  dsimp only [presentationAtlas, presentationGroupoid, representedAlgebraicSpace, yonedaSpace,
    pointHom] at h ⊢
  exact h

/-- **The morphism of a compatible family restricts to every member**: for every scheme point
`x : T ⟶ X`, the inverse image of `pointFamilyDescendedHom P hχ` along `x` is `χ_x`.  Both are
determined by their inverse images along the chart `T ×_X U ⟶ T` of the presentation of `T`
pulled back from `P` (`AlgebraicGeometry.Space.presentationAtlas_map_injective`), and there both
are the member at the point `T ×_X U ⟶ X`: the first because that point factors through the
atlas of `P`, the second by the compatibility of the family along `T ×_X U ⟶ T`. -/
theorem modulePullback_map_pointHom_pointFamilyDescendedHom {T : BigFppfOver B S hS}
    (x : yoneda.obj T ⟶ X.1) :
    (modulePullback B S hS (pointHom x)).map (pointFamilyDescendedHom P hχ) = χ T x := by
  have hA := P.map_alongPointToAtlas_comp_toSpace x
  have s1 : PullbackTransportSquare (Y := yonedaSpace B S hS P.U)
      (Z := (presentationGroupoid (F := (yonedaSpace B S hS T).obj)
        (hF := (yonedaSpace B S hS T).property) (P.alongPoint x)).objects)
      (representedSpaceMap B S hS (P.alongPointToAtlas x)) (pointHom P.toSpace)
      (pointHom (yoneda.map (P.alongPointToPoint x) ≫ x)) (pointHom_comp _ hA) G.obj H.obj
      (χ P.U P.toSpace) (χ _ (yoneda.map (P.alongPointToPoint x) ≫ x)) :=
    hχ.square _ _ _ hA
  have e1 := (modulePullback_map_eq_iff_of_pullbackTransportSquare _ _ _ _ s1
    (pointFamilyDescendedHom P hχ)).2
    (congrArg _ (modulePullback_map_pointHom_toSpace_pointFamilyDescendedHom P hχ))
  have s2 : PullbackTransportSquare (Y := yonedaSpace B S hS T)
      (Z := (presentationGroupoid (F := (yonedaSpace B S hS T).obj)
        (hF := (yonedaSpace B S hS T).property) (P.alongPoint x)).objects)
      (presentationAtlas (F := (yonedaSpace B S hS T).obj)
        (hF := (yonedaSpace B S hS T).property) (P.alongPoint x)) (pointHom x)
      (pointHom (yoneda.map (P.alongPointToPoint x) ≫ x)) (pointHom_comp _ rfl) G.obj H.obj
      (χ T x) (χ _ (yoneda.map (P.alongPointToPoint x) ≫ x)) :=
    hχ.square _ _ _ rfl
  have e2 := (modulePullback_map_eq_iff_of_pullbackTransportSquare _ _ _ _ s2
    (pointFamilyDescendedHom P hχ)).1 e1
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
    G.obj G.property
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
    H.obj H.property
  exact presentationAtlas_map_injective_of_space (Y := yonedaSpace B S hS T) (P.alongPoint x) e2

/-- **A morphism `G ⟶ H` restricting to every member of a compatible family is its morphism.** -/
theorem eq_pointFamilyDescendedHom_of_modulePullback_map_pointHom (g : G.obj ⟶ H.obj)
    (hg : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (modulePullback B S hS (pointHom x)).map g = χ T x) :
    g = pointFamilyDescendedHom P hχ := by
  have := G.property
  have := H.property
  exact eq_of_modulePullback_map_pointHom_toSpace_eq_aux P
    ((hg P.U P.toSpace).trans
      (modulePullback_map_pointHom_toSpace_pointFamilyDescendedHom P hχ).symm)

end Descent

section Compatibilities

variable (P : Presentation B S hS X.obj X.property)

/-- Two morphisms of quasi-coherent `𝒪_X`-modules with the same inverse image along the scheme
point `U ⟶ X` of the atlas of a presentation are equal
(`AlgebraicGeometry.Space.presentationAtlas_map_injective`, read along the point). -/
theorem eq_of_modulePullback_map_pointHom_toSpace_eq {M N : Modules.{u, u} B S hS X.1 X.2}
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] {φ ψ : M ⟶ N}
    (h : (modulePullback B S hS (pointHom (X := X) P.toSpace)).map φ =
      (modulePullback B S hS (pointHom (X := X) P.toSpace)).map ψ) :
    φ = ψ :=
  eq_of_modulePullback_map_pointHom_toSpace_eq_aux P h

variable {G H : QuasicoherentSheaves.{u, u} B S hS X.obj X.property}
  {χ : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (modulePullback B S hS (pointHom x)).obj G.obj ⟶
        (modulePullback B S hS (pointHom x)).obj H.obj}
  (hχ : PointFamilyNatural G.obj H.obj χ)

/-- **A triangle through the morphism of a compatible family is checked on the members**: for
`c : K ⟶ G` and `e : K ⟶ H` with `K` quasi-coherent, if `x^*c ≫ χ_x = x^*e` at every scheme
point `x`, then `c ≫ g = e` for the morphism `g` of the family.  (The form of clause (1) of
Stacks 0D2Z, and of the compatibility with units.) -/
theorem comp_pointFamilyDescendedHom_eq {K : Modules.{u, u} B S hS X.1 X.2}
    [K.IsQuasicoherentOnSite] (c : K ⟶ G.obj) (e : K ⟶ H.obj)
    (h : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (modulePullback B S hS (pointHom x)).map c ≫ χ T x =
        (modulePullback B S hS (pointHom x)).map e) :
    c ≫ pointFamilyDescendedHom P hχ = e := by
  have := H.property
  refine eq_of_modulePullback_map_pointHom_toSpace_eq P ?_
  rw [Functor.map_comp, modulePullback_map_pointHom_toSpace_pointFamilyDescendedHom]
  exact h _ _

attribute [local instance] modulesMonoidalCategory

/-- **Multiplicativity of morphisms of compatible families is checked on the members**: for
compatible families `χ^i`, `χ^j`, `χ^k` (between `G_i, H_i`, `G_j, H_j`, `G_k, H_k`) and
multiplications `μ_G : G_i ⊗ G_j ⟶ G_k`, `μ_H : H_i ⊗ H_j ⟶ H_k`, if at every scheme point `x`
the member `χ^k_x` carries `x^*μ_G` to `x^*μ_H` through the comparison of Stacks 03EL of inverse
images with tensor products, then the morphisms `g_i, g_j, g_k` of the families satisfy
`μ_G ≫ g_k = (g_i ⊗ g_j) ≫ μ_H`. -/
theorem mul_comp_pointFamilyDescendedHom {Gi Gj Gk Hi Hj Hk :
      QuasicoherentSheaves.{u, u} B S hS X.obj X.property}
    {χi : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (modulePullback B S hS (pointHom x)).obj Gi.obj ⟶
        (modulePullback B S hS (pointHom x)).obj Hi.obj}
    {χj : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (modulePullback B S hS (pointHom x)).obj Gj.obj ⟶
        (modulePullback B S hS (pointHom x)).obj Hj.obj}
    {χk : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (modulePullback B S hS (pointHom x)).obj Gk.obj ⟶
        (modulePullback B S hS (pointHom x)).obj Hk.obj}
    (hi : PointFamilyNatural Gi.obj Hi.obj χi) (hj : PointFamilyNatural Gj.obj Hj.obj χj)
    (hk : PointFamilyNatural Gk.obj Hk.obj χk) (μG : Gi.obj ⊗ Gj.obj ⟶ Gk.obj)
    (μH : Hi.obj ⊗ Hj.obj ⟶ Hk.obj)
    (h : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (modulePullback B S hS (pointHom x)).map μG ≫ χk T x =
        (modulePullbackTensorIso B S hS (pointHom x) Gi.obj Gj.obj).hom ≫ (χi T x ⊗ₘ χj T x) ≫
          (modulePullbackTensorIso B S hS (pointHom x) Hi.obj Hj.obj).inv ≫
            (modulePullback B S hS (pointHom x)).map μH) :
    μG ≫ pointFamilyDescendedHom P hk =
      (pointFamilyDescendedHom P hi ⊗ₘ pointFamilyDescendedHom P hj) ≫ μH := by
  have := Gi.property
  have := Gj.property
  have := Hk.property
  have := isQuasicoherentOnSite_tensorObj B S hS X.obj X.property Gi.obj Gj.obj
  refine eq_of_modulePullback_map_pointHom_toSpace_eq P ?_
  have hn := modulePullbackTensorIso_hom_naturality B S hS (pointHom (X := X) P.toSpace)
    (pointFamilyDescendedHom P hi) (pointFamilyDescendedHom P hj)
  rw [modulePullback_map_pointHom_toSpace_pointFamilyDescendedHom,
    modulePullback_map_pointHom_toSpace_pointFamilyDescendedHom] at hn
  rw [Functor.map_comp, Functor.map_comp,
    modulePullback_map_pointHom_toSpace_pointFamilyDescendedHom,
    h, (Iso.eq_comp_inv _).2 hn]
  simp only [Category.assoc]

end Compatibilities

end AlgebraicGeometry.Space

end
