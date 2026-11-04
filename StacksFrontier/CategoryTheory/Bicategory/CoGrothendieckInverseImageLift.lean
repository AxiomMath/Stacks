module

public import StacksFrontier.CategoryTheory.Bicategory.CoGrothendieckInverseImageDescent

/-!
# Natural transformations into a family of inverse images

Let `F` be a pseudofunctor on `𝒮ᵒᵖ` with values in categories, `G : 𝒟 ⥤ 𝒮` a functor and
`𝒢 : J ⥤ ∫ᶜ (F ∘ G)` a functor. Given an object `Y = (X, L)` of `∫ᶜ F` with morphisms
`s j : G (𝒢 j).base ⟶ X`, natural in `j`, and morphisms `σ j : (𝒢 j).fiber ⟶ s j^* L` of the
fibres, the morphisms `(𝟙, σ j)` form a natural transformation from `𝒢` to the family of inverse
images `j ↦ ((𝒢 j).base, s j^* L)` of `CategoryTheory.Pseudofunctor.CoGrothendieck.inverseImage`
(along the functor `CategoryTheory.Comma.liftConst` with constant right-hand side `Y`) as soon as
the `σ j` satisfy the naturality square
`(𝒢 u).fiber ≫ u^* σ j = σ j' ≫ (s j^* L ≅ (G u)^* s j^* L)` with the comparison of the
pseudofunctor.

## Main definitions

* `CategoryTheory.Pseudofunctor.CoGrothendieck.LiftConstSquare`: the naturality square.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.liftConstNatTrans`: the natural transformation.
* `CategoryTheory.NatTrans.liftOfFaithful`: a natural transformation read through a faithful
  functor.

## Implementation notes

Every object and morphism is spelled once: the bases as `(𝒢.obj j).base` and `(𝒢.map u).base`,
the right-hand side as `Y.base` and `Y.fiber`. A concrete square instantiating the hypothesis is
then compared with it argument by argument, never as a composite with other spellings, which
would unfold the composition of a concrete Grothendieck construction.
-/

@[expose] public noncomputable section

namespace CategoryTheory

/-- Two composites of identifications of objects with the same ends are equal. -/
theorem eqToHom_comp_eqToHom_comp_eqToHom_eq_comp {C : Type*} [Category C] {X Y Z W Y' : C}
    (p : X = Y) (q : Y = Z) (r : Z = W) (s : X = Y') (t : Y' = W) :
    eqToHom p ≫ eqToHom q ≫ eqToHom r = eqToHom s ≫ eqToHom t := by
  subst p q r t
  simp

end CategoryTheory

namespace CategoryTheory.NatTrans

/-- **A natural transformation along a faithful functor**: if the components of `θ : A ⋙ I ⟶ B ⋙ I`
are the images under the faithful functor `I` of morphisms `φ c : A c ⟶ B c`, then the `φ c` are
natural. -/
def liftOfFaithful {C D E : Type*} [Category C] [Category D] [Category E] {A B : C ⥤ D}
    (I : D ⥤ E) [hI : I.Faithful] (θ : A ⋙ I ⟶ B ⋙ I) (φ : ∀ c, A.obj c ⟶ B.obj c)
    (hφ : ∀ c, I.map (φ c) = θ.app c) : A ⟶ B where
  app := φ
  naturality c' c u := I.map_injective (by
    rw [I.map_comp, I.map_comp, hφ, hφ]
    exact θ.naturality u)

/-- The component of `liftOfFaithful` at `c` is `φ c`. -/
theorem liftOfFaithful_app {C D E : Type*} [Category C] [Category D] [Category E] {A B : C ⥤ D}
    (I : D ⥤ E) [hI : I.Faithful] (θ : A ⋙ I ⟶ B ⋙ I) (φ : ∀ c, A.obj c ⟶ B.obj c)
    (hφ : ∀ c, I.map (φ c) = θ.app c) (c : C) : (liftOfFaithful (hI := hI) I θ φ hφ).app c = φ c :=
  rfl

/-- The image under `I` of a component of `liftOfFaithful` is the component of `θ`. -/
theorem map_liftOfFaithful_app {C D E : Type*} [Category C] [Category D] [Category E]
    {A B : C ⥤ D} (I : D ⥤ E) [hI : I.Faithful] (θ : A ⋙ I ⟶ B ⋙ I) (φ : ∀ c, A.obj c ⟶ B.obj c)
    (hφ : ∀ c, I.map (φ c) = θ.app c) (c : C) :
    I.map ((liftOfFaithful (hI := hI) I θ φ hφ).app c) = θ.app c :=
  hφ c

/-- The image under a functor of a component of a transported natural transformation is the
image of the component, up to the identifications of the objects. -/
theorem map_transportOfEq_app {C D E : Type*} [Category C] [Category D] [Category E]
    {K K' L L' : C ⥤ D} (h : K = L) (h' : K' = L') (θ : K ⟶ K') (P : D ⥤ E) (X : C) :
    P.map ((transportOfEq h h' θ).app X) =
      eqToHom (congrArg P.obj (Functor.congr_obj h X).symm) ≫ P.map (θ.app X) ≫
        eqToHom (congrArg P.obj (Functor.congr_obj h' X)) := by
  subst h h'
  simp [transportOfEq]

end CategoryTheory.NatTrans

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open Opposite Bicategory

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

section Square

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒟 : Type u₃} [Category.{v₃} 𝒟]
  {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}} {G : 𝒟 ⥤ 𝒮}

/-- **The naturality square of fibre morphisms into inverse images**: for a morphism `m : P ⟶ Q` of
`∫ᶜ (F ∘ G)`, an object `Y = (X, L)` of `∫ᶜ F`, morphisms `s_P, s_Q` to `X` with
`G m.base ≫ s_Q = s_P` and morphisms `σ_P : P.fiber ⟶ s_P^* L`, `σ_Q : Q.fiber ⟶ s_Q^* L`, the
square `m.fiber ≫ m^* σ_Q = σ_P ≫ (s_P^* L ≅ m^* s_Q^* L)` with the comparison of the
pseudofunctor. -/
def LiftConstSquare {P Q : ∫ᶜ (G.op.toPseudofunctor.comp F)} (m : P ⟶ Q) (Y : ∫ᶜ F)
    (sP : G.obj P.base ⟶ Y.base) (sQ : G.obj Q.base ⟶ Y.base) (hs : G.map m.base ≫ sQ = sP)
    (σP : P.fiber ⟶ (F.map sP.op.toLoc).toFunctor.obj Y.fiber)
    (σQ : Q.fiber ⟶ (F.map sQ.op.toLoc).toFunctor.obj Y.fiber) : Prop :=
  m.fiber ≫ ((G.op.toPseudofunctor.comp F).map m.base.op.toLoc).toFunctor.map σQ =
    σP ≫ (F.mapComp' sQ.op.toLoc (G.map m.base).op.toLoc sP.op.toLoc
      (congrArg (fun k : G.obj P.base ⟶ Y.base => k.op.toLoc) hs)).hom.toNatTrans.app Y.fiber

end Square

section LiftConst

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒟 : Type u₃} [Category.{v₃} 𝒟]
  {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}} {G : 𝒟 ⥤ 𝒮}
  {J : Type u₄} [Category.{v₄} J] (𝒢 : J ⥤ ∫ᶜ (G.op.toPseudofunctor.comp F)) (Y : ∫ᶜ F)
  (s : ∀ j, G.obj (𝒢.obj j).base ⟶ Y.base)
  (hs : ∀ {j' j : J} (u : j' ⟶ j), G.map (𝒢.map u).base ≫ s j = s j')
  (σ : ∀ j, (𝒢.obj j).fiber ⟶ (F.map (s j).op.toLoc).toFunctor.obj Y.fiber)

/-- The family `j ↦ ((𝒢 j).base, Y, s j)` of triples with constant right-hand side. -/
abbrev liftConstComma : J ⥤ Comma G (forget F) :=
  Comma.liftConst (R := forget F) (𝒢 ⋙ forget _) Y s hs

/-- **The morphisms `(𝟙, σ j)` from `𝒢` to the inverse images `((𝒢 j).base, s j^* L)`**, natural
in `j` when the `σ j` are compatible with the transition morphisms of `𝒢` and the comparisons of
the pseudofunctor. -/
def liftConstNatTrans
    (hσ : ∀ {j' j : J} (u : j' ⟶ j),
      LiftConstSquare (F := F) (G := G) (𝒢.map u) Y (s j') (s j) (hs u) (σ j') (σ j)) :
    𝒢 ⟶ liftConstComma 𝒢 Y s hs ⋙ inverseImage F G where
  app j := (ι (G.op.toPseudofunctor.comp F) (𝒢.obj j).base).map (σ j)
  naturality {j' j} u := by
    refine (comp_ι_map_eq (F := G.op.toPseudofunctor.comp F) (b := (𝒢.obj j).base)
      (M := (𝒢.obj j).fiber) (σ j) (𝒢.map u)).trans (Eq.trans ?_
        (ι_map_comp_eq (F := G.op.toPseudofunctor.comp F) (a := (𝒢.obj j').base)
          (M := (𝒢.obj j').fiber) (σ j') ((inverseImage F G).map
            ((liftConstComma 𝒢 Y s hs).map u))).symm)
    exact congrArg (fun φ => (⟨(𝒢.map u).base, φ⟩ :
        (ι (G.op.toPseudofunctor.comp F) (𝒢.obj j').base).obj (𝒢.obj j').fiber ⟶
          (liftConstComma 𝒢 Y s hs ⋙ inverseImage F G).obj j))
      (Eq.trans (hσ u) (congrArg (σ j' ≫ ·)
        (inverseImage_map_liftConst_fiber (F := F) (G := G) (A := 𝒢 ⋙ forget _) (Y := Y)
          (s := s) (hs := hs) u).symm))

/-- The component of `liftConstNatTrans` at `j` is the image of `σ j` under the inclusion of the
fibre over `(𝒢 j).base`. -/
theorem liftConstNatTrans_app
    (hσ : ∀ {j' j : J} (u : j' ⟶ j),
      LiftConstSquare (F := F) (G := G) (𝒢.map u) Y (s j') (s j) (hs u) (σ j') (σ j)) (j : J) :
    (liftConstNatTrans 𝒢 Y s hs σ hσ).app j =
      (ι (G.op.toPseudofunctor.comp F) (𝒢.obj j).base).map (σ j) :=
  rfl

/-- The components of `liftConstNatTrans` are invertible when the `σ j` are. -/
theorem isIso_liftConstNatTrans_app
    (hσ : ∀ {j' j : J} (u : j' ⟶ j),
      LiftConstSquare (F := F) (G := G) (𝒢.map u) Y (s j') (s j) (hs u) (σ j') (σ j))
    (j : J) (h : IsIso (σ j)) :
    IsIso ((liftConstNatTrans 𝒢 Y s hs σ hσ).app j) :=
  Functor.map_isIso (ι (G.op.toPseudofunctor.comp F) (𝒢.obj j).base) (σ j)

end LiftConst

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
