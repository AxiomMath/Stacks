module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence

/-!
# Large-valued algebraic spaces over a smaller base

Let `g : V ⟶ S` be a morphism of a big fppf site `B`. The equivalence
`AlgebraicGeometry.FormalSpace.smallerBasePresheafEquivalenceULift` identifies presheaves with
values in `Type (u + 1)` on the big fppf site of `V` with such presheaves on the big fppf site of
`S` over the universe-lifted representable presheaf of `g` (Stacks 04SG, read through the
large-valued form of Stacks 00Y1). This file shows that the algebraic-space predicates for
presheaves with values in `Type (u + 1)`, the value universe of formal algebraic spaces, do not
see the change of base.

## Main definitions

* `AlgebraicGeometry.FormalSpace.smallerBaseULift`: the presheaf on the big fppf site of `S`
  attached to a presheaf on the big fppf site of `V`.
* `AlgebraicGeometry.FormalSpace.smallerBaseULiftYonedaIso`: the presheaf attached to the
  universe-lifted representable presheaf of an object `U` of the big fppf site of `V` is the
  universe-lifted representable presheaf of `U` viewed over `S`.
* `AlgebraicGeometry.FormalSpace.smallerBaseChart`: the chart over `S` attached to a chart over
  `V`.

## Main results

* `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_smallerBaseULift_iff`: a presheaf with
  values in `Type (u + 1)` on the big fppf site of `V` is an algebraic space over `V` exactly when
  the attached presheaf is an algebraic space over `S`.
* `AlgebraicGeometry.FormalSpace.exists_smallerBaseChart`: every chart of the attached presheaf
  is the chart attached to a chart over `V`.

## Implementation notes

Algebraicity is reduced to presheaves of `Type u`: an algebraic space with values in
`Type (u + 1)` is the universe lift of one with values in `Type u`
(`AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`), the
equivalence commutes with the universe lift
(`AlgebraicGeometry.FormalSpace.smallerBaseULiftWhiskerIso`), and for presheaves of `Type u`
both directions are in the library: Stacks 03I5 part (2)
(`AlgebraicGeometry.spacesOverSmallerBaseFunctor`) and the preservation of algebraic spaces by
the quasi-inverse (`AlgebraicGeometry.isAlgebraicSpace_smallerBasePresheafEquivalence_inverse`).

## References

* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

/-! ### The attached presheaf -/

/-- The presheaf with values in `Type (u + 1)` on the big fppf site of `S` attached to such a
presheaf `G` on the big fppf site of `V` by Stacks 04SG: its sections over `T` are the
factorizations `φ : T ⟶ (V ⟶ S)` together with a section of `G` over `T →φ V`. -/
abbrev smallerBaseULift (G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  ((smallerBasePresheafEquivalenceULift B V S hV hS g).functor.obj G).left

/-- The morphism of attached presheaves induced by a morphism of presheaves on the big fppf
site of `V`. -/
abbrev smallerBaseULiftMap {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} (f : G ⟶ G') :
    smallerBaseULift B V S hV hS g G ⟶ smallerBaseULift B V S hV hS g G' :=
  ((smallerBasePresheafEquivalenceULift B V S hV hS g).functor.map f).left

/-- The structural morphism of the attached presheaf to the universe-lifted representable
presheaf of `g : V ⟶ S`. -/
abbrev smallerBaseULiftHom (G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)) :
    smallerBaseULift B V S hV hS g G ⟶ (uliftYoneda.{u + 1}).obj (Over.mk g) :=
  ((smallerBasePresheafEquivalenceULift B V S hV hS g).functor.obj G).hom

/-- A section of the attached presheaf, from a factorization and a section over it. -/
abbrev smallerBaseULiftMk (G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1))
    {T : BigFppfOver B S hS} (φ : T ⟶ Over.mk g) (s : G.obj (op (Over.mk φ.left))) :
    (smallerBaseULift B V S hV hS g G).obj (op T) :=
  Sigma.mk (β := fun φ : T ⟶ Over.mk g => G.obj (op (Over.mk φ.left))) φ s

/-- The structural morphisms of attached presheaves are compatible with the induced morphisms. -/
@[reassoc (attr := simp)]
theorem smallerBaseULiftMap_comp_hom {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (f : G ⟶ G') :
    smallerBaseULiftMap B V S hV hS g f ≫ smallerBaseULiftHom B V S hV hS g G' =
      smallerBaseULiftHom B V S hV hS g G :=
  Over.w ((smallerBasePresheafEquivalenceULift B V S hV hS g).functor.map f)

/-- The induced morphisms of attached presheaves compose. -/
@[reassoc]
theorem smallerBaseULiftMap_comp {G G' G'' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (f : G ⟶ G') (f' : G' ⟶ G'') :
    smallerBaseULiftMap B V S hV hS g f ≫ smallerBaseULiftMap B V S hV hS g f' =
      smallerBaseULiftMap B V S hV hS g (f ≫ f') :=
  (congrArg Over.Hom.left
    ((smallerBasePresheafEquivalenceULift B V S hV hS g).functor.map_comp f f')).symm

/-- A section of an attached presheaf restricted along a morphism of factorizations with identity
underlying morphism of schemes is the same section. -/
theorem smallerBaseULiftMk_map_eq (G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1))
    {T : BigFppfOver B S hS} {φ φ' : T ⟶ Over.mk g} (s : G.obj (op (Over.mk φ'.left)))
    (k : (Over.mk φ.left : BigFppfOver B V hV) ⟶ Over.mk φ'.left) (hk : k.left = 𝟙 _) :
    smallerBaseULiftMk B V S hV hS g G φ (G.map k.op s) =
      smallerBaseULiftMk B V S hV hS g G φ' s := by
  have hw : k.left ≫ φ'.left = φ.left := Over.w k
  obtain rfl : φ = φ' := by
    apply Over.OverMorphism.ext
    rw [← hw, hk, Category.id_comp]
  obtain rfl : k = 𝟙 _ := Over.OverMorphism.ext hk
  simp

/-- Two sections of the attached presheaf of a universe-lifted representable presheaf agree as
soon as their underlying morphisms of schemes agree. -/
theorem smallerBaseULiftMk_uliftYoneda_ext {U₀ : BigFppfOver B V hV} {T : BigFppfOver B S hS}
    {φ φ' : T ⟶ Over.mk g} (k : Over.mk φ.left ⟶ U₀) (k' : Over.mk φ'.left ⟶ U₀)
    (h : k.left = k'.left) :
    smallerBaseULiftMk B V S hV hS g (uliftYoneda.{u + 1}.obj U₀) φ (ULift.up k) =
      smallerBaseULiftMk B V S hV hS g (uliftYoneda.{u + 1}.obj U₀) φ' (ULift.up k') := by
  have h1 : k.left ≫ U₀.hom = φ.left := Over.w k
  have h2 : k'.left ≫ U₀.hom = φ'.left := Over.w k'
  obtain rfl : φ = φ' := by
    apply Over.OverMorphism.ext
    rw [← h1, ← h2, h]
  obtain rfl : k = k' := Over.OverMorphism.ext h
  rfl

/-! ### Compatibility with the universe lift -/

/-- **The change of base commutes with the universe lift.** The presheaf attached to the universe
lift of a presheaf `G₀` of `Type u` is the universe lift of the presheaf attached to `G₀` by
`AlgebraicGeometry.smallerBasePresheafEquivalence`. -/
def smallerBaseULiftWhiskerIso (G₀ : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u) :
    smallerBaseULift B V S hV hS g (G₀ ⋙ uliftFunctor.{u + 1}) ≅
      ((smallerBasePresheafEquivalence B V S hV hS g).functor.obj G₀).left ⋙
        uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun T => Equiv.toIso
    { toFun := fun p => ULift.up ⟨p.1, p.2.down⟩
      invFun := fun p => ⟨p.down.1, ULift.up p.down.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })
    (fun _ => by ext; rfl)

/-- The comparison `AlgebraicGeometry.FormalSpace.smallerBaseULiftWhiskerIso` is one of presheaves
over the universe-lifted representable presheaf of `g`. -/
theorem smallerBaseULiftWhiskerIso_hom_comp (G₀ : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u) :
    (smallerBaseULiftWhiskerIso B V S hV hS g G₀).hom ≫
        Functor.whiskerRight ((smallerBasePresheafEquivalence B V S hV hS g).functor.obj G₀).hom
          uliftFunctor.{u + 1} =
      smallerBaseULiftHom B V S hV hS g (G₀ ⋙ uliftFunctor.{u + 1}) := by
  ext
  rfl

/-! ### Algebraicity -/

/-- The direction of `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_smallerBaseULift_iff`
descending algebraicity from the attached presheaf over `S` to `G` over `V`. -/
theorem isAlgebraicSpaceULift_of_smallerBaseULift (G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1))
    (h : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (smallerBaseULift B V S hV hS g G)) :
    Space.IsAlgebraicSpaceULift.{u + 1} B V hV G := by
  let Ψ := smallerBasePresheafEquivalence B V S hV hS g
  let Φ := smallerBasePresheafEquivalenceULift B V S hV hS g
  obtain ⟨F₀, hF₀, ⟨e⟩⟩ :=
    Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift.{u + 1} B S hS h
  obtain ⟨q₀, hq₀⟩ := Space.exists_whiskerRight_eq.{u + 1} B S hS
    (F := F₀) (G := yoneda.obj (Over.mk g))
    (e.hom ≫ smallerBaseULiftHom B V S hV hS g G)
  obtain ⟨X₀, e', hq, hX₀⟩ : ∃ (X₀ : Over (yoneda.obj (Over.mk g) :
      (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (e' : X₀.left ⋙ uliftFunctor.{u + 1} ≅
        smallerBaseULift B V S hV hS g G),
      Functor.whiskerRight X₀.hom uliftFunctor.{u + 1} =
        e'.hom ≫ smallerBaseULiftHom B V S hV hS g G ∧ IsAlgebraicSpace B S hS X₀.left :=
    ⟨Over.mk q₀, e, hq₀, hF₀⟩
  obtain ⟨ε, hε⟩ : ∃ ε : (Ψ.functor.obj (Ψ.inverse.obj X₀)).left ≅ X₀.left,
      ε.hom ≫ X₀.hom = (Ψ.functor.obj (Ψ.inverse.obj X₀)).hom :=
    ⟨(Over.forget _).mapIso (Ψ.counitIso.app X₀), Over.w (Ψ.counitIso.app X₀).hom⟩
  have key : Functor.whiskerRight ε.hom uliftFunctor.{u + 1} ≫ e'.hom ≫
      smallerBaseULiftHom B V S hV hS g G =
      Functor.whiskerRight (Ψ.functor.obj (Ψ.inverse.obj X₀)).hom uliftFunctor.{u + 1} := by
    rw [← hq, ← hε]
    rfl
  let i₁ : Φ.functor.obj (Ψ.inverse.obj X₀ ⋙ uliftFunctor.{u + 1}) ≅ Φ.functor.obj G :=
    Over.isoMk (smallerBaseULiftWhiskerIso B V S hV hS g (Ψ.inverse.obj X₀) ≪≫
      Functor.isoWhiskerRight ε uliftFunctor.{u + 1} ≪≫ e') (by
        simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Category.assoc]
        exact (whisker_eq _ key).trans (smallerBaseULiftWhiskerIso_hom_comp B V S hV hS g _))
  exact Space.isAlgebraicSpaceULift_of_iso B V hV (Φ.fullyFaithfulFunctor.preimageIso i₁)
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B V hV _).mpr
      (isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B V S hV hS g X₀ hX₀))

/-- The direction of `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_smallerBaseULift_iff`
transporting algebraicity from `G` over `V` to the attached presheaf over `S`. -/
theorem isAlgebraicSpaceULift_smallerBaseULift (G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1))
    (h : Space.IsAlgebraicSpaceULift.{u + 1} B V hV G) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (smallerBaseULift B V S hV hS g G) := by
  obtain ⟨G₀, hG₀, ⟨e⟩⟩ :=
    Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift.{u + 1} B V hV h
  have h₀ : IsAlgebraicSpace B S hS
      ((smallerBasePresheafEquivalence B V S hV hS g).functor.obj G₀).left :=
    ((spacesOverSmallerBaseFunctor B V S hV hS g).obj ⟨G₀, hG₀⟩).2
  exact Space.isAlgebraicSpaceULift_of_iso B S hS
    ((smallerBaseULiftWhiskerIso B V S hV hS g G₀).symm ≪≫
      (Over.forget _).mapIso
        ((smallerBasePresheafEquivalenceULift B V S hV hS g).functor.mapIso e))
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr h₀)

/-- **Algebraicity does not see the change of base.** A presheaf with values in `Type (u + 1)` on
the big fppf site of `V` is an algebraic space over `V` exactly when the attached presheaf on the
big fppf site of `S` is an algebraic space over `S`.

Both sides are universe lifts of presheaves of `Type u`, and for those this is Stacks 03I5
part (2) in one direction and the preservation of algebraic spaces by the quasi-inverse of
Stacks 04SG in the other. -/
theorem isAlgebraicSpaceULift_smallerBaseULift_iff (G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (smallerBaseULift B V S hV hS g G) ↔
      Space.IsAlgebraicSpaceULift.{u + 1} B V hV G :=
  ⟨isAlgebraicSpaceULift_of_smallerBaseULift B V S hV hS g G,
    isAlgebraicSpaceULift_smallerBaseULift B V S hV hS g G⟩

/-! ### Representable presheaves and charts -/

/-- The sections of the presheaf attached to the universe-lifted representable presheaf of an
object `U₀` of the big fppf site of `V` are the morphisms into `U₀` viewed over `S`. -/
def smallerBaseULiftYonedaEquiv (U₀ : BigFppfOver B V hV) (T : BigFppfOver B S hS) :
    (smallerBaseULift B V S hV hS g (uliftYoneda.{u + 1}.obj U₀)).obj (op T) ≃
      (uliftYoneda.{u + 1}.obj ((Over.map g).obj U₀)).obj (op T) where
  toFun p := ULift.up (Over.homMk p.2.down.left (by
    have h1 : p.2.down.left ≫ U₀.hom = p.1.left := Over.w p.2.down
    have h2 : p.1.left ≫ g = T.hom := Over.w p.1
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) h1).trans h2)))
  invFun m := smallerBaseULiftMk B V S hV hS g (uliftYoneda.{u + 1}.obj U₀)
    (m.down ≫ relocalizeOverHom B V S hV hS g U₀) (ULift.up (Over.homMk m.down.left rfl))
  left_inv p := smallerBaseULiftMk_uliftYoneda_ext B V S hV hS g _ _ rfl
  right_inv _ := rfl

/-- **The attached presheaf of a representable presheaf is representable.** The presheaf
attached to the universe-lifted representable presheaf of an object `U₀` of the big fppf site of
`V` is the universe-lifted representable presheaf of `U₀` viewed over `S`. -/
def smallerBaseULiftYonedaIso (U₀ : BigFppfOver B V hV) :
    smallerBaseULift B V S hV hS g (uliftYoneda.{u + 1}.obj U₀) ≅
      uliftYoneda.{u + 1}.obj ((Over.map g).obj U₀) :=
  NatIso.ofComponents (fun T => (smallerBaseULiftYonedaEquiv B V S hV hS g U₀ (unop T)).toIso)
    (fun _ => by ext; exact ULift.ext (Over.OverMorphism.ext rfl))

/-- The comparison `AlgebraicGeometry.FormalSpace.smallerBaseULiftYonedaIso` is natural in the
object of the big fppf site of `V`. -/
theorem smallerBaseULiftYonedaIso_hom_naturality {U₀ U₁ : BigFppfOver B V hV} (m : U₀ ⟶ U₁) :
    smallerBaseULiftMap B V S hV hS g (uliftYoneda.{u + 1}.map m) ≫
        (smallerBaseULiftYonedaIso B V S hV hS g U₁).hom =
      (smallerBaseULiftYonedaIso B V S hV hS g U₀).hom ≫
        uliftYoneda.{u + 1}.map ((Over.map g).map m) := by
  ext
  exact ULift.ext (Over.OverMorphism.ext rfl)

/-- The chart of the attached presheaf obtained from a chart `a` over `V`: the induced morphism
read through `AlgebraicGeometry.FormalSpace.smallerBaseULiftYonedaIso`. -/
noncomputable def smallerBaseChart {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    {U₀ : BigFppfOver B V hV} (a : uliftYoneda.{u + 1}.obj U₀ ⟶ G) :
    uliftYoneda.{u + 1}.obj ((Over.map g).obj U₀) ⟶ smallerBaseULift B V S hV hS g G :=
  (smallerBaseULiftYonedaIso B V S hV hS g U₀).inv ≫ smallerBaseULiftMap B V S hV hS g a

/-- Attaching a chart is compatible with postcomposition. -/
@[reassoc]
theorem smallerBaseChart_comp {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    {U₀ : BigFppfOver B V hV} (a : uliftYoneda.{u + 1}.obj U₀ ⟶ G) (k : G ⟶ G') :
    smallerBaseChart B V S hV hS g a ≫ smallerBaseULiftMap B V S hV hS g k =
      smallerBaseChart B V S hV hS g (a ≫ k) := by
  simp only [smallerBaseChart, Category.assoc, smallerBaseULiftMap_comp]

/-- Attaching a chart is compatible with precomposition by a morphism of the site. -/
theorem smallerBaseChart_naturality {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    {U₀ U₁ : BigFppfOver B V hV} (m : U₀ ⟶ U₁) (b : uliftYoneda.{u + 1}.obj U₁ ⟶ G) :
    uliftYoneda.{u + 1}.map ((Over.map g).map m) ≫ smallerBaseChart B V S hV hS g b =
      smallerBaseChart B V S hV hS g (uliftYoneda.{u + 1}.map m ≫ b) := by
  have h' : uliftYoneda.{u + 1}.map ((Over.map g).map m) ≫
      (smallerBaseULiftYonedaIso B V S hV hS g U₁).inv =
      (smallerBaseULiftYonedaIso B V S hV hS g U₀).inv ≫
        smallerBaseULiftMap B V S hV hS g (uliftYoneda.{u + 1}.map m) := by
    rw [Iso.comp_inv_eq, Category.assoc, smallerBaseULiftYonedaIso_hom_naturality,
      Iso.inv_hom_id_assoc]
  simp only [smallerBaseChart]
  rw [← Category.assoc, h', Category.assoc, smallerBaseULiftMap_comp]

/-- An attached chart followed by the structural morphism of the attached presheaf reads off the
structure morphism of the chart's object. -/
theorem smallerBaseChart_comp_hom {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    {U₀ : BigFppfOver B V hV} (a : uliftYoneda.{u + 1}.obj U₀ ⟶ G) :
    smallerBaseChart B V S hV hS g a ≫ smallerBaseULiftHom B V S hV hS g G =
      uliftYoneda.{u + 1}.map (relocalizeOverHom B V S hV hS g U₀) := by
  rw [smallerBaseChart, Category.assoc, smallerBaseULiftMap_comp_hom]
  ext
  exact ULift.ext (Over.OverMorphism.ext rfl)

/-- **Every chart of an attached presheaf is an attached chart.** A morphism from the
universe-lifted representable presheaf of `U` to the attached presheaf of `G` is a section over
`U`, that is a factorization `ψ` of the structure morphism of `U` through `V` together with a
section of `G` over `(U, ψ)`; so it is the chart attached to a chart of `G`, read through the
comparison `AlgebraicGeometry.relocalizeBaseHom`. -/
theorem exists_smallerBaseChart {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (U : BigFppfOver B S hS)
    (a : uliftYoneda.{u + 1}.obj U ⟶ smallerBaseULift B V S hV hS g G) :
    ∃ (ψ : U.left ⟶ B.obj hV) (hψ : ψ ≫ g = U.hom)
      (a₀ : uliftYoneda.{u + 1}.obj (Over.mk ψ : BigFppfOver B V hV) ⟶ G),
      a = uliftYoneda.{u + 1}.map (relocalizeBaseHom B V S hV hS g hψ) ≫
        smallerBaseChart B V S hV hS g a₀ := by
  generalize hx : uliftYonedaEquiv a = x
  obtain ⟨φ, s⟩ := x
  have hψ : φ.left ≫ g = U.hom := Over.w φ
  refine ⟨φ.left, hψ, uliftYonedaEquiv.symm s, ?_⟩
  apply uliftYonedaEquiv.injective
  rw [hx, uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
  exact (smallerBaseULiftMk_map_eq B V S hV hS g G
    (φ := relocalizeBaseHom B V S hV hS g hψ ≫ relocalizeOverHom B V S hV hS g (Over.mk φ.left))
    (φ' := φ) s (Over.homMk (relocalizeBaseHom B V S hV hS g hψ).left rfl) rfl).symm

end AlgebraicGeometry.FormalSpace

end
