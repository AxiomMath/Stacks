module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.RestrictMorPresheaf
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# Open substacks of the stack of curves cut out by a property of families (Stacks 0E0E)

Section 0E0E of the chapter on moduli of curves characterizes an open substack of the stack of
curves `Curves` by a property `P` of families of curves satisfying

* (o) given a family of curves `f : X → S` there is a largest open subscheme `S' ⊂ S` over
  which `f` has `P`, and formation of `S'` commutes with arbitrary base change.

This file proves, for any property `P` of families of curves satisfying (o), that the strictly
full subcategory `Curves^P ⊂ Curves` it cuts out is a category fibred in groupoids over the big
fppf site and that its inclusion into `Curves` is **representable by algebraic spaces and an open
immersion** (Stacks 02ZW and 04XB): for every scheme `U` and every 1-morphism
`y : (Sch/U)_{fppf} → Curves`, the base change `(Sch/U)_{fppf} ×_{Curves} Curves^P` is
represented by an open subscheme of `U`. That is the content of the source's statement that
`Curves^P` is an open substack; the source passes through a smooth presentation of the algebraic
stack `Curves`, which is not needed for the open immersion itself.

It also proves the factorization criterion: a 1-morphism `(Sch/U)_{fppf} → Curves` factors
through `Curves^P`, over the site and up to a 2-isomorphism, exactly when the family of curves
it classifies has `P`.

Condition (o) is taken in the form `AlgebraicGeometry.CurveFamily.exists_isOpenSubspace_smooth`
and its siblings produce: for every family `G` there is an open subspace `W` of its base such that
a family `F` with a morphism `F ⟶ G` — a base change of `G` — has `P` exactly when its morphism
of base schemes factors through `W`.

## Main definitions

* `AlgebraicGeometry.curvesSubFiberedCategory`: the strictly full subcategory `Curves^P`, as a
  category fibred in groupoids over the big fppf site.
* `AlgebraicGeometry.curvesSubInclusion`: its inclusion into `Curves`, as a 1-morphism.

## Main results

* `AlgebraicGeometry.isRepresentableByAlgebraicSpaces_curvesSubInclusion` and
  `AlgebraicGeometry.isOpenImmersion_curvesSubInclusion`: the inclusion is representable by
  algebraic spaces and an open immersion.
* `AlgebraicGeometry.exists_factorization_curvesSubInclusion_iff`: the factorization criterion.

## Implementation notes

The algebraicity of `Curves` (Stacks 0D5A) is not used: being representable by algebraic spaces
and an open immersion are properties of a 1-morphism of categories fibred in groupoids, and the
base change along a scheme-valued point is computed directly. The base change is fibred in
setoids, its fibres being thin because the inclusion of a full subcategory is faithful, and it is
identified with the category of elements of the representable presheaf of the open subscheme by
Stacks 02ZX in the form `AlgebraicGeometry.exists_equivalenceOver_elements_of_setoids`.

## References

* [Stacks Project, Section 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v t

namespace AlgebraicGeometry

/-! ### Open immersions out of a representable presheaf over a smaller base -/

/-- An algebraic space over a scheme `U` of the site which is isomorphic to the presheaf of an
object `V` over `U` whose structure morphism is an open immersion has open immersion structure
morphism when read as an algebraic space over `S`, through the equivalence of Stacks 04SG. -/
theorem Space.isOpenImmersion_algebraicSpaceMap_of_iso_yoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (V : BigFppfOver B U.left.1 U.left.2)
    (hV : _root_.AlgebraicGeometry.IsOpenImmersion (B.inclusion.map V.hom))
    (e : F ≅ yoneda.obj V) :
    Space.IsOpenImmersion B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  classical
  let i := spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom
  let K := spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom
  let V' : BigFppfOver B S hS := Over.mk (V.hom ≫ U.hom)
  let j' : V' ⟶ Over.mk U.hom := Over.homMk V.hom rfl
  let d : (K.obj ⟨F, hF⟩).1.left ≅ yoneda.obj V' :=
    i.app ⟨F, hF⟩ ≪≫
      (OverShriek.relocalizePresheafFunctor U.hom).mapIso e ≪≫
      (OverShriek.relocalizeYonedaIso U.hom).app V
  have hd : (K.obj ⟨F, hF⟩).1.hom = d.hom ≫ yoneda.map j' := by
    ext W x
    let s := (i.hom.app ⟨F, hF⟩).app W x
    have hx : (i.inv.app ⟨F, hF⟩).app W s = x :=
      congrArg (fun t => t.app W x) (i.app ⟨F, hF⟩).hom_inv_id
    have hs := spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
      B U.left.1 S U.left.2 hS U.hom ⟨F, hF⟩ W s
    rw [hx] at hs
    apply Over.OverMorphism.ext
    change (((K.obj ⟨F, hF⟩).1.hom).app W x).left = (d.hom.app W x).left ≫ V.hom
    rw [hs]
    change s.1.1 = (d.hom.app W x).left ≫ V.hom
    let q : Over.mk s.1.1 ⟶ V := e.hom.app (Opposite.op (Over.mk s.1.1)) s.1.2
    have hq : (d.hom.app W x).left = q.left := rfl
    rw [hq]
    exact (Over.w q).symm
  have hj : Space.IsOpenImmersion B S hS (yoneda.map j') := by
    let Tf := BigFppfOver.toScheme B S hS
    let P₀ := MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) Tf
    let : P₀.IsStableUnderBaseChange := ⟨by
      intro X Y Y' R f g f' g' h hg
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @AlgebraicGeometry.IsOpenImmersion) (h.map Tf) hg⟩
    exact MorphismProperty.relative_map (P := P₀) hV
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    MorphismProperty.presheaf
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))
  have : P.RespectsIso := inferInstance
  change P ((K.obj ⟨F, hF⟩).1.hom)
  rw [hd]
  exact MorphismProperty.RespectsIso.precomp P d.hom (yoneda.map j') hj

/-! ### Full subcategories whose base changes are open subschemes

The following statements are about an arbitrary category `D` fibred in groupoids over the big
fppf site of `S` and a property `P` of its objects stable under pullback, under the hypothesis
that for every scheme-valued point `y : (Sch/U)_{fppf} → D` the objects of `D` over `y` having
`P` are those over an open subscheme `V ⊂ U`. They are used for the stack of curves and for its
model with small hom-sets. -/

section GenericOpenLocus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : Type t} [Category.{v} D] (p : D ⥤ BigFppfOver B S hS)
  (P : ObjectProperty D) (hP : ∀ {x y : D}, (x ⟶ y) → P y → P x)

include hP in
/-- The full subcategory of a category fibred in groupoids cut out by a property stable under
pullback is fibred in groupoids. -/
theorem fullSubcategory_comp_isFiberedInGroupoids (hp : p.IsFiberedInGroupoids) :
    (P.ι ⋙ p).IsFiberedInGroupoids := by
  have : p.IsFibered := hp.isFibered
  have hclosed : Functor.ClosedUnderStronglyCartesian p P := fun _ φ _ hx =>
    Functor.isoOverId_of_prop (hP φ hx)
  have hFib : (P.ι ⋙ p).IsFibered := Functor.isFibered_restrict_of_closed p P hclosed
  have hGroups : ∀ U : BigFppfOver B S hS, IsGroupoid ((P.ι ⋙ p).Fiber U) := by
    intro U
    have hrfl : P.ι ⋙ p = P.ι ⋙ p := rfl
    set L := Functor.Fiber.mapOfComp (P.ι ⋙ p) p P.ι hrfl U with hL
    have : L.Full := Functor.Fiber.full_mapOfComp hrfl U
    have : L.Faithful := Functor.Fiber.faithful_mapOfComp hrfl U
    refine { all_isIso := fun f => ?_ }
    have : IsIso (L.map f) := (hp.fiber_isGroupoid U).all_isIso (L.map f)
    exact isIso_of_fully_faithful L f
  exact Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid.mpr ⟨hFib, hGroups⟩

/-- There is at most one morphism of the site into an object whose structure morphism is an open
immersion: an open immersion is a monomorphism. -/
theorem subsingleton_hom_of_isOpenImmersion {U : BigFppfOver B S hS}
    (V : BigFppfOver B U.left.1 U.left.2)
    (hV : _root_.AlgebraicGeometry.IsOpenImmersion (B.inclusion.map V.hom))
    (T : BigFppfOver B U.left.1 U.left.2) : Subsingleton (T ⟶ V) := by
  let : Mono (B.inclusion.map V.hom) := hV.mono
  constructor
  intro f g
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  apply (cancel_mono (B.inclusion.map V.hom)).mp
  rw [← Functor.map_comp, ← Functor.map_comp, Over.w f, Over.w g]

include hP in
/-- If the objects with `P` over a scheme-valued point `y` with values in `U` are exactly those
over an open subscheme `V ⊂ U`, the base change of the inclusion of the full subcategory along
`y` is equivalent over the site to the category of elements of the presheaf represented by
`V`. -/
theorem nonempty_equivalenceOver_baseChange_of_open (hp : p.IsFiberedInGroupoids)
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ D)
    (hy : y ⋙ p = Over.map U.hom) (V : BigFppfOver B U.left.1 U.left.2)
    (hV : _root_.AlgebraicGeometry.IsOpenImmersion (B.inclusion.map V.hom))
    (hchar : ∀ T : BigFppfOver B U.left.1 U.left.2, P (y.obj T) ↔ Nonempty (T ⟶ V)) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (P.ι ⋙ p) p y P.ι)
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p) := by
  classical
  set q := TwoFibreProductOver.fst (Over.map U.hom) (P.ι ⋙ p) p y P.ι with hqdef
  have hrfl : P.ι ⋙ p = P.ι ⋙ p := rfl
  have hgroup : q.IsFiberedInGroupoids :=
    Stack.fst_isFiberedInGroupoids_overMap U.hom (P.ι ⋙ p) p y P.ι
      (fullSubcategory_comp_isFiberedInGroupoids p P hP hp) hp hy rfl
  have hsetoid : q.IsFiberedInSetoids :=
    ⟨hgroup, fun T => TwoFibreProductOver.fiber_isThin_fst_of_faithful T⟩
  have hsubtarget := subsingleton_hom_of_isOpenImmersion V hV
  have hsubsource : ∀ T, Subsingleton (q.isoClassPresheaf.obj T) := by
    intro T
    refine ⟨fun c d => ?_⟩
    obtain ⟨A, rfl⟩ := Functor.isoClassMk_surjective c
    obtain ⟨C, rfl⟩ := Functor.isoClassMk_surjective d
    obtain ⟨f⟩ := TwoFibreProductOver.nonempty_fst_fiber_hom_of_full_fiber
      (Over.map U.hom) (P.ι ⋙ p) p y P.ι hrfl
      (fun W => Functor.Fiber.full_mapOfComp hrfl W) A C
    have : IsIso f := (hgroup.fiber_isGroupoid T.unop).all_isIso f
    exact Functor.isoClassMk_eq_of_iso (asIso f)
  have hprop : ∀ (T : BigFppfOver B U.left.1 U.left.2) (A : q.Fiber T), P (y.obj T) := by
    intro T A
    obtain ⟨A, rfl⟩ := A
    exact hP A.iso.hom A.y.property
  let fibreOf : ∀ (T : BigFppfOver B U.left.1 U.left.2), P (y.obj T) → q.Fiber T :=
    fun T h => ⟨{ base := (Over.map U.hom).obj T
                  x := T
                  y := ⟨y.obj T, h⟩
                  hx := rfl
                  hy := Functor.congr_obj hy T
                  iso := Iso.refl _
                  vertical := IsHomLift.id (Functor.congr_obj hy T) }, rfl⟩
  refine exists_equivalenceOver_elements_of_setoids q _ (fun T => ?_) ?_
  · have := hsubtarget T.unop
    exact
      { toFun := fun c => by
          refine Classical.choice ((hchar T.unop).mp ?_)
          obtain ⟨A, -⟩ := Functor.isoClassMk_surjective c
          exact hprop T.unop A
        invFun := fun s => Functor.isoClassMk q (fibreOf T.unop ((hchar T.unop).mpr ⟨s⟩))
        left_inv := fun _ => (hsubsource T).elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  · intro T T' g x
    have := hsubtarget T'.unop
    exact Subsingleton.elim _ _

include hP in
/-- In the situation of `AlgebraicGeometry.nonempty_equivalenceOver_baseChange_of_open`, every
algebraic space representing the base change has open immersion structure morphism. -/
theorem isOpenImmersion_of_baseChange_of_open (hp : p.IsFiberedInGroupoids)
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ D)
    (hy : y ⋙ p = Over.map U.hom) (V : BigFppfOver B U.left.1 U.left.2)
    (hV : _root_.AlgebraicGeometry.IsOpenImmersion (B.inclusion.map V.hom))
    (hchar : ∀ T : BigFppfOver B U.left.1 U.left.2, P (y.obj T) ↔ Nonempty (T ⟶ V))
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (P.ι ⋙ p) p y P.ι)
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Space.IsOpenImmersion B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  obtain ⟨eV⟩ := nonempty_equivalenceOver_baseChange_of_open p P hP hp U y hy V hV hchar
  set q := TwoFibreProductOver.fst (Over.map U.hom) (P.ι ⋙ p) p y P.ι
  have hgroup : q.IsFiberedInGroupoids :=
    Stack.fst_isFiberedInGroupoids_overMap U.hom _ _ y _
      (fullSubcategory_comp_isFiberedInGroupoids p P hP hp) hp hy rfl
  have : q.IsFibered := hgroup.isFibered
  have hsub := subsingleton_hom_of_isOpenImmersion V hV
  let i : F ≅ yoneda.obj V := NatIso.ofComponents
    (fun T => ((PresheafOfCategories.elementsIsoClassEquiv F eF T.unop).symm.trans
      (PresheafOfCategories.elementsIsoClassEquiv (yoneda.obj V) eV T.unop)).toIso)
    (by
      intro T T' g
      have := hsub T'.unop
      ext x
      exact Subsingleton.elim _ _)
  exact Space.isOpenImmersion_algebraicSpaceMap_of_iso_yoneda B S hS U F hF V hV i

end GenericOpenLocus

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### The strictly full subcategory cut out by a property of families of curves -/

section Sub

variable (P : ObjectProperty (CurveFamily B hZ))
  (hP : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → P G → P F)

include hP in
/-- The full subcategory of families of curves cut out by a property inherited along morphisms of
families (that is, stable under base change) is fibred in groupoids over the big fppf site. -/
theorem curvesSubProjection_isFiberedInGroupoids :
    (P.ι ⋙ curvesProjectionOver B hZ).IsFiberedInGroupoids :=
  fullSubcategory_comp_isFiberedInGroupoids _ P hP (curvesFiberedCategory B hZ).property

/-- The strictly full subcategory `Curves^P ⊂ Curves` cut out by a property of families of curves
stable under base change, as a category fibred in groupoids over the big fppf site. -/
def curvesSubFiberedCategory :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (P.ι ⋙ curvesProjectionOver B hZ))
    (curvesSubProjection_isFiberedInGroupoids B hZ P hP)

/-- The inclusion `Curves^P ⟶ Curves`, as a 1-morphism of categories fibred in groupoids. -/
def curvesSubInclusion : curvesSubFiberedCategory B hZ P hP ⟶ curvesFiberedCategory B hZ :=
  Bicategory.InducedBicategory.mkHom ({ toFunctor := P.ι, w := rfl })

/-- **The factorization criterion.** A 1-morphism `y : (Sch/U)_{fppf} → Curves` factors through
`Curves^P`, over the site and up to a 2-isomorphism, exactly when the family of curves it
classifies — its value `y(id_U)` at the terminal object — has `P`. -/
theorem exists_factorization_curvesSubInclusion_iff (U : BigFppfOver B integerBase hZ)
    (y : BasedCategory.ofFunctor (Over.map U.hom) ⥤ᵇ (curvesFiberedCategory B hZ).val) :
    (∃ g : BasedCategory.ofFunctor (Over.map U.hom) ⥤ᵇ (curvesSubFiberedCategory B hZ P hP).val,
        Nonempty (g.comp (curvesSubInclusion B hZ P hP).hom ≅ y)) ↔
      P (y.obj (Over.mk (𝟙 U.left))) := by
  constructor
  · rintro ⟨g, ⟨α⟩⟩
    have e := ((BasedNatTrans.forgetful _ _).mapIso α).app (Over.mk (𝟙 U.left))
    exact hP e.inv (g.obj (Over.mk (𝟙 U.left))).property
  · intro h
    have hall : ∀ T : BigFppfOver B U.left.1 U.left.2, P (y.obj T) := fun T =>
      hP (y.map (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 U.left))) h
    exact ⟨⟨P.lift y.toFunctor hall, y.w⟩, ⟨BasedNatIso.id _⟩⟩

end Sub

/-! ### The open subscheme over a scheme-valued point -/

section Open

variable (P : ObjectProperty (CurveFamily B hZ))
  (hO : ∀ G : CurveFamily B hZ, ∃ W : Subfunctor (schemeSpace G.base).obj,
    Space.IsOpenSubspace B integerBase hZ W ∧
    ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
      P F ↔ ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
        t ≫ W.ι = (schemeSpaceMap a.baseMap).hom)

include hO in
/-- Condition (o) makes `P` stable under base change: a family mapping to a family with `P` has
`P`. -/
theorem prop_of_hom_of_exists_isOpenSubspace {F G : CurveFamily B hZ} (a : F ⟶ G) (hG : P G) :
    P F := by
  obtain ⟨W, -, hW⟩ := hO G
  obtain ⟨t, ht⟩ := (hW G (𝟙 G)).mp hG
  refine (hW F a).mpr ⟨(schemeSpaceMap a.baseMap).hom ≫ t, ?_⟩
  rw [Category.assoc, ht]
  exact (congrArg (fun k => (schemeSpaceMap a.baseMap).hom ≫ k) (yoneda.map_id G.base)).trans
    (Category.comp_id _)

include hO in
/-- **The locus over a scheme-valued point is represented by an open subscheme.** Over a
scheme-valued point `y : (Sch/U)_{fppf} → Curves` there is an object `V` of the site over `U`
whose structure morphism is an open immersion and which receives a morphism from `T` exactly when
the family of curves `y(T)` has `P`.

The open is the open subspace of condition (o) for the family `y(id_U)`, represented by an open
subscheme of `U` by part (1) of Stacks 03BZ; the family `y(T)` maps to `y(id_U)` over the structure
morphism of `T`, so it has `P` exactly when that structure morphism factors through the open. -/
theorem exists_open_over_iff_of_exists_isOpenSubspace (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      IsOpenImmersion (B.inclusion.map V.hom) ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2, P (y.obj T) ↔ Nonempty (T ⟶ V) := by
  classical
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let G := y.obj T₀
  have h₁ : G.base = (Over.map U.hom).obj T₀ := congrArg (fun F => F.obj T₀) hy
  have h₂ : (Over.map U.hom).obj T₀ = U := by cases U; congr 1
  let β : G.base ≅ U := eqToIso (h₁.trans h₂)
  obtain ⟨W₁, hW₁, hWchar₁⟩ := hO G
  let W : Subfunctor (yoneda.obj G.base) := W₁
  have hW : Space.IsOpenSubspace B integerBase hZ W := hW₁
  have hWchar : ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
      P F ↔ ∃ t : yoneda.obj F.base ⟶ W.toFunctor, t ≫ W.ι = yoneda.map a.baseMap :=
    fun F a => hWchar₁ F a
  -- the open subspace `W` is represented by an open subscheme `V₀ ⟶ G.base` (Stacks 03BZ)
  let hpb := hW.2.rep.isPullback (𝟙 (yoneda.obj G.base))
  let V₀ := hW.2.rep.pullback (𝟙 (yoneda.obj G.base))
  let j : V₀ ⟶ G.base := hW.2.rep.snd (𝟙 (yoneda.obj G.base))
  let eMap := hW.2.rep.fst (𝟙 (yoneda.obj G.base))
  have : IsIso eMap := hpb.isIso_fst_of_isIso
  have hj : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) :=
    hW.2.property_snd (𝟙 (yoneda.obj G.base))
  let e : yoneda.obj V₀ ≅ W.toFunctor := asIso eMap
  have he : e.hom ≫ W.ι = yoneda.map j := by
    simpa only [e, eMap, j, asIso_hom, Category.comp_id] using hpb.w
  have he' : e.inv ≫ yoneda.map j = W.ι := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let j' : V₀ ⟶ U := j ≫ β.hom
  let V' : BigFppfOver B U.left.1 U.left.2 := Over.mk j'.left
  have hj' : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j') := by
    change IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map (j ≫ β.hom))
    rw [Functor.map_comp]
    infer_instance
  refine ⟨V', hj', fun T => ?_⟩
  let t : T ⟶ T₀ := Over.homMk T.hom (by simp [T₀])
  let a : y.obj T ⟶ G := y.map t
  have hT : (y.obj T).base = (Over.map U.hom).obj T := congrArg (fun F => F.obj T) hy
  let α : (y.obj T).base ≅ (Over.map U.hom).obj T := eqToIso hT
  have hcanon : (Over.map U.hom).map t ≫ eqToHom h₂ =
      (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by cases U; rfl
  have hcomm : a.baseMap ≫ β.hom =
      α.hom ≫ (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
    have hhy' : a.baseMap = eqToHom hT ≫ (Over.map U.hom).map t ≫ eqToHom h₁.symm :=
      Functor.congr_hom hy t
    rw [hhy', ← hcanon]
    simp [β, α, Category.assoc]
  -- a map `k` lifts `a.baseMap` through `j` exactly when `α.inv ≫ k` lifts the structure map
  have key : ∀ k : (y.obj T).base ⟶ V₀, k ≫ j = a.baseMap ↔
      (α.inv ≫ k) ≫ j' = (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
    intro k
    have h₃ : (α.inv ≫ k) ≫ j' = α.inv ≫ ((k ≫ j) ≫ β.hom) := by simp [j']
    have h₄ : (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) =
        α.inv ≫ (a.baseMap ≫ β.hom) := by rw [hcomm]; simp
    rw [h₃, h₄, cancel_epi, cancel_mono]
  rw [hWchar (y.obj T) a]
  constructor
  · rintro ⟨s, hs⟩
    -- the factorization through `W` is a factorization through `V₀`
    let k : (y.obj T).base ⟶ V₀ := yoneda.preimage (s ≫ e.inv)
    have hk : k ≫ j = a.baseMap := by
      apply yoneda.map_injective
      calc
        yoneda.map (k ≫ j) = (s ≫ e.inv) ≫ yoneda.map j := by
          rw [Functor.map_comp, yoneda.map_preimage]
        _ = s ≫ W.ι := by rw [Category.assoc, he']
        _ = yoneda.map a.baseMap := hs
    have hl := (key k).mp hk
    exact ⟨Over.homMk (α.inv ≫ k).left
      (congrArg (fun f : (Over.map U.hom).obj T ⟶ U => f.left) hl)⟩
  · rintro ⟨m⟩
    let l : (Over.map U.hom).obj T ⟶ V₀ := Over.homMk m.left (by
      calc
        m.left ≫ V₀.hom = m.left ≫ j'.left ≫ U.hom := by rw [Over.w j']
        _ = T.hom ≫ U.hom := by
          have hm : m.left ≫ j'.left = T.hom := m.w
          simpa [Category.assoc] using congrArg (fun f => f ≫ U.hom) hm)
    have hl : l ≫ j' = (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
      apply Over.OverMorphism.ext
      exact Over.w m
    let k : (y.obj T).base ⟶ V₀ := α.hom ≫ l
    have hk : k ≫ j = a.baseMap := (key k).mpr (by simpa [k] using hl)
    refine ⟨yoneda.map k ≫ e.hom, ?_⟩
    rw [Category.assoc, he, ← Functor.map_comp, hk]

end Open

/-! ### Representability by algebraic spaces and openness of the inclusion -/

section Immersion

variable (P : ObjectProperty (CurveFamily B hZ))
  (hO : ∀ G : CurveFamily B hZ, ∃ W : Subfunctor (schemeSpace G.base).obj,
    Space.IsOpenSubspace B integerBase hZ W ∧
    ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
      P F ↔ ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
        t ≫ W.ι = (schemeSpaceMap a.baseMap).hom)

include hO in
/-- **The inclusion `Curves^P ⟶ Curves` is representable by algebraic spaces** (Stacks 02ZW): its
base change along a scheme-valued point is represented by an open subscheme of the base. -/
theorem isRepresentableByAlgebraicSpaces_curvesSubInclusion :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
      (curvesSubInclusion B hZ P (prop_of_hom_of_exists_isOpenSubspace B hZ P hO)).hom := by
  intro U
  dsimp only
  intro y hy
  obtain ⟨V, hV, hchar⟩ := exists_open_over_iff_of_exists_isOpenSubspace B hZ P hO U y hy
  exact ⟨yoneda.obj V, isAlgebraicSpace_yoneda B U.left.1 U.left.2 V,
    nonempty_equivalenceOver_baseChange_of_open _ P
      (prop_of_hom_of_exists_isOpenSubspace B hZ P hO) (curvesFiberedCategory B hZ).property
      U y hy V hV hchar⟩

include hO in
/-- **The inclusion `Curves^P ⟶ Curves` is an open immersion** (Stacks 04XB): every algebraic space
representing its base change along a scheme-valued point is isomorphic to the presheaf of an open
subscheme of the base, so its structure morphism is an open immersion. -/
theorem isOpenImmersion_curvesSubInclusion :
    Stack.IsOpenImmersion B integerBase hZ
      (curvesSubInclusion B hZ P (prop_of_hom_of_exists_isOpenSubspace B hZ P hO)) := by
  intro U y hy F hF heF
  obtain ⟨V, hV, hchar⟩ := exists_open_over_iff_of_exists_isOpenSubspace B hZ P hO U y hy
  exact isOpenImmersion_of_baseChange_of_open _ P
    (prop_of_hom_of_exists_isOpenSubspace B hZ P hO) (curvesFiberedCategory B hZ).property
    U y hy V hV hchar F hF heF.some

end Immersion

end AlgebraicGeometry

end
