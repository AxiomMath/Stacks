module

public import Mathlib.RingTheory.Henselian
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperHenselianPairSections
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria.Characterizations

/-!
# Sections of étale morphisms over a proper base

Let `(A, I)` be a henselian pair (for instance `A` complete with respect to `I`), let `X` be an
algebraic space proper over `Spec A` and let `q : X' ⟶ X` be étale and an isomorphism over the
closed fibre `X_0 = X ×_{Spec A} Spec (A ⧸ I)`. Then `q` has a section. This is proper base change
in degree zero for the sheaf on `X_étale` represented by `X'`; `X'` need not be separated over `X`.

## Main results

* `AlgebraicGeometry.Space.exists_section_of_isEtale_of_isIso_adicFibreMap_of_henselianPair` and
  `AlgebraicGeometry.Space.exists_section_of_isEtale_of_isIso_adicFibreMap`: the statement, over a
  henselian pair and over a complete Noetherian ring.
* `AlgebraicGeometry.Space.nonempty_hom_idObj_of_globalSections`: a global section of the small
  étale sheaf represented by an étale `V ⟶ X` is a section of `V ⟶ X`.
* `AlgebraicGeometry.Space.nonempty_globalSections_inverseImage`: if the base change of `V` along
  `i : Y ⟶ X` is final, the inverse image along `i` of that sheaf has a global section.
* `AlgebraicGeometry.Space.isIso_of_isPullback_closedFibre_of_isIso_adicFibreMap`: an isomorphism
  on the first adic fibre is an isomorphism over `X ×_{Spec A} Spec (A ⧸ I)`.

## Implementation notes

The proof does not go through Chow's lemma: it applies Stacks 0DFY
(`AlgebraicGeometry.Space.isIso_globalSectionsRestriction_closedFibre_of_henselianPair`), proper
base change in degree zero for sheaves of sets on `X_étale`, to the sheaf represented by the
object `X'` of the spaces-étale site of `X`, transported to the small étale site. Its inverse
image on `X_0` is represented by `X' ×_X X_0` (Stacks 04D3,
`CategoryTheory.Adjunction.yonedaIso`), which is final in the spaces-étale site of `X_0` because
`q` is an isomorphism there; so it has a global section, and the bijectivity of restriction gives
a global section over `X`, that is a morphism `X ⟶ X'` over `X`.

## References

* [Stacks Project, Tag 0DFY](https://stacks.math.columbia.edu/tag/0DFY)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
* [Stacks Project, Tag 0A0B](https://stacks.math.columbia.edu/tag/0A0B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- Discrete limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_etaleSectionOverProperBase
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- Let `q : X' ⟶ X` and let `a : P ⟶ Y` be the base change of `q` along `k ≫ j`. If the base
change `c : Q ⟶ Z` of `q` along `j` is an isomorphism, so is `a`. -/
theorem isIso_of_isPullback_comp {C : Type*} [Category C] {P Q Y Z X' X : C} {q : X' ⟶ X}
    {j : Z ⟶ X} {k : Y ⟶ Z} {a : P ⟶ Y} {b : P ⟶ X'} (h : IsPullback a b (k ≫ j) q)
    {c : Q ⟶ Z} {d : Q ⟶ X'} (h' : IsPullback c d j q) [IsIso c] : IsIso a := by
  have t : IsPullback a (h'.lift (a ≫ k) b (by rw [Category.assoc, h.w])) k c :=
    IsPullback.of_bot (by simpa using h) (by simp) h'
  exact t.isIso_fst_of_isIso

section ClosedFibre

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}

/-- The closed immersion `Spec (A ⧸ I) ⟶ Spec (A ⧸ I ^ 1)` lies over `Spec A`. -/
theorem spec_factor_comp_adicThickeningι :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (show I ^ (0 + 1) ≤ I by rw [zero_add, pow_one]))) ≫ adicThickeningι A I 0 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [adicThickeningι, ← Spec.map_comp]
  rfl

variable (A I B hS hSn) in
/-- The closed subscheme `Spec (A ⧸ I)` of `Spec A` maps to the first adic thickening
`Spec (A ⧸ I ^ 1)`, as objects of the big fppf site over `Spec A`. -/
def quotientSpecOverToAdicThickening :
    quotientSpecOver A I hS ⟶ adicThickeningObject A I B hS hSn 0 :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (show I ^ (0 + 1) ≤ I by rw [zero_add, pow_one]))))) (ObjectProperty.hom_ext _
    spec_factor_comp_adicThickeningι)

/-- The comparison of `Spec (A ⧸ I)` with the first adic thickening lies over `Spec A`. -/
@[reassoc (attr := simp)]
theorem quotientSpecOverToAdicThickening_adicThickeningMap :
    quotientSpecOverToAdicThickening A I B hS hSn ≫ adicThickeningMap A I B hS hSn 0 =
      quotientSpecOverHom A I hS := by
  ext
  exact spec_factor_comp_adicThickeningι

/-- Let `q : X' ⟶ X` be a morphism of presheaves over `Spec A` whose first adic fibre is an
isomorphism. Then every base change of `q` along the inclusion
`X ×_{Spec A} Spec (A ⧸ I) ⟶ X` of the closed fibre is an isomorphism. -/
theorem isIso_of_isPullback_closedFibre_of_isIso_adicFibreMap
    {X X' P : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} (q : X' ⟶ X)
    (h0 : IsIso (adicFibreMap A I B hS hSn q (rfl : q ≫ fX = q ≫ fX) 0))
    {a : P ⟶ pullback fX (yoneda.map (quotientSpecOverHom A I hS))} {b : P ⟶ X'}
    (h : IsPullback a b (pullback.fst fX (yoneda.map (quotientSpecOverHom A I hS))) q) :
    IsIso a := by
  set t0 := yoneda.map (adicThickeningMap A I B hS hSn 0)
  set e := yoneda.map (quotientSpecOverToAdicThickening A I B hS hSn)
  have he : e ≫ t0 = yoneda.map (quotientSpecOverHom A I hS) := by
    rw [← yoneda.map_comp, quotientSpecOverToAdicThickening_adicThickeningMap]
  let k : pullback fX (yoneda.map (quotientSpecOverHom A I hS)) ⟶ pullback fX t0 :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e) (by
      rw [Category.assoc, he, pullback.condition])
  have hk : k ≫ pullback.fst fX t0 = pullback.fst fX (yoneda.map (quotientSpecOverHom A I hS)) :=
    pullback.lift_fst _ _ _
  have h' : IsPullback (adicFibreMap A I B hS hSn q (rfl : q ≫ fX = q ≫ fX) 0)
      (pullback.fst (q ≫ fX) t0) (pullback.fst fX t0) q := by
    refine IsPullback.of_right ?_ (adicFibreMap_fst A I B hS hSn q rfl 0)
      (IsPullback.of_hasPullback fX t0).flip
    rw [adicFibreMap_snd]
    exact (IsPullback.of_hasPullback (q ≫ fX) t0).flip
  rw [← hk] at h
  exact isIso_of_isPullback_comp h h'

end ClosedFibre

section SheafOfSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse image of the small étale topoi along a morphism of algebraic spaces, unfolded:
it is the inverse image of the spaces-étale morphism of sites, conjugated by the comparison
equivalences. -/
theorem smallToposMorphism_inverseImage_eq {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (smallToposMorphism B S hS f).inverseImage =
      (smallEtaleToposEquiv B S hS Y).inverse ⋙
        (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi.inverseImage ⋙
          (smallEtaleToposEquiv B S hS X).functor :=
  rfl

/-- A global section of the small étale sheaf represented by an object `V` of the spaces-étale
site of `X` is a morphism from the final object `X` to `V`: a section of `V ⟶ X`. -/
theorem nonempty_hom_idObj_of_globalSections {X : AlgebraicSpaces B S hS}
    (V : SpacesEtale B S hS X)
    (x : (Sheaf.Γ (SmallEtale.topology B S hS X.1) (Type (u + 1))).obj
      ((smallEtaleToposEquiv B S hS X).functor.obj
        ((SpacesEtale.topology B S hS X).yoneda.obj V))) :
    Nonempty (SpacesEtale.idObj B S hS X ⟶ V) := by
  let J := SpacesEtale.topology B S hS X
  let Js := SmallEtale.topology B S hS X.1
  let eX := smallEtaleToposEquiv B S hS X
  let n := Sheaf.ΓObjEquivHom (SmallEtale.topology B S hS X.1) _ PUnit.{u + 2} x
  let hP := (Stacks.Sites.isTerminalConstantSheafPUnit.{u, u + 1} Js).isTerminalObj eX.inverse
  let c : J.yoneda.obj (SpacesEtale.idObj B S hS X) ⟶ J.yoneda.obj V :=
    hP.from _ ≫ eX.inverse.map n ≫ eX.unitIso.inv.app _
  exact ⟨J.yonedaEquiv c⟩

/-- Let `i : Y ⟶ X` be a morphism of algebraic spaces and `V` an object of the spaces-étale
site of `X` whose base change along `i` is final. Then the inverse image along `i` of the small
étale sheaf represented by `V` has a global section. -/
theorem nonempty_globalSections_inverseImage {X Y : AlgebraicSpaces B S hS} (i : Y ⟶ X)
    (V : SpacesEtale B S hS X)
    (hV : IsTerminal ((spacesBaseChange B S hS i).functor.obj V)) :
    Nonempty ((Sheaf.Γ (SmallEtale.topology B S hS Y.1) (Type (u + 1))).obj
      ((smallToposMorphism B S hS i).inverseImage.obj
        ((smallEtaleToposEquiv B S hS X).functor.obj
          ((SpacesEtale.topology B S hS X).yoneda.obj V)))) := by
  let bc := (spacesBaseChange B S hS i).functor
  let J := SpacesEtale.topology B S hS X
  let J0 := SpacesEtale.topology B S hS Y
  let Js0 := SmallEtale.topology B S hS Y.1
  let φ := (spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi
  let adj : φ.inverseImage ⊣ bc.sheafPushforwardContinuous (Type (u + 1)) J J0 := φ.adj
  let eX := smallEtaleToposEquiv B S hS X
  let eY := smallEtaleToposEquiv B S hS Y
  let G0 := eY.functor.obj (J0.yoneda.obj (bc.obj V))
  let y0 : (Sheaf.Γ Js0 (Type (u + 1))).obj G0 :=
    (Sheaf.ΓObjEquivSections Js0 G0).symm ⟨fun _ => hV.from _, fun _ => hV.hom_ext _ _⟩
  let ψ : G0 ⟶ eY.functor.obj (φ.inverseImage.obj (eX.inverse.obj
      (eX.functor.obj (J.yoneda.obj V)))) :=
    eY.functor.map ((adj.yonedaIso V).inv ≫ φ.inverseImage.map (eX.unitIso.hom.app _))
  rw [smallToposMorphism_inverseImage_eq]
  exact ⟨(Sheaf.Γ Js0 (Type (u + 1))).map ψ y0⟩

end SheafOfSections

section Section

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}

/-- **Sections of étale morphisms over a proper base, from the closed fibre.** Let `(A, I)` be a
henselian pair, let `X` be an algebraic space proper over `Spec A`, and let `q : X' ⟶ X` be an
étale morphism of algebraic spaces whose first adic fibre `X'_0 ⟶ X_0` over `Spec (A ⧸ I)` is an
isomorphism. Then `q` has a section.

No separation or finiteness hypothesis on `q` is needed: the section is a global section of the
sheaf on `X_étale` represented by `X'`, and such global sections are those over the closed fibre
by Stacks 0DFY, where the inverse image of that sheaf is represented by `X'_0 ≅ X_0`. -/
theorem exists_section_of_isEtale_of_isIso_adicFibreMap_of_henselianPair
    (hI : HenselianPair A I) {X X' : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B _ hS X) (hX' : IsAlgebraicSpace B _ hS X')
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} (hpX : IsProper B _ hS fX)
    (q : X' ⟶ X) (hq : IsEtale B _ hS q)
    (h0 : IsIso (adicFibreMap A I B hS hSn q (rfl : q ≫ fX = q ≫ fX) 0)) :
    ∃ σ : X ⟶ X', σ ≫ q = 𝟙 X := by
  let 𝕏 : AlgebraicSpaces B (Spec (.of A)) hS := ⟨X, hX⟩
  let 𝕏' : AlgebraicSpaces B (Spec (.of A)) hS := ⟨X', hX'⟩
  let f : 𝕏 ⟶ ⟨yoneda.obj (Over.mk (𝟙 (B.obj hS))),
      isAlgebraicSpace_yoneda B (Spec (.of A)) hS (Over.mk (𝟙 (B.obj hS)))⟩ :=
    ObjectProperty.homMk fX
  let i := closedFibreInclusion A I hS 𝕏 f
  let qq : 𝕏' ⟶ 𝕏 := ObjectProperty.homMk q
  let V' : SpacesEtale B (Spec (.of A)) hS 𝕏 := ⟨Over.mk qq, hq⟩
  have hsnd : IsIso (pullback.snd qq i) := by
    have hpb := AlgebraicSpaces.isPullback_hom B _ hS (IsPullback.of_hasPullback qq i)
    have : IsIso (pullback.snd qq i).hom :=
      isIso_of_isPullback_closedFibre_of_isIso_adicFibreMap q h0 hpb.flip
    exact ⟨ObjectProperty.homMk (inv (pullback.snd qq i).hom),
      ObjectProperty.hom_ext _ (IsIso.hom_inv_id _),
      ObjectProperty.hom_ext _ (IsIso.inv_hom_id _)⟩
  have hV0 : IsTerminal ((spacesBaseChange B _ hS i).functor.obj V') :=
    SpacesEtale.isTerminal_of_isIso B _ hS _ hsnd
  have hr := isIso_globalSectionsRestriction_closedFibre_of_henselianPair A I hS 𝕏 f hI hpX
  obtain ⟨y⟩ := nonempty_globalSections_inverseImage B _ hS i V' hV0
  obtain ⟨x, -⟩ := ((isIso_iff_bijective ((globalSectionsRestriction B _ hS i).app
    ((smallEtaleToposEquiv B _ hS 𝕏).functor.obj
      ((SpacesEtale.topology B _ hS 𝕏).yoneda.obj V')))).1 inferInstance).2 y
  obtain ⟨s⟩ := nonempty_hom_idObj_of_globalSections B _ hS V' x
  refine ⟨s.hom.left.hom, ?_⟩
  have hw : (s.hom.left ≫ qq).hom = (𝟙 𝕏 : 𝕏 ⟶ 𝕏).hom :=
    congrArg (fun k => k.hom) (Over.w s.hom)
  exact hw

/-- **Sections of étale morphisms over a proper base, from the closed fibre.** Let `A` be a
ring complete with respect to an ideal `I`, let `X` be an algebraic space proper over `Spec A`, and
let `q : X' ⟶ X` be étale with first adic fibre `X'_0 ⟶ X_0` an isomorphism. Then `q` has a
section. `X'` need not be separated, quasi-compact or quasi-separated over `X`.

This is the case of `exists_section_of_isEtale_of_isIso_adicFibreMap_of_henselianPair` for the
henselian pair `(A, I)` of a complete ring. -/
theorem exists_section_of_isEtale_of_isIso_adicFibreMap [IsAdicComplete I A]
    {X X' : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B _ hS X) (hX' : IsAlgebraicSpace B _ hS X')
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} (hpX : IsProper B _ hS fX)
    (q : X' ⟶ X) (hq : IsEtale B _ hS q)
    (h0 : IsIso (adicFibreMap A I B hS hSn q (rfl : q ≫ fX = q ≫ fX) 0)) :
    ∃ σ : X ⟶ X', σ ≫ q = 𝟙 X :=
  exists_section_of_isEtale_of_isIso_adicFibreMap_of_henselianPair
    (henselianPair_of_henselianRing A I) hX hX' hpX q hq h0

end Section

end AlgebraicGeometry.Space

end
