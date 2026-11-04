module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# The composition law of Stacks 03G8 in inverse-image form

Stacks 03G8 attaches to a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` a morphism
`f_small` of their small étale ringed topoi and asserts that the construction respects
composition.  The library carries that assertion in *direct-image* form: the comparison
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso` of the direct images of sheaves
of commutative rings, and the equation
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp` for the structure maps
`f♯ : 𝒪_Y ⟶ f_*𝒪_X`.

This file transposes both across the adjunction `f⁻¹ ⊣ f_*`.  The outcome is a comparison
`p⁻¹f⁻¹ ≅ (p ≫ f)⁻¹` of inverse images of sheaves of commutative rings that is compatible with
the structure maps in their inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X`, and, for a commuting square

```
U --p--> X
|        |
g        f
v        v
V --q--> Y
```

the resulting isomorphism `p⁻¹f⁻¹𝒪_Y ≅ g⁻¹q⁻¹𝒪_Y` together with the agreement of the two
composite structure maps `p⁻¹f⁻¹𝒪_Y ⟶ p⁻¹𝒪_X ⟶ 𝒪_U` and `g⁻¹q⁻¹𝒪_Y ⟶ g⁻¹𝒪_V ⟶ 𝒪_U`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleInverseImageRing` is the inverse image of sheaves of
  commutative rings along `f_small`.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageIso` is the comparison of the
  iterated geometric inverse image with the inverse image along the composite.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso` is the same for
  sheaves of commutative rings.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_squareInverseImageRingIso` is the
  isomorphism `p⁻¹f⁻¹𝒪_Y ≅ g⁻¹q⁻¹𝒪_Y` attached to a commuting square.

## Main results

* `CategoryTheory.Adjunction.leftAdjointUniq_hom_app_comp_homEquiv_symm` and
  `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_hom_app_comp_homEquiv_symm`: the
  comparison of two left adjoints carries the adjunct for one adjunction to the adjunct for the
  other.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage`:
  **Stacks 03G8, the composition law in inverse-image form.**  The comparison followed by the
  structure map of the composite is the inverse image of the outer structure map followed by the
  inner one.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_squareInverseImageRingIso_fSharpInverseImage`:
  the isomorphism attached to a commuting square identifies the two composite structure maps.

## Implementation notes

The comparison of the inverse images is the mate of the comparison of the direct images: both are
left adjoints of the same direct image once the latter is transported along
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, so
`CategoryTheory.Adjunction.leftAdjointUniq` compares them.  The two adjunction lemmas above are
what makes the mate computable in practice: they say that appending the comparison to an adjunct
changes nothing but the adjunction it is taken for, so the structure-map compatibility reduces to
the direct-image equation it is transposed from.  They are stated here rather than with
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp`, of which they are the
`Equiv.symm` form, only to keep that file untouched.

The structure-map compatibility is proved on underlying sheaves of sets and then lifted through
the faithful `CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat)`.  Both steps are
in term mode: the sheaf of sets underlying the inverse image of a sheaf of commutative rings has
two spellings — through `AlgebraicGeometry.RingedTopos.Topos` and through the topology of the
site — which are definitionally but not syntactically equal, so `rw` produces terms that are not
type-correct at the implicit transparency level while `exact` accepts them.

The square comparison is the two composition comparisons with an `eqToIso` of the square's
equation between them.  That transport is unavoidable: `p ≫ f` and `g ≫ q` are equal morphisms
of algebraic spaces, so the two morphisms of ringed topoi attached to them are equal and not
merely isomorphic, and `AlgebraicGeometry.Space.eqToHom_comp_fSharpInverseImage` discharges the
transport by substituting the equation.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace CategoryTheory

universe v₁ u₁ v₂ u₂

/-- A morphism into the source of a natural isomorphism is recovered from its composite with the
forward direction by composing with the inverse. -/
private lemma natIso_comp_inv_app_eq {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F G : C ⥤ D} (e : F ≅ G) {A : C} {Z : D} {a : Z ⟶ F.obj A}
    {t : Z ⟶ G.obj A} (h : a ≫ e.hom.app A = t) : t ≫ e.inv.app A = a := by
  rw [← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

namespace Adjunction

/-- The canonical isomorphism of two left adjoints of one functor carries the adjunct of a
morphism for the second adjunction to its adjunct for the first.

This is the `Equiv.symm` form of
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp`. -/
lemma leftAdjointUniq_hom_app_comp_homEquiv_symm {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L L' : C ⥤ D} {R : D ⥤ C} (adj1 : L ⊣ R) (adj2 : L' ⊣ R) {X : C} {Y : D}
    (t : X ⟶ R.obj Y) :
    (adj1.leftAdjointUniq adj2).hom.app X ≫ (adj2.homEquiv X Y).symm t =
      (adj1.homEquiv X Y).symm t :=
  (adj1.homEquiv X Y).injective
    ((homEquiv_leftAdjointUniq_hom_app_comp adj1 adj2 ((adj2.homEquiv X Y).symm t)).trans
      (((adj2.homEquiv X Y).apply_symm_apply t).trans
        ((adj1.homEquiv X Y).apply_symm_apply t).symm))

/-- **The mate of an isomorphism of right adjoints, applied to an adjunct.**  For adjunctions
`adj1 : L ⊣ R` and `adj2 : L' ⊣ R'` and an isomorphism `ν : R ≅ R'`, the induced comparison
`L ≅ L'` carries the adjunct of `t` for `adj2` to the adjunct of `t ≫ ν⁻¹` for `adj1`. -/
lemma leftAdjointUniq_ofNatIsoRight_hom_app_comp_homEquiv_symm {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {L L' : C ⥤ D} {R R' : D ⥤ C} (adj1 : L ⊣ R) (adj2 : L' ⊣ R')
    (nu : R ≅ R') {X : C} {Y : D} (t : X ⟶ R'.obj Y) :
    ((adj1.ofNatIsoRight nu).leftAdjointUniq adj2).hom.app X ≫ (adj2.homEquiv X Y).symm t =
      (adj1.homEquiv X Y).symm (t ≫ nu.inv.app Y) :=
  (leftAdjointUniq_hom_app_comp_homEquiv_symm (adj1.ofNatIsoRight nu) adj2 t).trans
    (homEquiv_ofNatIsoRight_symm_apply adj1 nu t)

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V X Y : AlgebraicSpaces B S hS}

/-- The inverse image of sheaves of commutative rings along the morphism of small étale ringed
topoi of a morphism of algebraic spaces: `𝒢 ↦ f_small⁻¹𝒢`. -/
noncomputable abbrev smallEtaleInverseImageRing (f : X ⟶ Y) :
    Sheaf (smallEtaleRingedTopos B S hS Y).J CommRingCat.{u} ⥤
      Sheaf (smallEtaleRingedTopos B S hS X).J CommRingCat.{u} :=
  inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B S hS f).toToposHom

/-- **Stacks 03G8, the geometric composition law in inverse-image form.**  The iterated inverse
image of sheaves of sets along `p` and then `f` is the inverse image along `p ≫ f`.

This is the mate of `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`: that isomorphism
makes the direct image along `p ≫ f` a right adjoint of the iterated inverse image as well, and
two left adjoints of one functor are canonically isomorphic. -/
noncomputable def smallEtaleRingedToposHom_compInverseImageIso (p : U ⟶ X) (f : X ⟶ Y) :
    ((smallEtaleRingedToposHom B S hS f).toToposHom.comp
        (smallEtaleRingedToposHom B S hS p).toToposHom).inverseImage ≅
      (smallEtaleRingedToposHom B S hS (p ≫ f)).toToposHom.inverseImage :=
  (((smallEtaleRingedToposHom B S hS f).toToposHom.comp
        (smallEtaleRingedToposHom B S hS p).toToposHom).adj.ofNatIsoRight
      (smallToposMorphismTypeU_comp B S hS p f)).leftAdjointUniq
    (smallEtaleRingedToposHom B S hS (p ≫ f)).toToposHom.adj

/-- **Stacks 03G8, the composition law for the structure map, on underlying sheaves of sets.**
The geometric comparison followed by the inverse-image structure map of `p ≫ f` is the
inverse-image structure map of the composite of the two morphisms of ringed topoi.

This is `AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp` transposed across the
adjunction `(p ≫ f)⁻¹ ⊣ (p ≫ f)_*`. -/
theorem smallEtaleRingedToposHom_compInverseImageIso_fSharpInverseImageForget
    (p : U ⟶ X) (f : X ⟶ Y) :
    (smallEtaleRingedToposHom_compInverseImageIso B S hS p f).hom.app
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
            (smallEtaleRingedTopos B S hS Y).O) ≫
        (smallEtaleRingedToposHom B S hS (p ≫ f)).fSharpInverseImageForget =
      ((smallEtaleRingedToposHom B S hS f).comp
          (smallEtaleRingedToposHom B S hS p)).fSharpInverseImageForget := by
  have hring : (smallEtaleRingedTopos B S hS Y).forgetRing.map
      ((smallEtaleRingedToposHom_compRingIso B S hS p f).hom.app
        (smallEtaleRingedTopos B S hS U).O) =
      (smallToposMorphismTypeU_comp B S hS p f).hom.app (structureSetSheaf B S hS U) :=
    underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
      (SmallEtale.topology B S hS Y.1) _ (smallToposMorphismTypeU_comp B S hS p f)
  have hcomp := congrArg (smallEtaleRingedTopos B S hS Y).forgetRing.map
    (smallEtaleRingedToposHom_comp_fSharp B S hS p f)
  rw [CategoryTheory.Functor.map_comp, hring] at hcomp
  refine Eq.trans
    (Adjunction.leftAdjointUniq_ofNatIsoRight_hom_app_comp_homEquiv_symm
      ((smallEtaleRingedToposHom B S hS f).toToposHom.comp
        (smallEtaleRingedToposHom B S hS p).toToposHom).adj
      (smallEtaleRingedToposHom B S hS (p ≫ f)).toToposHom.adj
      (smallToposMorphismTypeU_comp B S hS p f) _) (congrArg _ ?_)
  exact natIso_comp_inv_app_eq (smallToposMorphismTypeU_comp B S hS p f) hcomp

/-- **Stacks 03G8, the composition law for inverse images of sheaves of commutative rings.**
Taking the inverse image along `p` of the inverse image along `f` is taking the inverse image
along `p ≫ f`.

The underlying sheaf of sets is unchanged by the first factor and is the geometric comparison
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageIso` on the second. -/
noncomputable def smallEtaleRingedToposHom_compInverseImageRingIso (p : U ⟶ X) (f : X ⟶ Y) :
    smallEtaleInverseImageRing B S hS f ⋙ smallEtaleInverseImageRing B S hS p ≅
      smallEtaleInverseImageRing B S hS (p ≫ f) :=
  inverseImageCommRingComp (smallEtaleRingedToposHom B S hS f).toToposHom
      (smallEtaleRingedToposHom B S hS p).toToposHom ≪≫
    pullbackCommRingSheafFunctorIsoOfNatIso (smallEtaleRingedTopos B S hS U).J
      (Φ := ((smallEtaleRingedToposHom B S hS f).toToposHom.comp
        (smallEtaleRingedToposHom B S hS p).toToposHom).inverseImage)
      (Φ' := (smallEtaleRingedToposHom B S hS (p ≫ f)).toToposHom.inverseImage)
      (smallEtaleRingedToposHom_compInverseImageIso B S hS p f)

/-- **Stacks 03G8, the composition law in inverse-image form.**  The comparison of the iterated
inverse image with the inverse image along `p ≫ f`, followed by the structure map
`(p ≫ f)⁻¹𝒪_Y ⟶ 𝒪_U`, is the inverse image along `p` of the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X`
followed by the structure map `p⁻¹𝒪_X ⟶ 𝒪_U`. -/
theorem smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage
    (p : U ⟶ X) (f : X ⟶ Y) :
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).hom.app
          (smallEtaleRingedTopos B S hS Y).O ≫
        (smallEtaleRingedToposHom B S hS (p ≫ f)).fSharpInverseImage =
      (smallEtaleInverseImageRing B S hS p).map
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage ≫
        (smallEtaleRingedToposHom B S hS p).fSharpInverseImage := by
  have hgeom : (smallEtaleRingedTopos B S hS U).forgetRing.map
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).hom.app
        (smallEtaleRingedTopos B S hS Y).O) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS p f).hom.app
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
          (smallEtaleRingedTopos B S hS Y).O) := by
    refine Eq.trans ((smallEtaleRingedTopos B S hS U).forgetRing.map_comp _ _) ?_
    refine Eq.trans (congrArg₂ (fun a b ↦ a ≫ b)
      (forget_map_inverseImageCommRingComp_hom (smallEtaleRingedToposHom B S hS f).toToposHom
        (smallEtaleRingedToposHom B S hS p).toToposHom (smallEtaleRingedTopos B S hS Y).O)
      (underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
        (smallEtaleRingedTopos B S hS U).J (smallEtaleRingedTopos B S hS Y).O
        (smallEtaleRingedToposHom_compInverseImageIso B S hS p f))) ?_
    exact Category.id_comp _
  have hfp := RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
    (smallEtaleRingedToposHom B S hS (p ≫ f))
  have hp := RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
    (smallEtaleRingedToposHom B S hS p)
  have hf := RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
    (smallEtaleRingedToposHom B S hS f)
  have hsplit := RingedToposHom.fSharpInverseImageForget_comp
    (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS p)
  have hset := smallEtaleRingedToposHom_compInverseImageIso_fSharpInverseImageForget B S hS p f
  refine (smallEtaleRingedTopos B S hS U).forgetRing.map_injective ?_
  refine Eq.trans ((smallEtaleRingedTopos B S hS U).forgetRing.map_comp _ _) ?_
  refine Eq.trans ?_ ((smallEtaleRingedTopos B S hS U).forgetRing.map_comp _ _).symm
  refine Eq.trans (congrArg₂ (fun a b ↦ a ≫ b) hgeom hfp) ?_
  refine Eq.trans hset (Eq.trans hsplit ?_)
  have hpf := congrArg ((smallEtaleRingedToposHom B S hS p).toToposHom.inverseImage.map) hf.symm
  have hforget := underlyingRingSheaf_map_pullbackCommRingSheafMap
    (smallEtaleRingedTopos B S hS U).J
    (Φ := (smallEtaleRingedToposHom B S hS p).toToposHom.inverseImage)
    (smallEtaleRingedToposHom B S hS f).fSharpInverseImage
  have hmap := hpf.trans hforget.symm
  have hcomp := (congrArg (· ≫ (smallEtaleRingedToposHom B S hS p).fSharpInverseImageForget)
    hmap).trans (congrArg (_ ≫ ·) hp.symm)
  exact hcomp

/-- The transport along an equality of morphisms of algebraic spaces is compatible with the
inverse-image form of the structure map, the two morphisms of ringed topoi being equal. -/
theorem eqToHom_comp_fSharpInverseImage {a b : U ⟶ Y} (hab : a = b) :
    eqToHom (congrArg (fun k : U ⟶ Y ↦
        (smallEtaleInverseImageRing B S hS k).obj (smallEtaleRingedTopos B S hS Y).O) hab) ≫
        (smallEtaleRingedToposHom B S hS b).fSharpInverseImage =
      (smallEtaleRingedToposHom B S hS a).fSharpInverseImage := by
  subst hab
  exact Category.id_comp _

/-- **Stacks 03G8 for a commuting square.**  For `p ≫ f = g ≫ q` the two iterated inverse images
of the structure sheaf of `Y` on the small étale site of `U` agree:

`p⁻¹f⁻¹𝒪_Y ≅ g⁻¹q⁻¹𝒪_Y`.

Both sides are compared with the inverse image along the common composite by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso`, and the two
composites are equal, not merely isomorphic. -/
noncomputable def smallEtaleRingedToposHom_squareInverseImageRingIso {p : U ⟶ X} {f : X ⟶ Y}
    {g : U ⟶ V} {q : V ⟶ Y} (h : p ≫ f = g ≫ q) :
    (smallEtaleInverseImageRing B S hS p).obj
        ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O) ≅
      (smallEtaleInverseImageRing B S hS g).obj
        ((smallEtaleInverseImageRing B S hS q).obj (smallEtaleRingedTopos B S hS Y).O) :=
  (smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).app
      (smallEtaleRingedTopos B S hS Y).O ≪≫
    eqToIso (congrArg (fun k : U ⟶ Y ↦
      (smallEtaleInverseImageRing B S hS k).obj (smallEtaleRingedTopos B S hS Y).O) h) ≪≫
    ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS g q).app
      (smallEtaleRingedTopos B S hS Y).O).symm

/-- **Stacks 03G8 for a commuting square, the compatibility with the structure maps.**  The
isomorphism `p⁻¹f⁻¹𝒪_Y ≅ g⁻¹q⁻¹𝒪_Y` carries the composite structure map
`g⁻¹q⁻¹𝒪_Y ⟶ g⁻¹𝒪_V ⟶ 𝒪_U` to the composite structure map `p⁻¹f⁻¹𝒪_Y ⟶ p⁻¹𝒪_X ⟶ 𝒪_U`. -/
theorem smallEtaleRingedToposHom_squareInverseImageRingIso_fSharpInverseImage {p : U ⟶ X}
    {f : X ⟶ Y} {g : U ⟶ V} {q : V ⟶ Y} (h : p ≫ f = g ≫ q) :
    (smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom ≫
        (smallEtaleInverseImageRing B S hS g).map
            (smallEtaleRingedToposHom B S hS q).fSharpInverseImage ≫
          (smallEtaleRingedToposHom B S hS g).fSharpInverseImage =
      (smallEtaleInverseImageRing B S hS p).map
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage ≫
        (smallEtaleRingedToposHom B S hS p).fSharpInverseImage := by
  rw [← smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS g q,
    ← smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS p f,
    ← eqToHom_comp_fSharpInverseImage B S hS h]
  simp only [smallEtaleRingedToposHom_squareInverseImageRingIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc, eqToIso.hom, Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.Space

end
