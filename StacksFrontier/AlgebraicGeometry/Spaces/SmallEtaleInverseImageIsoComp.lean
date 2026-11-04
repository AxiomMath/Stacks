module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleInverseImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp

/-!
# Composition law for the inverse image along an étale morphism

Let `h : D ⟶ A` and `g : A ⟶ C` be étale morphisms of algebraic spaces over a scheme `S`
contained in a big fppf site `B`.  Stacks 03LQ identifies the inverse image of the morphism of
small étale topoi of an étale morphism with restriction of sheaves of sets along small étale
postcomposition; the identification is the comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso` of the two left adjoints of
the direct image.  This file proves that it is compatible with composition at an **arbitrary**
sheaf of sets: the unit of the restriction adjunction of `g`, followed by the direct image along
`g` of the unit of `h`, followed by the comparison of Stacks 03G2, part (3), of the iterated
direct image with the direct image of `h ≫ g`, is the unit of the restriction adjunction of
`h ≫ g`.  At the structure sheaf the statement is
`AlgebraicGeometry.Space.structureSharpSet_comp`, Stacks 03G8 for sheaves of sets, which it
recovers through `AlgebraicGeometry.Space.structureSharpSet_eq_unit`.

The law is proved where it is a statement about the *sites*: the unit of the sheaf adjunction of
an adjunction of sites is restriction of sections along the counit of that adjunction of sites,
so on the spaces-étale topoi the law is the corresponding law for the counits of
`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction`, which in turn is the
compatibility of Stacks 03G2, part (2), with the cartesian projections.  It is then carried to
the small étale topoi, where the restriction adjunction is a conjugate by the comparison
equivalences of Stacks 03G1.

Independently, the file records that the unit of the Stacks 03D3 adjunction between the inverse
image and the direct image of sheaves of modules along a morphism of ringed topoi is the unit of
the adjunction of the underlying morphism of topoi, read on underlying sheaves of sets.

## Main results

* `AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction_counit_comp`: the counits of
  the adjunction of Stacks 03LP between spaces-étale postcomposition and base change compose,
  through the comparison of base changes of Stacks 03G2, part (2).
* `AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction_unit_comp`: the composition law
  for the units on the spaces-étale topoi, at an arbitrary sheaf of sets.
* `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comparison`: at a sheaf read
  from the spaces-étale site, the unit of the small étale restriction adjunction is the
  spaces-étale unit, through the comparison of direct images of Stacks 03G2, part (3).
* `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp`: **the composition law
  on the small étale topoi**, as an equality of the units of the two adjunctions between
  restriction along `h ≫ g` and the direct image along `h ≫ g`.
* `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_app`: that law at a
  single sheaf, in the shape of `AlgebraicGeometry.Space.structureSharpSet_comp`.
* `moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app`, in the namespace
  `Stacks.Sheaves.RingedToposModules`: the unit of the Stacks 03D3 adjunction on sheaves of
  modules is the unit of the adjunction of the underlying morphism of topoi, on underlying
  sheaves of sets.
* `CategoryTheory.Equivalence.conjugate_unit_app_functor`: the unit of a transformation
  conjugated by two equivalences, read at an object in the image of one of them, is the image of
  the original transformation.
* `CategoryTheory.natTrans_from_id_eq_of_essSurj`: two natural transformations out of the
  identity functor agree as soon as they agree on the image of an essentially surjective
  functor.

## Implementation notes

On the spaces-étale side every step is an equality of morphisms of sites or of sections: the
unit of `CategoryTheory.Adjunction.sheafPushforwardContinuous` is restriction of sections along
the counit of the adjunction of sites by `Eq.refl`, and each of the three factors of the law is
`Eq.refl` on sections, so the law reduces to one equation in the spaces-étale site of the
target.

Rewriting with `rw` is unavailable in several places: the composition of `AlgebraicSpaces` and
the compositions of the sheaf categories occur with object arguments that are definitionally but
not syntactically equal, and `rw` matches those arguments at `instances` transparency only.  Each
such step is therefore performed as a `congrArg` or an `Eq.trans` in term mode, which unifies at
default transparency; the auxiliary lemmas `CategoryTheory.comp_congr_of_eq₅`,
`CategoryTheory.comp_eq_of_factorizations₅` and
`CategoryTheory.Equivalence.conjugate_unit_app_functor` isolate the shapes whose rewriting would
otherwise have to happen inside a large concrete term.  No `set_option` appears in this file.

## Universes

Everything on the algebraic spaces side is at the universe `u` of the structure rings, which is
the universe at which `AlgebraicGeometry.Space.smallEtaleDirectImage`, and hence the small étale
restriction adjunction, exists.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-! ### Generalities -/

/-- Congruence in the fourth of five factors of a composite, together with the reassociation
that brings the last factor inside. -/
theorem comp_congr_of_eq₅ {CC : Type u₁} [Category.{v₁} CC] {O₀ O₁ O₂ O₃ O₄ O₅ : CC}
    (a : O₀ ⟶ O₁) (b : O₁ ⟶ O₂) (c : O₂ ⟶ O₃) (e : O₄ ⟶ O₅) {d d' : O₃ ⟶ O₄}
    (hd : d = d') : (a ≫ b ≫ c ≫ d) ≫ e = a ≫ b ≫ c ≫ d' ≫ e := by
  rw [hd, Category.assoc, Category.assoc, Category.assoc]

/-- A five-factor substitution chain: a composite of three factors followed by one more is
rewritten by a factorization of its last pair, by functoriality in the middle, by a
factorization of the resulting pair, and by a factorization of its leading pair.  Isolated so
that it carries no types of its own. -/
theorem comp_eq_of_factorizations₅ {XX : Type u₁} [Category.{v₁} XX] {YY : Type u₂}
    [Category.{v₂} YY] (Rg : XX ⥤ YY) {A₁ A₂ A₃ : XX} {O₀ O₃ O₄ O₅ O₆ : YY}
    {ug : O₀ ⟶ Rg.obj A₁} {uh : A₁ ⟶ A₂} {ch : A₂ ⟶ A₃} {Fa : A₁ ⟶ A₃}
    {k : Rg.obj A₂ ⟶ O₃} {e : O₃ ⟶ O₄} {cg : Rg.obj A₃ ⟶ O₅} {m₃ : O₅ ⟶ O₄}
    {cg' : Rg.obj A₁ ⟶ O₆} {m₂ : O₆ ⟶ O₅} {m₁ : O₀ ⟶ O₆} {U : O₀ ⟶ O₃} {Z : O₀ ⟶ O₄}
    (hA : U ≫ e = Z) (hcomp : Rg.map ch ≫ cg ≫ m₃ = k ≫ e) (hB : uh ≫ ch = Fa)
    (hnat : Rg.map Fa ≫ cg = cg' ≫ m₂) (hC : ug ≫ cg' = m₁) (hmul : m₁ ≫ m₂ ≫ m₃ = Z) :
    (ug ≫ Rg.map uh ≫ k) ≫ e = U ≫ e := by
  rw [hA, Category.assoc, Category.assoc, ← hcomp, ← Category.assoc (Rg.map uh),
    ← Rg.map_comp, hB, ← Category.assoc (Rg.map Fa), hnat, Category.assoc,
    ← Category.assoc ug, hC, hmul]

/-- Two natural transformations out of the identity functor agree as soon as they agree on the
image of an essentially surjective functor: every object is isomorphic to one in that image, and
naturality transports the component along such an isomorphism. -/
theorem natTrans_from_id_eq_of_essSurj {CC : Type u₁} [Category.{v₁} CC] {DD : Type u₂}
    [Category.{v₂} DD] {T : CC ⥤ CC} (E : DD ⥤ CC) [E.EssSurj] {tau tau' : 𝟭 CC ⟶ T}
    (hc : ∀ X : DD, tau.app (E.obj X) = tau'.app (E.obj X)) : tau = tau' := by
  ext P
  have h1 := tau.naturality (E.objObjPreimageIso P).hom
  have h2 := tau'.naturality (E.objObjPreimageIso P).hom
  rw [hc (E.objPreimage P)] at h1
  exact (cancel_epi ((E.objObjPreimageIso P).hom)).mp (h1.trans h2.symm)

namespace Equivalence

variable {S₁ : Type u₁} [Category.{v₁} S₁] {S₂ : Type u₂} [Category.{v₂} S₂]
  {T₁ : Type u₃} [Category.{v₃} T₁] {T₂ : Type u₄} [Category.{v₄} T₂]

/-- **A conjugated unit at an object in the image of the equivalence.**  For equivalences
`e₁ : S₁ ≌ T₁` and `e₂ : S₂ ≌ T₂` and a transformation `η : 𝟭 S₂ ⟶ L ⋙ R`, the four-factor
composite that the conjugate of `η` by `e₁` and `e₂` becomes at `e₂.functor.obj H`, read through
the comparison `e₁.unitIso.inv`, is `e₂.functor` applied to `η.app H`.

The two occurrences of `e₁.unitIso` cancel by its naturality, and the two occurrences of
`e₂.unitIso` cancel against each other after naturality of `η`. -/
theorem conjugate_unit_app_functor (e₁ : S₁ ≌ T₁) (e₂ : S₂ ≌ T₂)
    (L : S₂ ⥤ S₁) (R : S₁ ⥤ S₂) (η : 𝟭 S₂ ⟶ L ⋙ R) (H : S₂) :
    e₂.counitIso.inv.app (e₂.functor.obj H) ≫
        e₂.functor.map (η.app (e₂.inverse.obj (e₂.functor.obj H))) ≫
        e₂.functor.map (R.map (e₁.unitIso.hom.app
          (L.obj (e₂.inverse.obj (e₂.functor.obj H))))) ≫
        e₂.functor.map (R.map (e₁.inverse.map (e₁.functor.map
          (L.map (e₂.unitIso.inv.app H))))) ≫
        e₂.functor.map (R.map (e₁.unitIso.inv.app (L.obj H))) =
      e₂.functor.map (η.app H) := by
  have hnat : η.app (e₂.inverse.obj (e₂.functor.obj H)) ≫
        R.map (L.map (e₂.unitIso.inv.app H)) =
      e₂.unitIso.inv.app H ≫ η.app H := (η.naturality (e₂.unitIso.inv.app H)).symm
  simp [← Functor.map_comp, Equivalence.counitInv_app_functor, hnat]

end Equivalence

namespace Adjunction

/-- The unit of a composite adjunction transported along a natural isomorphism of its right
adjoint, at a single object. -/
theorem comp_ofNatIsoRight_unit_app {CC : Type u₁} [Category.{v₁} CC] {DD : Type u₂}
    [Category.{v₂} DD] {EE : Type u₃} [Category.{v₃} EE] {F : CC ⥤ DD} {G : DD ⥤ CC}
    {F' : DD ⥤ EE} {G' : EE ⥤ DD} {K : EE ⥤ CC} (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G')
    (iso : G' ⋙ G ≅ K) (X : CC) :
    ((adj₁.comp adj₂).ofNatIsoRight iso).unit.app X =
      adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X)) ≫ iso.hom.app (F'.obj (F.obj X)) := by
  simp [Adjunction.comp_unit_app]

end Adjunction

end CategoryTheory

namespace Stacks.Sheaves.RingedToposModules

universe w w' v uu v' u'

variable {CC : Type uu} [Category.{v} CC] {DD : Type u'} [Category.{v'} DD]
  {J : GrothendieckTopology CC} {K : GrothendieckTopology DD}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'})

/-- **The unit of the Stacks 03D3 adjunction on sheaves of modules is the unit on sheaves of
sets**, on underlying sheaves.  The hom-set bijection of Stacks 03D3 sends a morphism to the
transpose of its underlying morphism of sheaves of sets, so its value at the identity — which is
what the unit of an adjunction presented by a hom-set bijection is — is the transpose of the
identity, namely the unit of `f⁻¹ ⊣ f_*`. -/
theorem moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app
    (G : SheafOfModules.{w'} O) :
    (Sheaf.moduleSheafFunctor O).map ((inverseImageAdjDirectImageModules f O).unit.app G) =
      f.adj.unit.app (Sheaf.moduleSheaf O G) := by
  change (Sheaf.moduleSheafFunctor O).map
      (toposModulesHomEquiv f O G ((inverseImageModules f O).obj G) (𝟙 _)) = _
  rw [moduleSheafFunctor_map_toposModulesHomEquiv]
  change (f.adj.homEquiv (Sheaf.moduleSheaf O G)
    (Sheaf.moduleSheaf (inverseImageRingSheaf f O)
      ((inverseImageModules f O).obj G))) (𝟙 _) = _
  exact f.adj.homEquiv_id _

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)

/-! ### The composition law on the spaces-étale topoi -/

/-- **The counits of the adjunction of Stacks 03LP compose.**  For étale morphisms `h : D ⟶ A`
and `g : A ⟶ C` and an object `W` of the spaces-étale site of `C`, the counit of
`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction` at `W` for `h ≫ g` is the
counit for `h` at `A ×_C W`, postcomposed along `g` and preceded by the comparison of base
changes of Stacks 03G2, part (2).

Both sides have the same image under the faithful
`AlgebraicGeometry.Space.SpacesEtale.toSpaces`, where the counits are the cartesian projections
(`AlgebraicGeometry.Space.toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit`) and the
assertion is their compatibility with the comparison of base changes
(`AlgebraicGeometry.Space.spacesBaseChange_comp_projection`). -/
theorem spacesEtalePostcompBaseChangeAdjunction_counit_comp (W : SpacesEtale B S hS C) :
    (spacesEtalePostcomp B S hS (h ≫ g) hhg).map
          ((spacesBaseChange_comp B S hS h g).inv.app W) ≫
        (spacesEtalePostcomp B S hS g hg).map
          ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
            ((spacesBaseChange B S hS g).functor.obj W)) ≫
        (spacesEtalePostcompBaseChangeAdjunction B S hS g hg).counit.app W =
      (spacesEtalePostcompBaseChangeAdjunction B S hS (h ≫ g) hhg).counit.app W := by
  have hgamma : (SpacesEtale.toSpaces B S hS C).map
        ((spacesEtalePostcomp B S hS (h ≫ g) hhg).map
          ((spacesBaseChange_comp B S hS h g).inv.app W)) =
      (SpacesEtale.toSpaces B S hS D).map
        ((spacesBaseChange_comp B S hS h g).inv.app W) := rfl
  have halpha : (SpacesEtale.toSpaces B S hS C).map
        ((spacesEtalePostcomp B S hS g hg).map
          ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
            ((spacesBaseChange B S hS g).functor.obj W))) =
      (spacesBaseChange B S hS h).projection.app
        ((spacesBaseChange B S hS g).functor.obj W) :=
    toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit B S hS h hh
      ((spacesBaseChange B S hS g).functor.obj W)
  have hcancel : (SpacesEtale.toSpaces B S hS D).map
        ((spacesBaseChange_comp B S hS h g).inv.app W) ≫
      Over.Hom.left ((spacesBaseChange_comp B S hS h g).hom.app W).hom = 𝟙 _ := by
    change (SpacesEtale.toSpaces B S hS D).map
          ((spacesBaseChange_comp B S hS h g).inv.app W) ≫
        (SpacesEtale.toSpaces B S hS D).map
          ((spacesBaseChange_comp B S hS h g).hom.app W) = 𝟙 _
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  apply (SpacesEtale.toSpaces B S hS C).map_injective
  refine Eq.trans ?_ (toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit
    B S hS (h ≫ g) hhg W).symm
  refine Eq.trans (CategoryTheory.Functor.map_comp _ _ _) ?_
  refine Eq.trans (congrArg₂ (fun p q ↦ p ≫ q) hgamma
    ((CategoryTheory.Functor.map_comp _ _ _).trans
      (congrArg₂ (fun p q ↦ p ≫ q) halpha
        (toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit B S hS g hg W)))) ?_
  refine Eq.trans (congrArg (fun m ↦ (SpacesEtale.toSpaces B S hS D).map
      ((spacesBaseChange_comp B S hS h g).inv.app W) ≫ m)
    (spacesBaseChange_comp_projection B S hS h g W).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m ↦ m ≫ (spacesBaseChange B S hS (h ≫ g)).projection.app W)
    hcancel) ?_
  exact Category.id_comp _

/-- **The composition law for the inverse image of Stacks 03LQ on the spaces-étale topoi, at an
arbitrary sheaf of sets.**  For étale `h : D ⟶ A` and `g : A ⟶ C` and a sheaf of sets `P` on the
spaces-étale site of `C`, the unit of
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction` of `g` at `P`, followed by the
direct image along `g` of the unit of `h` at `P|_A`, followed by the comparison of the iterated
direct image with the direct image of `h ≫ g`, is the unit of `h ≫ g` at `P`.

On sections over an object `W` of the spaces-étale site of `C` each of the three factors is
restriction of sections along a morphism of that site, so the law is
`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction_counit_comp`. -/
theorem spacesEtalePostcompSheafAdjunction_unit_comp
    (P : Sheaf (SpacesEtale.topology B S hS C) (Type u)) :
    (spacesEtalePostcompSheafAdjunction B S hS (Type u) g hg).unit.app P ≫
        (spacesSetBaseChange B S hS g).map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app
            ((spacesEtaleSetRestriction B S hS g hg).obj P)) ≫
        (spacesBaseChange_pushforward_compTypeU B S hS h g).hom.app
          ((spacesEtaleSetRestriction B S hS (h ≫ g) hhg).obj P) =
      (spacesEtalePostcompSheafAdjunction B S hS (Type u) (h ≫ g) hhg).unit.app P := by
  refine Sheaf.hom_ext_sections (fun W x ↦ ?_)
  change P.obj.map ((spacesEtalePostcomp B S hS (h ≫ g) hhg).map
          ((spacesBaseChange_comp B S hS h g).inv.app W.unop)).op
        (P.obj.map ((spacesEtalePostcomp B S hS g hg).map
            ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
              ((spacesBaseChange B S hS g).functor.obj W.unop))).op
          (P.obj.map ((spacesEtalePostcompBaseChangeAdjunction B S hS g hg).counit.app
            W.unop).op x)) =
      P.obj.map ((spacesEtalePostcompBaseChangeAdjunction B S hS (h ≫ g) hhg).counit.app
        W.unop).op x
  refine Eq.trans (congrArg (fun y ↦ P.obj.map ((spacesEtalePostcomp B S hS (h ≫ g) hhg).map
        ((spacesBaseChange_comp B S hS h g).inv.app W.unop)).op y)
    (Functor.map_comp_apply P.obj _ _ x).symm) ?_
  refine Eq.trans (Functor.map_comp_apply P.obj _ _ x).symm ?_
  exact congrArg (fun m ↦ P.obj.map (Quiver.Hom.op m) x)
    (spacesEtalePostcompBaseChangeAdjunction_counit_comp B S hS h g hh hg hhg W.unop)

/-! ### The unit on the small étale topoi against the spaces-étale unit -/

/-- **The unit of small étale restriction is the spaces-étale unit.**  For an étale `h : D ⟶ A`
and a sheaf of sets `H` on the spaces-étale site of `A`, the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at the sheaf that `H` becomes on
the small étale site, followed by the comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comparison` of direct images of Stacks 03G2,
part (3), is the spaces-étale unit read on the small étale site.

The small étale restriction adjunction is the spaces-étale one conjugated by the comparison
equivalences of Stacks 03G1, so the assertion is
`CategoryTheory.Equivalence.conjugate_unit_app_functor` once the four factors of the unit and
the comparison are written out; the only non-definitional step is
`CategoryTheory.Equivalence.counit_app_functor` for the comparison equivalence at `A`. -/
theorem smallEtaleSetRestrictionAdjunction_unit_comparison
    (H : Sheaf (SpacesEtale.topology B S hS A) (Type u)) :
    (smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
          ((smallEtaleComparisonRestriction B S hS A).obj H) ≫
        (smallToposMorphismTypeU_comparison B S hS h).hom.app
          ((spacesEtaleSetRestriction B S hS h hh).obj H) =
      (smallEtaleComparisonRestriction B S hS A).map
        ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app H) := by
  have hunit : (smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
        ((smallEtaleComparisonRestriction B S hS A).obj H) =
      (smallEtaleComparisonRestriction B S hS A).asEquivalence.counitIso.inv.app
          ((smallEtaleComparisonRestriction B S hS A).obj H) ≫
        (smallEtaleComparisonRestriction B S hS A).map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app
            ((smallEtaleComparisonRestriction B S hS A).asEquivalence.inverse.obj
              ((smallEtaleComparisonRestriction B S hS A).obj H))) ≫
        (smallEtaleComparisonRestriction B S hS A).map
          ((spacesSetBaseChange B S hS h).map
            ((smallEtaleComparisonRestriction B S hS D).asEquivalence.unitIso.hom.app
              ((spacesEtaleSetRestriction B S hS h hh).obj
                ((smallEtaleComparisonRestriction B S hS A).asEquivalence.inverse.obj
                  ((smallEtaleComparisonRestriction B S hS A).obj H))))) ≫
        (smallEtaleDirectImage B S hS h).map
          ((smallEtaleSetRestriction B S hS h hh).map
            ((smallEtaleComparisonRestriction B S hS A).asEquivalence.counitIso.hom.app
              ((smallEtaleComparisonRestriction B S hS A).obj H))) := rfl
  have hcmp : (smallToposMorphismTypeU_comparison B S hS h).hom.app
        ((spacesEtaleSetRestriction B S hS h hh).obj H) =
      (smallEtaleComparisonRestriction B S hS A).map
        ((spacesSetBaseChange B S hS h).map
          ((smallEtaleComparisonRestriction B S hS D).asEquivalence.unitIso.inv.app
            ((spacesEtaleSetRestriction B S hS h hh).obj H))) :=
    Category.comp_id _
  have he1 : (smallEtaleComparisonRestriction B S hS A).asEquivalence.counitIso.hom.app
        ((smallEtaleComparisonRestriction B S hS A).obj H) =
      (smallEtaleComparisonRestriction B S hS A).map
        ((smallEtaleComparisonRestriction B S hS A).asEquivalence.unitIso.inv.app H) :=
    Equivalence.counit_app_functor (smallEtaleComparisonRestriction B S hS A).asEquivalence H
  have he2 : (smallEtaleSetRestriction B S hS h hh).map
        ((smallEtaleComparisonRestriction B S hS A).map
          ((smallEtaleComparisonRestriction B S hS A).asEquivalence.unitIso.inv.app H)) =
      (smallEtaleComparisonRestriction B S hS D).map
        ((spacesEtaleSetRestriction B S hS h hh).map
          ((smallEtaleComparisonRestriction B S hS A).asEquivalence.unitIso.inv.app H)) := rfl
  have he3 : (smallEtaleDirectImage B S hS h).map
        ((smallEtaleComparisonRestriction B S hS D).map
          ((spacesEtaleSetRestriction B S hS h hh).map
            ((smallEtaleComparisonRestriction B S hS A).asEquivalence.unitIso.inv.app H))) =
      (smallEtaleComparisonRestriction B S hS A).map
        ((spacesSetBaseChange B S hS h).map
          ((smallEtaleComparisonRestriction B S hS D).asEquivalence.inverse.map
            ((smallEtaleComparisonRestriction B S hS D).map
              ((spacesEtaleSetRestriction B S hS h hh).map
                ((smallEtaleComparisonRestriction B S hS A).asEquivalence.unitIso.inv.app
                  H))))) := rfl
  have hfac4 := ((congrArg (fun m ↦ (smallEtaleDirectImage B S hS h).map
      ((smallEtaleSetRestriction B S hS h hh).map m)) he1).trans
    (congrArg (fun m ↦ (smallEtaleDirectImage B S hS h).map m) he2)).trans he3
  refine Eq.trans (congrArg₂ (fun p q ↦ p ≫ q) hunit hcmp) ?_
  refine Eq.trans ?_ (CategoryTheory.Equivalence.conjugate_unit_app_functor
    (smallEtaleComparisonRestriction B S hS D).asEquivalence
    (smallEtaleComparisonRestriction B S hS A).asEquivalence
    (spacesEtaleSetRestriction B S hS h hh) (spacesSetBaseChange B S hS h)
    (spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit H)
  exact CategoryTheory.comp_congr_of_eq₅ _ _ _ _ hfac4

/-! ### The composition law on the small étale topoi -/

/-- The composition law for the units of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at a sheaf of sets read from the
spaces-étale site of `C`.

Composing with the comparison of direct images of Stacks 03G2, part (3), for `h ≫ g` — an
isomorphism — turns both sides into images under the comparison equivalence of Stacks 03G1 of
the spaces-étale statement
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction_unit_comp`.  The three steps that
effect this are `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_comparison`,
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comparison`, and naturality of
the comparison of direct images of `g`. -/
theorem smallEtaleSetRestrictionAdjunction_unit_comp_comparison
    (H : Sheaf (SpacesEtale.topology B S hS C) (Type u)) :
    (smallEtaleSetRestrictionAdjunction B S hS g hg).unit.app
          ((smallEtaleComparisonRestriction B S hS C).obj H) ≫
        (smallEtaleDirectImage B S hS g).map
          ((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
            ((smallEtaleSetRestriction B S hS g hg).obj
              ((smallEtaleComparisonRestriction B S hS C).obj H))) ≫
        (smallToposMorphismTypeU_comp B S hS h g).hom.app
          ((smallEtaleSetRestriction B S hS (h ≫ g) hhg).obj
            ((smallEtaleComparisonRestriction B S hS C).obj H)) =
      (smallEtaleSetRestrictionAdjunction B S hS (h ≫ g) hhg).unit.app
        ((smallEtaleComparisonRestriction B S hS C).obj H) := by
  have hnat : (smallEtaleDirectImage B S hS g).map
        ((smallEtaleComparisonRestriction B S hS A).map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app
            ((spacesEtaleSetRestriction B S hS g hg).obj H))) ≫
        (smallToposMorphismTypeU_comparison B S hS g).hom.app
          ((spacesSetBaseChange B S hS h).obj
            ((spacesEtaleSetRestriction B S hS (h ≫ g) hhg).obj H)) =
      (smallToposMorphismTypeU_comparison B S hS g).hom.app
          ((spacesEtaleSetRestriction B S hS g hg).obj H) ≫
        (smallEtaleComparisonRestriction B S hS C).map
          ((spacesSetBaseChange B S hS g).map
            ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app
              ((spacesEtaleSetRestriction B S hS g hg).obj H))) :=
    (smallToposMorphismTypeU_comparison B S hS g).hom.naturality
      ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app
        ((spacesEtaleSetRestriction B S hS g hg).obj H))
  have hmap : (smallEtaleComparisonRestriction B S hS C).map
        ((spacesEtalePostcompSheafAdjunction B S hS (Type u) g hg).unit.app H ≫
          (spacesSetBaseChange B S hS g).map
            ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app
              ((spacesEtaleSetRestriction B S hS g hg).obj H)) ≫
          (spacesBaseChange_pushforward_compTypeU B S hS h g).hom.app
            ((spacesEtaleSetRestriction B S hS (h ≫ g) hhg).obj H)) =
      (smallEtaleComparisonRestriction B S hS C).map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) g hg).unit.app H) ≫
        (smallEtaleComparisonRestriction B S hS C).map
          ((spacesSetBaseChange B S hS g).map
            ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app
              ((spacesEtaleSetRestriction B S hS g hg).obj H))) ≫
        (smallEtaleComparisonRestriction B S hS C).map
          ((spacesBaseChange_pushforward_compTypeU B S hS h g).hom.app
            ((spacesEtaleSetRestriction B S hS (h ≫ g) hhg).obj H)) :=
    (CategoryTheory.Functor.map_comp _ _ _).trans
      (congrArg (fun m ↦ (smallEtaleComparisonRestriction B S hS C).map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) g hg).unit.app H) ≫ m)
        (CategoryTheory.Functor.map_comp _ _ _))
  have hmul := hmap.symm.trans (congrArg (smallEtaleComparisonRestriction B S hS C).map
    (spacesEtalePostcompSheafAdjunction_unit_comp B S hS h g hh hg hhg H))
  refine (Iso.cancel_iso_hom_right _ _
    ((smallToposMorphismTypeU_comparison B S hS (h ≫ g)).app
      ((spacesEtaleSetRestriction B S hS (h ≫ g) hhg).obj H))).mp ?_
  exact CategoryTheory.comp_eq_of_factorizations₅ (smallEtaleDirectImage B S hS g)
    (smallEtaleSetRestrictionAdjunction_unit_comparison B S hS (h ≫ g) hhg H)
    (smallToposMorphismTypeU_comp_comparison B S hS h g
      ((spacesEtaleSetRestriction B S hS (h ≫ g) hhg).obj H))
    (smallEtaleSetRestrictionAdjunction_unit_comparison B S hS h hh
      ((spacesEtaleSetRestriction B S hS g hg).obj H))
    hnat
    (smallEtaleSetRestrictionAdjunction_unit_comparison B S hS g hg H)
    hmul

/-- **The composition law for the inverse image of Stacks 03LQ at an arbitrary sheaf of sets.**
For étale morphisms `h : D ⟶ A` and `g : A ⟶ C` of algebraic spaces, the adjunction between
small étale restriction along `h ≫ g` and the direct image along `h ≫ g` assembled from the two
factors through the comparison of direct images of Stacks 03G2, part (3), has the same unit as
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` of `h ≫ g`.

Both units are natural transformations out of the identity functor of the small étale topos of
`C`, and the comparison equivalence of Stacks 03G1 is essentially surjective, so
`CategoryTheory.natTrans_from_id_eq_of_essSurj` reduces the assertion to
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_comparison`. -/
theorem smallEtaleSetRestrictionAdjunction_unit_comp :
    (((smallEtaleSetRestrictionAdjunction B S hS g hg).comp
          (smallEtaleSetRestrictionAdjunction B S hS h hh)).ofNatIsoRight
        (smallToposMorphismTypeU_comp B S hS h g)).unit =
      (smallEtaleSetRestrictionAdjunction B S hS (h ≫ g) hhg).unit :=
  CategoryTheory.natTrans_from_id_eq_of_essSurj (smallEtaleComparisonRestriction B S hS C)
    (fun H ↦ (CategoryTheory.Adjunction.comp_ofNatIsoRight_unit_app _ _ _ _).trans
      (smallEtaleSetRestrictionAdjunction_unit_comp_comparison B S hS h g hh hg hhg H))

/-- **The composition law for the inverse image of Stacks 03LQ at a single sheaf of sets.**  For
étale morphisms `h : D ⟶ A` and `g : A ⟶ C` and a sheaf of sets `P` on the small étale site of
`C`, the unit of `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` of `g` at `P`,
followed by the direct image along `g` of the unit of `h` at `P|_A`, followed by the comparison
of Stacks 03G2, part (3), of the iterated direct image with the direct image of `h ≫ g`, is the
unit of `h ≫ g` at `P`.

This is `AlgebraicGeometry.Space.structureSharpSet_comp` — Stacks 03G8, compatibility with
composition, at the level of sheaves of sets — at an arbitrary sheaf in place of the structure
sheaf; the structure-sheaf case follows from it through
`AlgebraicGeometry.Space.structureSharpSet_eq_unit`. -/
theorem smallEtaleSetRestrictionAdjunction_unit_comp_app
    (P : Sheaf (SmallEtale.topology B S hS C.1) (Type u)) :
    (smallEtaleSetRestrictionAdjunction B S hS g hg).unit.app P ≫
        (smallEtaleDirectImage B S hS g).map
          ((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
            ((smallEtaleSetRestriction B S hS g hg).obj P)) ≫
        (smallToposMorphismTypeU_comp B S hS h g).hom.app
          ((smallEtaleSetRestriction B S hS (h ≫ g) hhg).obj P) =
      (smallEtaleSetRestrictionAdjunction B S hS (h ≫ g) hhg).unit.app P :=
  (CategoryTheory.Adjunction.comp_ofNatIsoRight_unit_app _ _ _ P).symm.trans
    (CategoryTheory.NatTrans.congr_app
      (smallEtaleSetRestrictionAdjunction_unit_comp B S hS h g hh hg hhg) P)

end AlgebraicGeometry.Space

end
