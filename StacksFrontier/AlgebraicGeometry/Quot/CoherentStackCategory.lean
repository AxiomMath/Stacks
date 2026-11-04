module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso

/-!
# The category structure on the coherent sheaves with proper support (Stacks 08KB)

Stacks 08KB names `Coh_{X/Y}` a category by designation: it writes down the objects
(`AlgebraicGeometry.Space.CoherentObject`), the morphisms
(`AlgebraicGeometry.Space.CoherentHom`), the identities
(`AlgebraicGeometry.Space.CoherentHom.id`) and the composition
(`AlgebraicGeometry.Space.CoherentHom.comp`), and does not verify the category laws.  The
specification of that category — a `CategoryTheory.Category` on the objects whose hom-sets *are*
the morphisms, whose identity and composition are the two above, together with the projection to
the test schemes — is `AlgebraicGeometry.Space.CoherentCategoryData`.

This file verifies the three laws and builds a value of that specification.  Composition of
morphisms of `Coh_{X/Y}` is associative and unital exactly because the inverse images of
`𝒪`-modules of Stacks 03LU are pseudofunctorial, and that pseudofunctoriality is
`AlgebraicGeometry.Space.modulePushforwardCoherence`, which is constructed with no hypothesis.
So `AlgebraicGeometry.Space.CoherentSituation.categoryData` needs nothing beyond the
standing datum.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.coherentCategory`: the category structure on
  `AlgebraicGeometry.Space.CoherentObject` whose hom-sets are
  `AlgebraicGeometry.Space.CoherentHom`.
* `AlgebraicGeometry.Space.CoherentSituation.coherentProjection`: the projection
  `(T, g, F) ↦ (T, g)` of `Coh_{X/Y}` to the test schemes over `Y`.
* `AlgebraicGeometry.Space.CoherentSituation.categoryData`: **a value of
  `AlgebraicGeometry.Space.CoherentCategoryData` for the canonical pseudofunctoriality datum**,
  so `Coh_{X/Y}` is a category.

## Main results

* `AlgebraicGeometry.Space.CoherentHom.id_comp`,
  `AlgebraicGeometry.Space.CoherentHom.comp_id` and
  `AlgebraicGeometry.Space.CoherentHom.assoc`: **the three category laws of `Coh_{X/Y}`**, from
  the coherences `AlgebraicGeometry.Space.idComparison_comp_fac`,
  `AlgebraicGeometry.Space.comp_idComparison_fac` and
  `AlgebraicGeometry.Space.compComparison_assoc` of the comparisons of inverse images along the
  morphisms of base changes.
* `AlgebraicGeometry.Space.CoherentSituation.relativeMapComparison_hom_app`: the component of
  the identification induced by an equality of base maps is a transport.
* `CategoryTheory.heq_of_eq_eqToHom_comp`: a morphism that is a transport followed by a second
  morphism is heterogeneously equal to that second morphism.

## Implementation notes

**The two base maps of each law are equal but not syntactically equal, and the laws are proved
with `AlgebraicGeometry.Space.coherentHom_eq_of_heq` rather than
`AlgebraicGeometry.Space.CoherentHom.ext` for that reason.**  `ext` compares the comparisons of
modules after a transport along the equality of base maps, and supplying the equality
`𝟙 T ≫ h = h` — whose two sides are definitionally the base maps of the two morphisms being
compared, but spelled differently — makes the resulting goal type-correct only at default
transparency, so no rewrite fires in it.  This is the obstruction recorded in the docstring of
`AlgebraicGeometry.Space.coherentHom_eq_of_heq`, and the heterogeneous comparison avoids it.

Each law is proved by instantiating the abstract law
(`CategoryTheory.Functor.fibreComp_id_left`, `fibreComp_id_right`, `fibreComp_assoc`) at the
spelling the corresponding coherence of `StacksFrontier/AlgebraicGeometry/Quot/CoherentStack.lean`
already has, and letting the one remaining definitional step be the unfolding of
`AlgebraicGeometry.Space.CoherentHom.comp`.  The target morphism of
`CategoryTheory.heq_of_eq_eqToHom_comp` is passed explicitly: left to be inferred from the goal,
the elaborator assigns the functors of `CategoryTheory.Functor.fibreComp` from the goal first and
then has to reconcile them with the ones of the coherence, which it does by reducing
`AlgebraicGeometry.Space.modulePullback` — the nonterminating reduction recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean`.  With the
target given, every functor is concrete before the comparison starts.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

/-- A morphism which is a transport along an equality of objects followed by a second morphism is
heterogeneously equal to that second morphism.

This is the form in which a law whose two sides have definitionally equal but differently spelled
types is discharged: the transport is recognised as an identity once the equality of objects is
substituted away. -/
theorem heq_of_eq_eqToHom_comp {C : Type*} [Category* C] {X Y Z : C} (e : X = Y)
    (f : Y ⟶ Z) {g : X ⟶ Z} (h : g = eqToHom e ≫ f) : HEq g f := by
  subst e
  simp only [eqToHom_refl, Category.id_comp] at h
  exact heq_of_eq h

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

/-- The component at a module of the identification of the inverse images along the morphisms of
base changes induced by two equal morphisms of test schemes: it is the transport along the
induced equality of modules. -/
theorem relativeMapComparison_hom_app (D : CoherentSituation B S hS)
    {T T' : SchemesOver D.Y} {h h' : T ⟶ T'} (e : h = h')
    (M : Modules.{u, u} B S hS (D.space T').1 (D.space T').2) :
    (D.relativeMapComparison e).hom.app M =
      eqToHom (congrArg
        (fun k : T ⟶ T' => (modulePullback B S hS (D.relativeMap k)).obj M) e) := by
  subst e
  rfl

end CoherentSituation

namespace CoherentHom

/-- **Stacks 08KB, the unit law at the source.**  Composing a morphism of `Coh_{X/Y}` after the
identity of its source is that morphism.

It is the unit law `AlgebraicGeometry.Space.idComparison_comp_fac` of the comparisons of inverse
images along the morphisms of base changes. -/
theorem id_comp (hc : ModulePushforwardCoherence B S hS) {D : CoherentSituation B S hS}
    {A A' : CoherentObject D} (m : CoherentHom A A') :
    (CoherentHom.id hc A).comp m = m := by
  have hb : ((CoherentHom.id hc A).comp m).base = m.base := Category.id_comp m.base
  have key := Functor.fibreComp_id_left (D.idComparison hc A.T)
    (D.compComparison (𝟙 A.T) m.base)
    (D.relativeMapComparison (Category.id_comp m.base))
    (idComparison_comp_fac hc D m.base) m.fibre
  rw [D.relativeMapComparison_hom_app] at key
  refine coherentHom_eq_of_heq hb ?_
  simp only [CoherentHom.comp_fibre, CoherentHom.id_fibre]
  exact heq_of_eq_eqToHom_comp _ m.fibre key

/-- **Stacks 08KB, the unit law at the target.**  Composing a morphism of `Coh_{X/Y}` before the
identity of its target is that morphism.

It is the unit law `AlgebraicGeometry.Space.comp_idComparison_fac` of the comparisons of inverse
images along the morphisms of base changes. -/
theorem comp_id (hc : ModulePushforwardCoherence B S hS) {D : CoherentSituation B S hS}
    {A A' : CoherentObject D} (m : CoherentHom A A') :
    m.comp (CoherentHom.id hc A') = m := by
  have hb : (m.comp (CoherentHom.id hc A')).base = m.base := Category.comp_id m.base
  have key := Functor.fibreComp_id_right (D.idComparison hc A'.T)
    (D.compComparison m.base (𝟙 A'.T))
    (D.relativeMapComparison (Category.comp_id m.base))
    (comp_idComparison_fac hc D m.base) m.fibre
  rw [D.relativeMapComparison_hom_app] at key
  refine coherentHom_eq_of_heq hb ?_
  simp only [CoherentHom.comp_fibre, CoherentHom.id_fibre]
  exact heq_of_eq_eqToHom_comp _ m.fibre key

/-- **Stacks 08KB, associativity.**  Composition of morphisms of `Coh_{X/Y}` is associative.

It is the associativity coherence `AlgebraicGeometry.Space.compComparison_assoc` of the
comparisons of inverse images along the morphisms of base changes. -/
theorem assoc (hc : ModulePushforwardCoherence B S hS) {D : CoherentSituation B S hS}
    {A A' A'' A''' : CoherentObject D} (m : CoherentHom A A') (n : CoherentHom A' A'')
    (p : CoherentHom A'' A''') :
    (m.comp n).comp p = m.comp (n.comp p) := by
  have hb : ((m.comp n).comp p).base = (m.comp (n.comp p)).base :=
    Category.assoc m.base n.base p.base
  have key := Functor.fibreComp_assoc (D.compComparison m.base n.base)
    (D.compComparison (m.base ≫ n.base) p.base) (D.compComparison n.base p.base)
    (D.compComparison m.base (n.base ≫ p.base))
    (D.relativeMapComparison (Category.assoc m.base n.base p.base))
    (compComparison_assoc hc D m.base n.base p.base) m.fibre n.fibre p.fibre
  rw [D.relativeMapComparison_hom_app] at key
  refine coherentHom_eq_of_heq hb ?_
  simp only [CoherentHom.comp_fibre]
  exact heq_of_eq_eqToHom_comp _
    (Functor.fibreComp (D.compComparison m.base (n.base ≫ p.base)) m.fibre
      (Functor.fibreComp (D.compComparison n.base p.base) n.fibre p.fibre)) key

end CoherentHom

namespace CoherentSituation

variable (hc : ModulePushforwardCoherence B S hS) (D : CoherentSituation B S hS)

/-- **The category `Coh_{X/Y}` of Stacks 08KB.**  The category structure on the objects whose
hom-sets are `AlgebraicGeometry.Space.CoherentHom`, whose identity is
`AlgebraicGeometry.Space.CoherentHom.id` and whose composition is
`AlgebraicGeometry.Space.CoherentHom.comp`. -/
@[instance_reducible]
def coherentCategory : Category.{u + 1} (CoherentObject D) where
  Hom A A' := CoherentHom A A'
  id A := CoherentHom.id hc A
  comp m n := CoherentHom.comp m n
  id_comp m := CoherentHom.id_comp hc m
  comp_id m := CoherentHom.comp_id hc m
  assoc m n p := CoherentHom.assoc hc m n p

/-- **The projection of `Coh_{X/Y}` to the test schemes over `Y` of Stacks 08KB**,
`(T, g, F) ↦ (T, g)`: it forgets the module and keeps the base map of a morphism. -/
def coherentProjection : letI : Category.{u + 1} (CoherentObject D) := coherentCategory hc D
    CoherentObject D ⥤ SchemesOver D.Y :=
  letI : Category.{u + 1} (CoherentObject D) := coherentCategory hc D
  { obj := fun A => A.T
    map := fun m => m.base
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

/-- **Stacks 08KB: `Coh_{X/Y}` is a category, with the projection to the test schemes over `Y`**
— the specification `AlgebraicGeometry.Space.CoherentCategoryData`, for a given
pseudofunctoriality datum of the inverse images of Stacks 03LU. -/
def coherentCategoryData : CoherentCategoryData hc D where
  category := coherentCategory hc D
  projection := coherentProjection hc D
  hom_type _ _ := rfl
  identity _ := rfl
  composition _ _ := rfl
  projection_obj _ := rfl
  projection_map _ := rfl

/-- **`Coh_{X/Y}` is a category**, for the canonical pseudofunctoriality datum
`AlgebraicGeometry.Space.modulePushforwardCoherence` of the direct images of Stacks 03LU. -/
@[stacks 08KB "the category structure on Coh_{X/Y}: the identity and associativity laws, which
Stacks 08KB asserts by designation and this library had left unverified"]
def categoryData : CoherentCategoryData (modulePushforwardCoherence B S hS) D :=
  coherentCategoryData (modulePushforwardCoherence B S hS) D

end CoherentSituation

end AlgebraicGeometry.Space

end
