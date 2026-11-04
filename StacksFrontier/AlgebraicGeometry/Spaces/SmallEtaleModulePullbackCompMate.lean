module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge

/-!
# The composition comparison for inverse images of modules, computed on a module and on a section

`AlgebraicGeometry.Space.modulePullbackCompIso` is the comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of
inverse images of `𝒪`-modules of **Stacks 03LU**.  It is built as
`CategoryTheory.Adjunction.leftAdjointUniq` of the two adjunctions
`AlgebraicGeometry.Space.moduleCompAdjunction` and
`AlgebraicGeometry.Space.modulePullbackAdjunction`, so it carries no formula: what determines it
is its compatibility with the units, and
`AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom` states that
compatibility with the composite unit left as `moduleCompAdjunction.unit`, which a consumer
cannot evaluate.

This file writes that equation out — the mate transport.  Every factor other than the
comparison itself is named: the unit of `g^* ⊣ g_*`, the direct image along `g` of the unit of
`f^* ⊣ f_*`, and the comparison `AlgebraicGeometry.Space.modulePushforwardCompIso` of direct
images of **Stacks 03LU**, whose own value on a section is the geometric comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of **Stacks 03G2**, part (3) by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app_apply`.  So the
inverse-image comparison is transported across the adjunction from the already-computed
direct-image comparison, and `AlgebraicGeometry.Space.modulePullback` — a sheafification — is
never unfolded.

## Main results

* `AlgebraicGeometry.Space.moduleCompAdjunction_unit` and
  `AlgebraicGeometry.Space.moduleCompAdjunction_unit_app_assoc`: the unit of the composite
  adjunction of **Stacks 03LU**, as the iterated unit followed by the comparison of direct
  images, and the same on a single module, bracketed and spelled as the consumers below need
  it.
* `AlgebraicGeometry.Space.unit_comp_map_modulePullbackCompIso_hom_app`: **the comparison of
  inverse images, computed on a module** — the unit equation with no `moduleCompAdjunction` left
  in it.  `AlgebraicGeometry.Space.unit_comp_map_modulePullbackCompIso_hom_app_assoc` is the same
  equation regrouped, which is the bracketing in which it can be read on a section.
* `AlgebraicGeometry.Space.unit_comp_map_modulePullbackCompIso_hom_app_val_app`: **the comparison
  of inverse images, computed on a section** — the direct image of the comparison, evaluated on
  the section the iterated unit and the comparison of direct images produce out of a section of
  the module, is the section the unit of `(f ≫ g)^* ⊣ (f ≫ g)_*` produces.
* `AlgebraicGeometry.Space.unit_comp_val_app_apply`: a morphism out of `g_*g^*G` precomposed with
  the unit, read on a section.  This is the lemma that splits the remaining composite above at
  the unit of `g`; see the implementation note for why it is stated with its target abstract and
  its source spelled as the composite functor.
* `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app` and
  `AlgebraicGeometry.Space.comp_modulePushforwardCompIso_hom_app_val_app`: **the comparison of
  direct images of Stacks 03LU is the geometric comparison of Stacks 03G2, part (3) in the
  language of module sections**, as it stands and precomposed with an arbitrary morphism into the
  iterated direct image.  The latter is what splits the remaining composite above at the
  comparison of direct images.  Both come from
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app_apply` through
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_hom_app_apply`, which says that a morphism of
  `𝒪`-modules acts on a section the same way read on the underlying sheaf of sets.

## Implementation notes

*Why the name must be routed through an explicit equality.*  `modulePullbackCompIso` is
`Adjunction.leftAdjointUniq` of the two adjunctions by `Eq.refl`, so Mathlib's
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` ought to apply to a goal mentioning the
name directly.  It does not: handing that lemma to a goal whose statement says
`modulePullbackCompIso` asks one `isDefEq` to unfold the name *and* match the surrounding
composite.  Rewriting first with
`AlgebraicGeometry.Space.modulePullbackCompIso_eq`, an `Eq.refl` at the level of isomorphisms
where nothing is evaluated at a module, leaves the lemma applicable.  This is the same discipline
the direct-image side records: never let a single `isDefEq` bridge two differences at once.

*Which junctions a section-level reading may cross.*  Reading a composite of morphisms
of `𝒪`-modules on a section means applying `.val.app V` to each factor in turn, and at each
junction the elaborator must identify the codomain of one factor with the domain of the next *as
a module of sections*, that is under `.val.obj V`.  Two of the three junctions of the unit
equation are free: the one between the comparison of direct images and the direct image of the
comparison of inverse images is syntactically an identity, and the one between the end of the
composite and the unit of `(f ≫ g)^* ⊣ (f ≫ g)_*` is a single `CategoryTheory.Functor.comp`
unfold, which the elaborator settles by congruence.  The junction at the unit of `g` — where
`(g^* ⋙ g_*).obj G` meets `g_*(g^*G)` — is **not** free, even though the bare equality of those
two modules of sections is immediate.  So the composite is read on a section with that one
junction left uncrossed, the iterated unit and the comparison of direct images staying a single
morphism, and `unit_comp_val_app_apply` supplies the crossing in the one shape where it is free:
its source is spelled `(g^* ⋙ g_*).obj G`, so that at a use site the identification is made
between two *modules* and never between two modules of sections.

*What is not here.*  There is no elementwise formula for the comparison itself, and there cannot
be one: `modulePullback` is a sheafification, so a morphism out of `g^*f^*G` has no description
on sections to state.  The unit equation is the available characterization, and the point of
reading it on a section is that the sections of an inverse image which a consumer meets — the
chart sections of `AlgebraicGeometry.Space.modulePullbackChartSection`, for instance — are
images of unit sections.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### The unit of the composite adjunction -/

/-- **The unit of the composite adjunction of Stacks 03LU.**
`AlgebraicGeometry.Space.moduleCompAdjunction` is the composite of the two adjunctions with its
right adjoint read as `(f ≫ g)_*` along `AlgebraicGeometry.Space.modulePushforwardCompIso`, so
its unit is the unit of the composite adjunction followed by that comparison. -/
theorem moduleCompAdjunction_unit (f : X ⟶ Y) (g : Y ⟶ Z) :
    (moduleCompAdjunction B S hS f g).unit =
      ((modulePullbackAdjunction B S hS g).comp (modulePullbackAdjunction B S hS f)).unit ≫
        Functor.whiskerLeft (modulePullback B S hS g ⋙ modulePullback B S hS f)
          (modulePushforwardCompIso B S hS f g).hom :=
  Adjunction.ofNatIsoRight_unit
    ((modulePullbackAdjunction B S hS g).comp (modulePullbackAdjunction B S hS f))
    (modulePushforwardCompIso B S hS f g)

/-- **The unit of the composite adjunction on a single module, bracketed to the left**: the unit
of `g^* ⊣ g_*`, then the direct image along `g` of the unit of `f^* ⊣ f_*`, then the comparison
of direct images.  This is `CategoryTheory.Adjunction.comp_unit_app` put into
`AlgebraicGeometry.Space.moduleCompAdjunction_unit`, whose whiskering spells the source of the
comparison through the composite functor, as `(g^* ⋙ f^*).obj G`.

The same identity in the other bracketing and the other spelling is
`AlgebraicGeometry.Space.moduleCompAdjunction_unit_app` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackPresentationComplex.lean`: it associates to
the right and spells the source `f^*(g^*G)`, because it comes out of
`CategoryTheory.Adjunction.comp_ofNatIsoRight_unit_app` instead of the whiskering.

*Why this is not that lemma composed with `CategoryTheory.Category.assoc`.*  Written
that way — `(Category.assoc _ _ _).trans (imported _ _ _ _ _ _).symm`, with the composite
spelled `(g^* ⋙ f^*).obj G` as every consumer below needs it — the elaborator must identify the
two spellings inside the implicit object arguments of
`CategoryTheory.CategoryStruct.comp`, and reports `(deterministic) timeout at whnf, maximum
number of heartbeats (200000) has been reached`, with the three arguments of `Category.assoc`
given explicitly as well as left implicit.  Spelled `f^*(g^*G)` instead, the delegation does
elaborate — and then neither consumer below can use it, because each reaches the equation after
a `rw [← Category.assoc]` on a goal carrying the `⋙` spelling and `rw` matches syntactically.
Respelling the consumers is not available either: their section-level readings are the ones the
implementation notes below record as forced to the composite-functor spelling.  Two routes to
one identity, at two spellings neither of which serves the other's consumers. -/
theorem moduleCompAdjunction_unit_app_assoc (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Modules.{u, u} B S hS Z.1 Z.2) :
    (moduleCompAdjunction B S hS f g).unit.app G =
      ((modulePullbackAdjunction B S hS g).unit.app G ≫
          (modulePushforward B S hS g).map
            ((modulePullbackAdjunction B S hS f).unit.app
              ((modulePullback B S hS g).obj G))) ≫
        (modulePushforwardCompIso B S hS f g).hom.app
          ((modulePullback B S hS g ⋙ modulePullback B S hS f).obj G) :=
  (NatTrans.congr_app (moduleCompAdjunction_unit B S hS f g) G).trans
    ((NatTrans.comp_app _ _ G).trans
      (congrArg (fun m ↦ m ≫ (modulePushforwardCompIso B S hS f g).hom.app
          ((modulePullback B S hS g ⋙ modulePullback B S hS f).obj G))
        (Adjunction.comp_unit_app (modulePullbackAdjunction B S hS g)
          (modulePullbackAdjunction B S hS f) G)))

/-! ### The comparison of inverse images on a module -/

/-- **Stacks 03LU, the composition comparison for inverse images, computed on a module.**  The
unit of `g^* ⊣ g_*`, the direct image along `g` of the unit of `f^* ⊣ f_*`, the comparison
`AlgebraicGeometry.Space.modulePushforwardCompIso` of direct images and the direct image along
`f ≫ g` of the comparison of inverse images compose to the unit of `(f ≫ g)^* ⊣ (f ≫ g)_*`.

This is `AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom` on a module
with the composite unit written out, so that nothing in it is a name a consumer cannot evaluate.
Since the transpose is a bijection it determines the comparison, and it is the mate
correspondence: the only factor with content is the comparison of direct images, which
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` identifies
with the geometric comparison of Stacks 03G2, part (3). -/
theorem unit_comp_map_modulePullbackCompIso_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Modules.{u, u} B S hS Z.1 Z.2) :
    ((modulePullbackAdjunction B S hS g).unit.app G ≫
          (modulePushforward B S hS g).map
            ((modulePullbackAdjunction B S hS f).unit.app
              ((modulePullback B S hS g).obj G))) ≫
        (modulePushforwardCompIso B S hS f g).hom.app
            ((modulePullback B S hS g ⋙ modulePullback B S hS f).obj G) ≫
          (modulePushforward B S hS (f ≫ g)).map
            ((modulePullbackCompIso B S hS f g).hom.app G) =
      (modulePullbackAdjunction B S hS (f ≫ g)).unit.app G := by
  rw [← Category.assoc, ← moduleCompAdjunction_unit_app_assoc,
    modulePullbackCompIso_eq B S hS f g]
  exact Adjunction.unit_leftAdjointUniq_hom_app (moduleCompAdjunction B S hS f g)
    (modulePullbackAdjunction B S hS (f ≫ g)) G

/-- `AlgebraicGeometry.Space.unit_comp_map_modulePullbackCompIso_hom_app` regrouped, with the
iterated unit and the comparison of direct images as one factor and the direct image of the
comparison of inverse images as the other.

This is the bracketing in which the equation can be read on a section: the junction between the
two factors is syntactically an identity, whereas the junction at the unit of `g` is the one
crossing a section-level reading may not make.  The proof is that of the former, the regrouping
being absorbed by `CategoryTheory.Category.assoc`. -/
theorem unit_comp_map_modulePullbackCompIso_hom_app_assoc (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Modules.{u, u} B S hS Z.1 Z.2) :
    ((modulePullbackAdjunction B S hS g).unit.app G ≫
          (modulePushforward B S hS g).map
              ((modulePullbackAdjunction B S hS f).unit.app
                ((modulePullback B S hS g).obj G)) ≫
            (modulePushforwardCompIso B S hS f g).hom.app
              ((modulePullback B S hS g ⋙ modulePullback B S hS f).obj G)) ≫
        (modulePushforward B S hS (f ≫ g)).map
          ((modulePullbackCompIso B S hS f g).hom.app G) =
      (modulePullbackAdjunction B S hS (f ≫ g)).unit.app G := by
  simpa only [Category.assoc] using unit_comp_map_modulePullbackCompIso_hom_app B S hS f g G

/-! ### The comparison of inverse images on a section -/

/-- **Stacks 03LU, the composition comparison for inverse images, computed on a section.**  For a
section `s` of `G` over an object `V` of the small étale site of `Z`, the direct image along
`f ≫ g` of the comparison `g^*f^*G ≅ (f ≫ g)^*G` carries the section produced by the iterated
unit followed by the comparison of direct images to the section produced by the unit of
`(f ≫ g)^* ⊣ (f ≫ g)_*`.

This is the form a consumer computing with the comparison on sections works with:  the inverse
image is a sheafification, so the comparison has no elementwise formula, but the sections of an
inverse image that a consumer meets are images of unit sections, and this says what the
comparison does to them.  The remaining composite is split at the unit of `g` by
`AlgebraicGeometry.Space.unit_comp_val_app_apply` and the comparison of direct images inside it
is the geometric comparison of Stacks 03G2, part (3) by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app_apply`. -/
theorem unit_comp_map_modulePullbackCompIso_hom_app_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (V : (SmallEtale B S hS Z.1)ᵒᵖ)
    (s : G.val.obj V) :
    ((modulePushforward B S hS (f ≫ g)).map
          ((modulePullbackCompIso B S hS f g).hom.app G)).val.app V
        (((modulePullbackAdjunction B S hS g).unit.app G ≫
            (modulePushforward B S hS g).map
                ((modulePullbackAdjunction B S hS f).unit.app
                  ((modulePullback B S hS g).obj G)) ≫
              (modulePushforwardCompIso B S hS f g).hom.app
                ((modulePullback B S hS g ⋙ modulePullback B S hS f).obj G)).val.app V s) =
      ((modulePullbackAdjunction B S hS (f ≫ g)).unit.app G).val.app V s :=
  (Stacks.Sheaves.RingedToposModules.comp_val_app_apply
      ((modulePullbackAdjunction B S hS g).unit.app G ≫
        (modulePushforward B S hS g).map
            ((modulePullbackAdjunction B S hS f).unit.app ((modulePullback B S hS g).obj G)) ≫
          (modulePushforwardCompIso B S hS f g).hom.app
            ((modulePullback B S hS g ⋙ modulePullback B S hS f).obj G))
      ((modulePushforward B S hS (f ≫ g)).map
        ((modulePullbackCompIso B S hS f g).hom.app G)) V s).symm.trans
    (congrArg (fun m ↦ m.val.app V s)
      (unit_comp_map_modulePullbackCompIso_hom_app_assoc B S hS f g G))

/-- **A morphism out of `g_*g^*G` precomposed with the unit of Stacks 03D7, read on a section.**
This splits the composite left in
`AlgebraicGeometry.Space.unit_comp_map_modulePullbackCompIso_hom_app_val_app` at the unit of `g`.

The target `N` is arbitrary and the source of `b` is spelled as the composite functor applied to
`G`, which is exactly how the unit's own codomain is spelled.  Both are forced: with the source
written `g_*(g^*G)` instead, the statement would ask the elaborator to identify the two spellings
*under* `.val.obj V`, while written this way every junction is syntactically an identity and a
use site performs only an identification between two modules.  See the implementation notes. -/
theorem unit_comp_val_app_apply (g : Y ⟶ Z) (G : Modules.{u, u} B S hS Z.1 Z.2)
    {N : Modules.{u, u} B S hS Z.1 Z.2}
    (b : (modulePullback B S hS g ⋙ modulePushforward B S hS g).obj G ⟶ N)
    (V : (SmallEtale B S hS Z.1)ᵒᵖ) (s : G.val.obj V) :
    ((modulePullbackAdjunction B S hS g).unit.app G ≫ b).val.app V s =
      b.val.app V (((modulePullbackAdjunction B S hS g).unit.app G).val.app V s) :=
  Stacks.Sheaves.RingedToposModules.comp_val_app_apply
    ((modulePullbackAdjunction B S hS g).unit.app G) b V s

/-! ### The comparison of direct images in the language of module sections -/

/-- **A morphism of `𝒪`-modules acts on a section the way it does on the underlying sheaf of
sets.**  The underlying sheaf of sets of a sheaf of modules is the module of sections with its
addition and its scalar action forgotten, so this is a `rfl`; what it is for is to carry a
statement proved about `Stacks.Sheaves.RingedToposModules`' underlying sheaves of sets into the
`.val.app` language that the consumers of `AlgebraicGeometry.Space.Modules` work in. -/
theorem moduleSheafFunctor_map_hom_app_apply {W : AlgebraicSpaces B S hS}
    {M₁ M₂ : Modules.{u, u} B S hS W.1 W.2} (m : M₁ ⟶ M₂)
    (V : (SmallEtale B S hS W.1)ᵒᵖ) (t : M₁.val.obj V) :
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map m).hom.app V t =
      m.val.app V t :=
  rfl

/-! `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app` is declared in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`, which this
module now imports; it was stated here a second time, with the source of the composite spelled
`(f ⋙ g).obj F` rather than `g.obj (f.obj F)` -- the same object by `rfl`. -/

/-- **The comparison of Stacks 03LU acting on a section, as a function of that section.**  This
is `((modulePushforwardCompIso B S hS f g).hom.app F).val.app V` applied to `t`, named.

Naming it is what makes the comparison usable under a chart projection.  The sections of
`(f ≫ g)_*F` are an object of `ModuleCat`, so applying the component `.val.app V` to a section
goes through the concrete-category coercion, and the coercion's implicit arguments are chosen
from the *expected* type at the point of application.  Written inside an equation whose other
side is a function of those sections, the application therefore elaborates to a different term
than the same application written with no expected type — the two are definitionally equal, and
comparing them forces `AlgebraicGeometry.Space.modulePushforward` to be unfolded.  With the
application named, the term is the same on both sides of every junction.  See the implementation
notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartSectionComp.lean`. -/
noncomputable def modulePushforwardCompIsoSection (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (V : (SmallEtale B S hS Z.1)ᵒᵖ)
    (t : ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj F).val.obj V) :
    ((modulePushforward B S hS (f ≫ g)).obj F).val.obj V :=
  ((modulePushforwardCompIso B S hS f g).hom.app F).val.app V t

/-- The named action of the comparison of Stacks 03LU on a section is that comparison's
component applied to the section. -/
theorem modulePushforwardCompIsoSection_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (V : (SmallEtale B S hS Z.1)ᵒᵖ)
    (t : ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj F).val.obj V) :
    modulePushforwardCompIsoSection B S hS f g F V t =
      ((modulePushforwardCompIso B S hS f g).hom.app F).val.app V t :=
  rfl

/-- **A morphism into the iterated direct image followed by the comparison of Stacks 03LU, on a
section.**  This splits the composite left in
`AlgebraicGeometry.Space.unit_comp_map_modulePullbackCompIso_hom_app_val_app` at the comparison
of direct images, leaving the geometric comparison of Stacks 03G2, part (3).

As with `AlgebraicGeometry.Space.unit_comp_val_app_apply`, the morphism is arbitrary and its
codomain is spelled as the composite functor applied to the module, which is how the comparison
spells its own domain.  So every junction here is syntactically an identity, and a use site —
where the morphism is the direct image along `g` of the unit of `f^* ⊣ f_*`, whose codomain is
spelled differently — performs only an identification between two modules. -/
theorem comp_modulePushforwardCompIso_hom_app_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules.{u, u} B S hS X.1 X.2) {A : Modules.{u, u} B S hS Z.1 Z.2}
    (a : A ⟶ (modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj M)
    (V : (SmallEtale B S hS Z.1)ᵒᵖ) (t : A.val.obj V) :
    (a ≫ (modulePushforwardCompIso B S hS f g).hom.app M).val.app V t =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj M)).hom.app V
          (a.val.app V t) :=
  (Stacks.Sheaves.RingedToposModules.comp_val_app_apply a
      ((modulePushforwardCompIso B S hS f g).hom.app M) V t).trans
    (modulePushforwardCompIso_hom_app_val_app B S hS f g M V (a.val.app V t))

end AlgebraicGeometry.Space

end
