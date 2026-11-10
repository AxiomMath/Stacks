module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Pi
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Evaluation at a component of a product of categories

Let `B : I → Type u` be a family of categories. Limits and colimits in `∀ i, B i` are computed
componentwise, so evaluation at the `j`-th component,
`CategoryTheory.Pi.eval B j : (∀ i, B i) ⥤ B j`, preserves them. That is proved here, with the
index type, the objects, the morphisms and the shape in four independent universes.

## Main results

* `CategoryTheory.Pi.evalPreservesLimitsOfShape` and
  `CategoryTheory.Pi.evalPreservesColimitsOfShape`: evaluation preserves limits and colimits of
  any shape for which they exist componentwise. Mathlib has the cone-assembly primitives these
  are built from but no `Preserves` instance.
* `CategoryTheory.Pi.pi'PreservesLimit` and `CategoryTheory.Pi.pi'PreservesColimit`: dually, a
  functor into a product of categories preserves a (co)limit as soon as each of its components
  does.
* `CategoryTheory.Pi.concentrateAdjunction`: when the components have zero objects and the index
  type has decidable equality, `CategoryTheory.Pi.eval B j` has a left adjoint
  `CategoryTheory.Pi.concentrate B j`, which places an object of `B j` in degree `j` and the zero
  object in every other degree.
* `CategoryTheory.Functor.piAdjunction`: a family of adjunctions gives an adjunction between the
  products of the categories.

## Implementation notes

Mathlib's `CategoryTheory.pi.coneOfConeEvalIsLimit` and its siblings assemble componentwise
limit cones into a limit cone, which is exactly the content needed, but they are stated for
`I : Type v₁` with `[∀ i, Category.{v₁} (B i)]` and `J : Type v₁` — index type, morphism
universe and shape in a single universe. The consumers here have an index type whose universe is
unrelated to the morphisms of the categories, so the four assembly lemmas are restated with the
universes free; the proofs are Mathlib's.

The two `Preserves` instances are then immediate: the assembled cone over the componentwise
limits *is* a limit, and its image under `Pi.eval B i` is, by definition, the limit cone of the
`i`-th component, so `preservesLimit_of_preserves_limit_cone` applies with nothing to check.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Pi

universe w v u v' u' j₁ j₂

section Limits

variable {I : Type w} {B : I → Type u} [∀ i, Category.{v} (B i)]
  {J : Type j₁} [Category.{j₂} J]

/-- The componentwise cone of a cone over a functor into a product of categories. This is
`CategoryTheory.pi.coneCompEval` with the universes free. -/
def coneCompEval {F : J ⥤ ∀ i, B i} (c : Cone F) (i : I) : Cone (F ⋙ Pi.eval B i) where
  pt := c.pt i
  π :=
    { app := fun j => c.π.app j i
      naturality := fun _ _ f => congr_fun (c.π.naturality f) i }

/-- A family of componentwise cones assembles into a cone. This is
`CategoryTheory.pi.coneOfConeCompEval` with the universes free. -/
def coneOfConeCompEval {F : J ⥤ ∀ i, B i} (c : ∀ i, Cone (F ⋙ Pi.eval B i)) : Cone F where
  pt i := (c i).pt
  π :=
    { app := fun j i => (c i).π.app j
      naturality := fun _ _ f => by
        funext i
        exact (c i).π.naturality f }

/-- A family of componentwise limit cones assembles into a limit cone. This is
`CategoryTheory.pi.coneOfConeEvalIsLimit` with the universes free. -/
def coneOfConeEvalIsLimit {F : J ⥤ ∀ i, B i} {c : ∀ i, Cone (F ⋙ Pi.eval B i)}
    (P : ∀ i, IsLimit (c i)) : IsLimit (coneOfConeCompEval c) where
  lift s i := (P i).lift (coneCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coneCompEval s i) j
  uniq s m hm := by
    funext i
    exact (P i).uniq (coneCompEval s i) (m i) fun j => congr_fun (hm j) i

/-- The componentwise cocone of a cocone over a functor into a product of categories. This is
`CategoryTheory.pi.coconeCompEval` with the universes free. -/
def coconeCompEval {F : J ⥤ ∀ i, B i} (c : Cocone F) (i : I) : Cocone (F ⋙ Pi.eval B i) where
  pt := c.pt i
  ι :=
    { app := fun j => c.ι.app j i
      naturality := fun _ _ f => congr_fun (c.ι.naturality f) i }

/-- A family of componentwise cocones assembles into a cocone. This is
`CategoryTheory.pi.coconeOfCoconeCompEval` with the universes free. -/
def coconeOfCoconeCompEval {F : J ⥤ ∀ i, B i} (c : ∀ i, Cocone (F ⋙ Pi.eval B i)) :
    Cocone F where
  pt i := (c i).pt
  ι :=
    { app := fun j i => (c i).ι.app j
      naturality := fun _ _ f => by
        funext i
        exact (c i).ι.naturality f }

/-- A family of componentwise colimit cocones assembles into a colimit cocone. This is
`CategoryTheory.pi.coconeOfCoconeEvalIsColimit` with the universes free. -/
def coconeOfCoconeEvalIsColimit {F : J ⥤ ∀ i, B i} {c : ∀ i, Cocone (F ⋙ Pi.eval B i)}
    (P : ∀ i, IsColimit (c i)) : IsColimit (coconeOfCoconeCompEval c) where
  desc s i := (P i).desc (coconeCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coconeCompEval s i) j
  uniq s m hm := by
    funext i
    exact (P i).uniq (coconeCompEval s i) (m i) fun j => congr_fun (hm j) i

/-- **Evaluation at a component preserves limits**: limits in a product of categories are
computed componentwise. -/
instance evalPreservesLimitsOfShape [∀ i, HasLimitsOfShape J (B i)] (i : I) :
    PreservesLimitsOfShape J (Pi.eval B i) where
  preservesLimit {F} :=
    preservesLimit_of_preserves_limit_cone
      (coneOfConeEvalIsLimit (F := F) fun k => limit.isLimit (F ⋙ Pi.eval B k))
      (limit.isLimit (F ⋙ Pi.eval B i))

/-- **Evaluation at a component preserves colimits**: colimits in a product of categories are
computed componentwise. -/
instance evalPreservesColimitsOfShape [∀ i, HasColimitsOfShape J (B i)] (i : I) :
    PreservesColimitsOfShape J (Pi.eval B i) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (coconeOfCoconeEvalIsColimit (F := F) fun k => colimit.isColimit (F ⋙ Pi.eval B k))
      (colimit.isColimit (F ⋙ Pi.eval B i))

/-- A cone in a product of categories is a limit cone as soon as each of its components is. The
assembly of a cone's own components is the cone itself, so this is `coneOfConeEvalIsLimit`. -/
def isLimitOfIsLimitConeCompEval {F : J ⥤ ∀ i, B i} {c : Cone F}
    (P : ∀ i, IsLimit (coneCompEval c i)) : IsLimit c :=
  coneOfConeEvalIsLimit P

/-- A cocone in a product of categories is a colimit cocone as soon as each of its components
is. -/
def isColimitOfIsColimitCoconeCompEval {F : J ⥤ ∀ i, B i} {c : Cocone F}
    (P : ∀ i, IsColimit (coconeCompEval c i)) : IsColimit c :=
  coconeOfCoconeEvalIsColimit P

end Limits

section Pi'

variable {I : Type w} {A : Type u'} [Category.{v'} A] {B : I → Type u} [∀ i, Category.{v} (B i)]
  {J : Type j₁} [Category.{j₂} J]

/-- **A functor into a product of categories preserves a limit as soon as each of its
components does**: the limit is computed componentwise. -/
instance pi'PreservesLimit (G : ∀ i, A ⥤ B i) (F : J ⥤ A) [∀ i, PreservesLimit F (G i)] :
    PreservesLimit F (Functor.pi' G) where
  preserves hc := ⟨isLimitOfIsLimitConeCompEval fun i => isLimitOfPreserves (G i) hc⟩

/-- **A functor into a product of categories preserves a colimit as soon as each of its
components does**: the colimit is computed componentwise. -/
instance pi'PreservesColimit (G : ∀ i, A ⥤ B i) (F : J ⥤ A) [∀ i, PreservesColimit F (G i)] :
    PreservesColimit F (Functor.pi' G) where
  preserves hc := ⟨isColimitOfIsColimitCoconeCompEval fun i => isColimitOfPreserves (G i) hc⟩

/-- A functor into a product of categories preserves limits of shape `J` as soon as each of its
components does. -/
instance pi'PreservesLimitsOfShape (G : ∀ i, A ⥤ B i) [∀ i, PreservesLimitsOfShape J (G i)] :
    PreservesLimitsOfShape J (Functor.pi' G) where
  preservesLimit := inferInstance

/-- A functor into a product of categories preserves colimits of shape `J` as soon as each of its
components does. -/
instance pi'PreservesColimitsOfShape (G : ∀ i, A ⥤ B i) [∀ i, PreservesColimitsOfShape J (G i)] :
    PreservesColimitsOfShape J (Functor.pi' G) where
  preservesColimit := inferInstance

end Pi'

section LeftAdjoint

variable {I : Type w} (B : I → Type u) [∀ i, Category.{v} (B i)] [DecidableEq I]
  [∀ i, HasZeroObject (B i)]

open scoped ZeroObject

/-- The `k`-th component of the functor concentrating an object of `B j` in degree `j`: the
identity functor when `k = j`, and the constant functor with value the zero object otherwise. -/
noncomputable def concentrateComponent (j k : I) : B j ⥤ B k :=
  if h : j = k then (h ▸ 𝟭 (B j) : B j ⥤ B k) else (Functor.const _).obj 0

/-- The `j`-th component of the functor concentrating in degree `j` is the identity functor. -/
lemma concentrateComponent_self (j : I) : concentrateComponent B j j = 𝟭 (B j) :=
  dite_eq_left rfl

/-- For `k ≠ j`, the `k`-th component of the functor concentrating in degree `j` is the constant
functor with value the zero object. -/
lemma concentrateComponent_of_ne {j k : I} (h : j ≠ k) :
    concentrateComponent B j k = (Functor.const _).obj 0 :=
  dite_eq_right h

/-- For `k ≠ j`, the `k`-th component of the functor concentrating in degree `j` takes only zero
objects as values. -/
lemma isZero_concentrateComponent_obj {j k : I} (h : j ≠ k) (X : B j) :
    IsZero ((concentrateComponent B j k).obj X) := by
  rw [concentrateComponent_of_ne B h]
  exact isZero_zero _

/-- The functor concentrating an object of `B j` in degree `j`: it sends `X` to the family which
is `X` in degree `j` and the zero object in every other degree. -/
noncomputable def concentrate (j : I) : B j ⥤ ∀ i, B i :=
  Functor.pi' (concentrateComponent B j)

/-- Degree `j` of `concentrate B j` is the identity functor. -/
noncomputable def concentrateCompEval (j : I) : concentrate B j ⋙ Pi.eval B j ≅ 𝟭 (B j) :=
  eqToIso (concentrateComponent_self B j)

/-- The component of the counit of `concentrate B j ⊣ Pi.eval B j` in a degree `k` equal to `j`.
Branching the whole natural transformation on `j = k` (rather than its components) lets the
equality be eliminated by `subst` before any morphism is written down. -/
noncomputable def diagCounit {j k : I} (h : j = k) :
    Pi.eval B j ⋙ concentrateComponent B j k ⟶ Pi.eval B k := by
  subst h
  exact Functor.whiskerLeft (Pi.eval B j) (concentrateCompEval B j).hom

/-- The component of the counit of `concentrate B j ⊣ Pi.eval B j` in a degree `k ≠ j`: its
source is a zero object, so there is nothing to choose. -/
noncomputable def offDiagCounit {j k : I} (h : j ≠ k) :
    Pi.eval B j ⋙ concentrateComponent B j k ⟶ Pi.eval B k where
  app M := (isZero_concentrateComponent_obj B h (M j)).to_ (M k)
  naturality _ _ _ := (isZero_concentrateComponent_obj B h _).eq_of_src _ _

/-- The degree `k` component of the counit of `concentrate B j ⊣ Pi.eval B j`. -/
noncomputable def counitComponent (j k : I) :
    Pi.eval B j ⋙ concentrateComponent B j k ⟶ Pi.eval B k :=
  if h : j = k then diagCounit B h else offDiagCounit B h

/-- In degree `j`, the component of the counit of `concentrate B j ⊣ Pi.eval B j` is the
whiskering of `concentrateCompEval B j` by `Pi.eval B j`. -/
lemma counitComponent_self (j : I) : counitComponent B j j =
    Functor.whiskerLeft (Pi.eval B j) (concentrateCompEval B j).hom :=
  dite_eq_left rfl

/-- The left triangle identity for an isomorphism to the identity functor. -/
private lemma map_inv_app_comp_hom_app {C : Type*} [Category C] {G : C ⥤ C} (e : G ≅ 𝟭 C)
    (X : C) : G.map (e.inv.app X) ≫ e.hom.app (G.obj X) = 𝟙 (G.obj X) := by
  rw [e.hom.naturality, Functor.id_map]
  exact e.hom_inv_id_app X

/-- **Evaluation at a component has a left adjoint**, namely the functor concentrating an object
in that degree. In particular `Pi.eval B j` preserves limits, and `concentrate B j` preserves
colimits. -/
noncomputable def concentrateAdjunction (j : I) : concentrate B j ⊣ Pi.eval B j where
  unit := (concentrateCompEval B j).inv
  counit := NatTrans.pi' (C := B) (fun k => counitComponent B j k)
  left_triangle_components X := by
    ext k
    by_cases h : j = k
    · subst h
      change (concentrateComponent B j j).map ((concentrateCompEval B j).inv.app X) ≫
          (counitComponent B j j).app ((concentrate B j).obj X) = _
      rw [counitComponent_self, Functor.whiskerLeft_app]
      exact map_inv_app_comp_hom_app (concentrateCompEval B j) X
    · exact (isZero_concentrateComponent_obj B h _).eq_of_src _ _
  right_triangle_components M := by
    change (concentrateCompEval B j).inv.app (M j) ≫ (counitComponent B j j).app M = _
    rw [counitComponent_self, Functor.whiskerLeft_app]
    exact (concentrateCompEval B j).inv_hom_id_app (M j)

end LeftAdjoint

end CategoryTheory.Pi

namespace CategoryTheory.Functor

universe w v u v' u'

variable {I : Type w} {A : I → Type u'} [∀ i, Category.{v'} (A i)]
  {B : I → Type u} [∀ i, Category.{v} (B i)]

/-- **A family of adjunctions gives an adjunction between the products of the categories.**
Everything is componentwise, including the two triangle identities. -/
def piAdjunction {L : ∀ i, A i ⥤ B i} {R : ∀ i, B i ⥤ A i} (adj : ∀ i, L i ⊣ R i) :
    Functor.pi L ⊣ Functor.pi R where
  unit :=
    { app := fun X i => (adj i).unit.app (X i)
      naturality := fun _ _ f => by funext i; exact (adj i).unit.naturality (f i) }
  counit :=
    { app := fun Y i => (adj i).counit.app (Y i)
      naturality := fun _ _ f => by funext i; exact (adj i).counit.naturality (f i) }
  left_triangle_components X := by
    funext i
    exact (adj i).left_triangle_components (X i)
  right_triangle_components Y := by
    funext i
    exact (adj i).right_triangle_components (Y i)

end CategoryTheory.Functor

end
