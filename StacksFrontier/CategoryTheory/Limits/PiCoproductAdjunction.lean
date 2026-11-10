module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Pi.Basic

/-!
# The left adjoint of a functor into a product of categories

Let `F i : A ⥤ B i` be a family of functors out of one category, assembled into
`Functor.pi' F : A ⥤ ∀ i, B i`. If every `F i` has a left adjoint `G i`, then `Functor.pi' F`
has a left adjoint as well, namely the functor sending a family `(Z i)` to the coproduct
`∐ i, G i (Z i)`: a map out of that coproduct is a family of maps out of its summands, and each
of those transposes across `G i ⊣ F i`.

Such a coproduct of left adjoints is exact as soon as each `G i` is and coproducts of shape `I`
are exact, which is the Grothendieck axiom AB4.

## Main definitions

* `CategoryTheory.Limits.discreteHomEquiv`: a morphism out of a coproduct is a family of
  morphisms out of the summands.
* `CategoryTheory.Limits.piDiscrete`: the family `i ↦ G i (Z i)`, read as a functor out of the
  discrete category on the index type.
* `CategoryTheory.Limits.piCoproduct`: the functor `(Z i) ↦ ∐ i, G i (Z i)`.

## Main results

* `CategoryTheory.Limits.piCoproductAdjunction`: `piCoproduct G ⊣ Functor.pi' F`.
* `CategoryTheory.Limits.preservesFiniteLimits_piCoproduct`: `piCoproduct G` preserves finite
  limits when each `G i` does and coproducts of shape `I` are exact.
* `CategoryTheory.Limits.concentrateAdjunction`: **evaluation at an index has a left adjoint**,
  namely `CategoryTheory.Limits.concentrate`, which places an object at that index and the zero
  object elsewhere; and
  `CategoryTheory.Limits.preservesFiniteLimits_concentrate`: that left adjoint is exact.
* `CategoryTheory.Limits.preservesFiniteLimits_pi_of_eval`: a functor into a product of
  categories preserves finite limits as soon as each of its components does.

## Implementation notes

`piCoproduct` is the composite of `piDiscrete` with `CategoryTheory.Limits.colim`, rather than a
functor written out with `∐` directly, because exactness of coproducts is stated in Mathlib as
`colim` preserving finite limits (`CategoryTheory.HasExactColimitsOfShape`) and this
factorization is what lets that be applied. A coproduct *is* the colimit of a `Discrete.functor`,
so the two readings agree; the cocone inclusions and the universal property are used in the
`colimit` spelling throughout so that no comparison between them is ever needed.

Evaluation of a product of categories at an index preserves finite limits, since limits in a
product category are computed componentwise. Mathlib's cone assembly for product categories
(`CategoryTheory.pi.coneOfConeCompEval`) constrains the index type, the shape category and the
hom universe to coincide, so the declarations it would be used through are given here at
independent universes instead.

The concentration functor is `Functor.pi'` of a family `concentrateComponent j k`, which is the
identity functor transported along `j = k` on the diagonal and constant at the zero object off
it. Writing the family rather than a bare `if` on objects keeps the dependent transport in one
place: the single coherence equation `concentrate_obj_self`, whose naturality is
`eqToHom_concentrate_obj_self`. Every `eqToHom` in the adjunction is one of its two directions,
and the off-diagonal cases are discharged by `IsZero.eq_of_src` rather than by any transport.
-/

@[expose] public section

universe w v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {I : Type w} {A : Type u₁} [Category.{v₁} A]
  {B : I → Type u₂} [∀ i, Category.{v₂} (B i)]

/-- **A morphism out of a coproduct is a family of morphisms out of the summands.** The
coproduct is spelled as the colimit of a functor out of a discrete category, which is what it
is by definition. -/
@[simps]
noncomputable def discreteHomEquiv (Z : Discrete I ⥤ A) [HasColimit Z] (a : A) :
    (colimit Z ⟶ a) ≃ ∀ i, (Z.obj ⟨i⟩ ⟶ a) where
  toFun g i := colimit.ι Z ⟨i⟩ ≫ g
  invFun h := colimit.desc Z (Cocone.mk a (Discrete.natTrans fun i => h i.as))
  left_inv _ := colimit.hom_ext fun i => by
    obtain ⟨i⟩ := i
    simp
  right_inv _ := funext fun _ => by simp

section PiEval

variable {J : Type u₃} [Category.{v₃} J]

/-- A cone over a functor into a product of categories, read at one index. -/
@[simps]
def coneEvalPi (F : J ⥤ ∀ i, B i) (c : Cone F) (i : I) : Cone (F ⋙ Pi.eval B i) where
  pt := c.pt i
  π :=
    { app := fun j => c.π.app j i
      naturality := fun _ _ f => congrFun (c.π.naturality f) i }

/-- A family of cones over the components of a functor into a product of categories, assembled
into a cone. -/
@[simps]
def coneOfConeEvalPi (F : J ⥤ ∀ i, B i) (c : ∀ i, Cone (F ⋙ Pi.eval B i)) : Cone F where
  pt := fun i => (c i).pt
  π :=
    { app := fun j i => (c i).π.app j
      naturality := fun _ _ f => funext fun i => (c i).π.naturality f }

/-- A cone assembled from componentwise limit cones is a limit cone: limits in a product of
categories are computed componentwise. -/
def isLimitConeOfConeEvalPi (F : J ⥤ ∀ i, B i) (c : ∀ i, Cone (F ⋙ Pi.eval B i))
    (hc : ∀ i, IsLimit (c i)) : IsLimit (coneOfConeEvalPi F c) where
  lift s i := (hc i).lift (coneEvalPi F s i)
  fac s j := funext fun i => (hc i).fac (coneEvalPi F s i) j
  uniq s m w := funext fun i => (hc i).uniq (coneEvalPi F s i) (m i) fun j => congrFun (w j) i

/-- Evaluation at an index preserves the limits of a functor into a product of categories whose
components all have limits. -/
instance preservesLimit_piEval (F : J ⥤ ∀ i, B i) (i : I)
    [∀ k, HasLimit (F ⋙ Pi.eval B k)] : PreservesLimit F (Pi.eval B i) :=
  preservesLimit_of_preserves_limit_cone
    (isLimitConeOfConeEvalPi F (fun _ => limit.cone _) fun _ => limit.isLimit _)
    (limit.isLimit _)

end PiEval

/-- Evaluation at an index preserves finite limits. -/
noncomputable instance preservesFiniteLimits_piEval [∀ i, HasFiniteLimits (B i)] (i : I) :
    PreservesFiniteLimits (Pi.eval B i) where
  preservesFiniteLimits _ _ _ := ⟨fun {_} => inferInstance⟩

/-- The family `i ↦ G i (Z i)`, read as a functor out of the discrete category on the index
type. -/
@[simps]
def piDiscrete (G : ∀ i, B i ⥤ A) : (∀ i, B i) ⥤ (Discrete I ⥤ A) where
  obj Z := Discrete.functor fun i => (G i).obj (Z i)
  map f := Discrete.natTrans fun i => (G i.as).map (f i.as)
  map_id Z := NatTrans.ext (funext fun i => (G i.as).map_id (Z i.as))
  map_comp f g := NatTrans.ext (funext fun i => (G i.as).map_comp (f i.as) (g i.as))

/-- **The coproduct of a family of functors into a fixed category**: the functor sending a
family `(Z i)` to `∐ i, G i (Z i)`. -/
noncomputable def piCoproduct (G : ∀ i, B i ⥤ A) [HasColimitsOfShape (Discrete I) A] :
    (∀ i, B i) ⥤ A :=
  piDiscrete G ⋙ colim

/-- The inclusion of the `i`-th summand of `(piCoproduct G).obj Z`, with its source spelled as
`G i (Z i)`. -/
noncomputable def piCoproductι (G : ∀ i, B i ⥤ A) [HasColimitsOfShape (Discrete I) A]
    (Z : ∀ i, B i) (i : I) : (G i).obj (Z i) ⟶ (piCoproduct G).obj Z :=
  colimit.ι ((piDiscrete G).obj Z) ⟨i⟩

/-- `piCoproduct G` acts on a morphism summand by summand. -/
theorem ι_piCoproduct_map (G : ∀ i, B i ⥤ A) [HasColimitsOfShape (Discrete I) A]
    {Z Z' : ∀ i, B i} (f : Z ⟶ Z') (i : I) :
    piCoproductι G Z i ≫ (piCoproduct G).map f =
      (G i).map (f i) ≫ piCoproductι G Z' i :=
  ι_colimMap ((piDiscrete G).map f) ⟨i⟩

/-- Two morphisms out of `(piCoproduct G).obj Z` that agree on every summand are equal. -/
theorem piCoproduct_hom_ext (G : ∀ i, B i ⥤ A) [HasColimitsOfShape (Discrete I) A]
    {Z : ∀ i, B i} {a : A} {p q : (piCoproduct G).obj Z ⟶ a}
    (h : ∀ i, piCoproductι G Z i ≫ p = piCoproductι G Z i ≫ q) : p = q :=
  colimit.hom_ext fun i => by obtain ⟨i⟩ := i; exact h i

/-- The transposition underlying `piCoproductAdjunction`: a map `∐ i, G i (Z i) ⟶ a` is a
family of maps `G i (Z i) ⟶ a`, and each of those is a map `Z i ⟶ F i a`. -/
noncomputable def piCoproductHomEquiv (F : ∀ i, A ⥤ B i) (G : ∀ i, B i ⥤ A)
    (adj : ∀ i, G i ⊣ F i) [HasColimitsOfShape (Discrete I) A] (Z : ∀ i, B i) (a : A) :
    ((piCoproduct G).obj Z ⟶ a) ≃ (Z ⟶ (Functor.pi' F).obj a) :=
  (discreteHomEquiv ((piDiscrete G).obj Z) a).trans
    (Equiv.piCongrRight fun i => (adj i).homEquiv (Z i) a)

/-- The transpose of a map out of the coproduct is, at `i`, the transpose of its restriction to
the `i`-th summand. -/
theorem piCoproductHomEquiv_apply (F : ∀ i, A ⥤ B i) (G : ∀ i, B i ⥤ A)
    (adj : ∀ i, G i ⊣ F i) [HasColimitsOfShape (Discrete I) A] (Z : ∀ i, B i) (a : A)
    (g : (piCoproduct G).obj Z ⟶ a) (i : I) :
    piCoproductHomEquiv F G adj Z a g i =
      (adj i).homEquiv (Z i) a (piCoproductι G Z i ≫ g) :=
  rfl

/-- The inverse transpose, restricted to the `i`-th summand, is the inverse transpose of the
`i`-th component. -/
theorem ι_piCoproductHomEquiv_symm (F : ∀ i, A ⥤ B i) (G : ∀ i, B i ⥤ A)
    (adj : ∀ i, G i ⊣ F i) [HasColimitsOfShape (Discrete I) A] (Z : ∀ i, B i) (a : A)
    (h : Z ⟶ (Functor.pi' F).obj a) (i : I) :
    piCoproductι G Z i ≫ (piCoproductHomEquiv F G adj Z a).symm h =
      ((adj i).homEquiv (Z i) a).symm (h i) :=
  colimit.ι_desc _ _

/-- **The left adjoint of a functor into a product of categories is the coproduct of the left
adjoints of its components.** -/
noncomputable def piCoproductAdjunction (F : ∀ i, A ⥤ B i) (G : ∀ i, B i ⥤ A)
    (adj : ∀ i, G i ⊣ F i) [HasColimitsOfShape (Discrete I) A] :
    piCoproduct G ⊣ Functor.pi' F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := piCoproductHomEquiv F G adj
      homEquiv_naturality_left_symm := fun {Z Z' a} f g =>
        piCoproduct_hom_ext G fun i => by
          calc piCoproductι G Z i ≫ (piCoproductHomEquiv F G adj Z a).symm (f ≫ g)
              = ((adj i).homEquiv (Z i) a).symm (f i ≫ g i) :=
                ι_piCoproductHomEquiv_symm F G adj Z a (f ≫ g) i
            _ = (G i).map (f i) ≫ ((adj i).homEquiv (Z' i) a).symm (g i) :=
                (adj i).homEquiv_naturality_left_symm (f i) (g i)
            _ = (G i).map (f i) ≫
                  (piCoproductι G Z' i ≫ (piCoproductHomEquiv F G adj Z' a).symm g) := by
                rw [ι_piCoproductHomEquiv_symm]
            _ = (piCoproductι G Z i ≫ (piCoproduct G).map f) ≫
                  (piCoproductHomEquiv F G adj Z' a).symm g := by
                rw [ι_piCoproduct_map, Category.assoc]
            _ = piCoproductι G Z i ≫
                  (piCoproduct G).map f ≫ (piCoproductHomEquiv F G adj Z' a).symm g :=
                Category.assoc _ _ _
      homEquiv_naturality_right := fun {Z a a'} g h => funext fun i =>
        (congrArg ((adj i).homEquiv (Z i) a')
            (Category.assoc (piCoproductι G Z i) g h).symm).trans
          ((adj i).homEquiv_naturality_right (piCoproductι G Z i ≫ g) h) }

/-- `piDiscrete G`, read at an index, is evaluation there followed by `G i`. -/
def piDiscreteCompEvaluation (G : ∀ i, B i ⥤ A) (i : Discrete I) :
    piDiscrete G ⋙ (evaluation (Discrete I) A).obj i ≅ Pi.eval B i.as ⋙ G i.as :=
  Iso.refl _

/-- `piDiscrete` preserves finite limits as soon as every `G i` does: limits in a functor
category out of a discrete category are computed at each object, and there the functor is
evaluation followed by `G i`. -/
theorem preservesFiniteLimits_piDiscrete (G : ∀ i, B i ⥤ A) [∀ i, HasFiniteLimits (B i)]
    (hG : ∀ i, PreservesFiniteLimits (G i)) : PreservesFiniteLimits (piDiscrete G) where
  preservesFiniteLimits L _ _ := by
    refine preservesLimitsOfShape_of_evaluation _ L fun i => ?_
    have := hG i.as
    exact preservesLimitsOfShape_of_natIso (piDiscreteCompEvaluation G i).symm

/-- **A coproduct of functors preserving finite limits preserves finite limits**, given that
coproducts of that shape are exact. Together with `piCoproductAdjunction`, which makes
`piCoproduct G` a left adjoint and so right exact, this is exactness of `piCoproduct G`. -/
theorem preservesFiniteLimits_piCoproduct (G : ∀ i, B i ⥤ A)
    [HasColimitsOfShape (Discrete I) A] [HasFiniteLimits A]
    [HasExactColimitsOfShape (Discrete I) A] [∀ i, HasFiniteLimits (B i)]
    (hG : ∀ i, PreservesFiniteLimits (G i)) :
    PreservesFiniteLimits (piCoproduct G) :=
  have := preservesFiniteLimits_piDiscrete G hG
  have := HasExactColimitsOfShape.preservesFiniteLimits (J := Discrete I) (C := A)
  comp_preservesFiniteLimits (piDiscrete G) colim

/-- A cone in a product of categories is a limit cone as soon as each of its components is:
limits in a product of categories are computed componentwise. -/
def isLimitOfIsLimitEvalPi {J : Type u₃} [Category.{v₃} J] (F : J ⥤ ∀ i, B i) (c : Cone F)
    (hc : ∀ i, IsLimit (coneEvalPi F c i)) : IsLimit c where
  lift s i := (hc i).lift (coneEvalPi F s i)
  fac s j := funext fun i => (hc i).fac (coneEvalPi F s i) j
  uniq s m w := funext fun i => (hc i).uniq (coneEvalPi F s i) (m i) fun j => congrFun (w j) i

/-- A functor into a product of categories preserves limits of a shape as soon as each of its
components does. -/
lemma preservesLimitsOfShape_pi_of_eval {D : Type u₁} [Category.{v₁} D] (H : D ⥤ ∀ i, B i)
    (J : Type u₃) [Category.{v₃} J]
    (h : ∀ i, PreservesLimitsOfShape J (H ⋙ Pi.eval B i)) : PreservesLimitsOfShape J H where
  preservesLimit {F} :=
    ⟨fun {c} hc => ⟨isLimitOfIsLimitEvalPi (F ⋙ H) (H.mapCone c) fun i =>
      have := h i
      isLimitOfPreserves (H ⋙ Pi.eval B i) hc⟩⟩

/-- A functor into a product of categories preserves finite limits as soon as each of its
components does. -/
lemma preservesFiniteLimits_pi_of_eval {D : Type u₁} [Category.{v₁} D] (H : D ⥤ ∀ i, B i)
    (h : ∀ i, PreservesFiniteLimits (H ⋙ Pi.eval B i)) : PreservesFiniteLimits H where
  preservesFiniteLimits J _ _ :=
    preservesLimitsOfShape_pi_of_eval H J fun i => (h i).preservesFiniteLimits J

/-! ### Extension by zero into a product of categories

Evaluation at an index has a left adjoint, the functor concentrating an object at that index
and placing the zero object elsewhere, and that left adjoint is exact. -/

section Concentrate

open scoped ZeroObject

variable [∀ i, HasZeroObject (B i)]

/-- The constant functor at a zero object preserves limits of any shape: a zero object is
terminal, so the constant cone at it is a limit cone. -/
theorem preservesLimitsOfShape_constZero (k : I) {D : Type u₁} [Category.{v₁} D]
    (J : Type u₃) [Category.{v₃} J] :
    PreservesLimitsOfShape J ((Functor.const D).obj (0 : B k)) where
  preservesLimit := ⟨fun _ => ⟨{
    lift := fun s => (isZero_zero (B k)).from_ s.pt
    fac := fun _ _ => (isZero_zero (B k)).eq_of_tgt _ _
    uniq := fun _ _ _ => (isZero_zero (B k)).eq_of_tgt _ _ }⟩⟩

variable [DecidableEq I]

/-- The functor `B j ⥤ B k` which is the identity when `j = k` and constant at the zero object
otherwise. Transport along `j = k` rather than an `eqToHom` on objects, so that the two
branches are definitionally separated. -/
noncomputable def concentrateComponent (j k : I) : B j ⥤ B k :=
  if h : j = k then h ▸ 𝟭 (B j) else (Functor.const (B j)).obj 0

/-- On the diagonal, `concentrateComponent` is the identity functor. -/
theorem concentrateComponent_self (j : I) :
    concentrateComponent (B := B) j j = 𝟭 (B j) :=
  dite_eq_left rfl

/-- Off the diagonal, `concentrateComponent` is constant at the zero object. -/
theorem concentrateComponent_of_ne {j k : I} (h : j ≠ k) :
    concentrateComponent (B := B) j k = (Functor.const (B j)).obj 0 :=
  dite_eq_right h

/-- The single coherence isomorphism of `concentrateComponent` on the diagonal. -/
noncomputable def concentrateComponentSelfIso (j : I) :
    concentrateComponent (B := B) j j ≅ 𝟭 (B j) :=
  eqToIso (concentrateComponent_self j)

/-- Off the diagonal, the values of `concentrateComponent` are zero. -/
theorem isZero_concentrateComponent_obj {j k : I} (h : j ≠ k) (X : B j) :
    IsZero ((concentrateComponent (B := B) j k).obj X) :=
  (isZero_zero (B k)).of_iso ((eqToIso (concentrateComponent_of_ne h)).app X)

/-- **The family concentrated at `j`**: `X` in degree `j`, the zero object elsewhere. -/
noncomputable def concentrate (j : I) : B j ⥤ ∀ k, B k :=
  Functor.pi' (concentrateComponent (B := B) j)

/-- The family concentrated at `j`, read at an index. -/
theorem concentrate_obj_apply (j k : I) (X : B j) :
    (concentrate j).obj X k = (concentrateComponent (B := B) j k).obj X :=
  rfl

/-- The family concentrated at `j`, read at `j` itself, is `X`. This is the one coherence
equation of the construction; every `eqToHom` below is one of its two directions. -/
theorem concentrate_obj_self (j : I) (X : B j) :
    (concentrate (B := B) j).obj X j = X :=
  congrArg (fun F : B j ⥤ B j => F.obj X) (concentrateComponent_self j)

/-- The coherence equation is natural: transporting along it intertwines `f` with its image
under `concentrateComponent j j`. -/
theorem eqToHom_concentrate_obj_self {j : I} {X X' : B j} (f : X' ⟶ X) :
    eqToHom (concentrate_obj_self j X') ≫ f =
      (concentrateComponent (B := B) j j).map f ≫ eqToHom (concentrate_obj_self j X) := by
  have h := (eqToIso (concentrateComponent_self (B := B) j)).hom.naturality f
  simp only [eqToIso.hom, eqToHom_app, Functor.id_map] at h
  exact h.symm

/-- The diagonal component of the extension of `h : X ⟶ Y j` to the family concentrated at
`j`, as a function of the proof that the index is `j`. Separating it out keeps the transport in
one place. -/
noncomputable def concentrateHomMkDiag (j : I) {X : B j} {Y : ∀ k, B k} (h : X ⟶ Y j)
    (k : I) (hk : j = k) :
    (concentrate (B := B) j).obj X k ⟶ Y k := by
  subst hk; exact eqToHom (concentrate_obj_self j X) ≫ h

/-- At the proof `rfl`, the diagonal component is `h` precomposed with the transport along
`concentrate_obj_self`. -/
@[simp]
theorem concentrateHomMkDiag_rfl (j : I) {X : B j} {Y : ∀ k, B k} (h : X ⟶ Y j) :
    concentrateHomMkDiag j h j rfl = eqToHom (concentrate_obj_self j X) ≫ h :=
  rfl

/-- A map out of the family concentrated at `j` is determined by its `j`-th component, and any
map there extends: off the diagonal the source is a zero object. -/
noncomputable def concentrateHomMk (j : I) {X : B j} {Y : ∀ k, B k} (h : X ⟶ Y j) :
    (concentrate j).obj X ⟶ Y := fun k =>
  if hk : j = k then concentrateHomMkDiag j h k hk
  else (isZero_concentrateComponent_obj hk X).to_ (Y k)

/-- The `j`-th component of `concentrateHomMk j h` is `h` precomposed with the transport along
`concentrate_obj_self`. -/
@[simp]
theorem concentrateHomMk_self (j : I) {X : B j} {Y : ∀ k, B k} (h : X ⟶ Y j) :
    concentrateHomMk j h j = eqToHom (concentrate_obj_self j X) ≫ h := by
  unfold concentrateHomMk
  exact dite_eq_left rfl

/-- Two maps out of the family concentrated at `j` agree as soon as their `j`-th components
do: off the diagonal the source is a zero object. -/
theorem concentrate_hom_ext (j : I) {X : B j} {Y : ∀ k, B k}
    {p q : (concentrate j).obj X ⟶ Y} (h : p j = q j) : p = q := by
  funext k
  by_cases hk : j = k
  · subst hk; exact h
  · exact (isZero_concentrateComponent_obj hk X).eq_of_src _ _

/-- **Evaluation at an index has a left adjoint**, namely concentration at that index. -/
noncomputable def concentrateAdjunction (j : I) : concentrate (B := B) j ⊣ Pi.eval B j :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun g => eqToHom (concentrate_obj_self j X).symm ≫ g j
          invFun := fun h => concentrateHomMk j h
          left_inv := fun g => by
            have key : concentrateHomMk j (X := X) (Y := Y)
                (eqToHom (concentrate_obj_self j X).symm ≫ g j) j =
                  eqToHom (concentrate_obj_self j X) ≫
                    eqToHom (concentrate_obj_self j X).symm ≫ g j :=
              concentrateHomMk_self j _
            have key2 : eqToHom (concentrate_obj_self j X) ≫
                eqToHom (concentrate_obj_self j X).symm ≫ g j = g j := by
              rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
            exact concentrate_hom_ext j (key.trans key2)
          right_inv := fun h => by
            have key : concentrateHomMk j (X := X) (Y := Y) h j =
                eqToHom (concentrate_obj_self j X) ≫ h := concentrateHomMk_self j h
            dsimp only
            rw [key, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        have key : concentrateHomMk j (X := X') (Y := Y) (f ≫ g) j =
            eqToHom (concentrate_obj_self j X') ≫ f ≫ g := concentrateHomMk_self j _
        have key' : concentrateHomMk j (X := X) (Y := Y) g j =
            eqToHom (concentrate_obj_self j X) ≫ g := concentrateHomMk_self j g
        have main : eqToHom (concentrate_obj_self j X') ≫ f ≫ g =
            (concentrateComponent (B := B) j j).map f ≫
              (eqToHom (concentrate_obj_self j X) ≫ g) :=
          ((Category.assoc (eqToHom (concentrate_obj_self j X')) f g).symm.trans
            (congrArg (· ≫ g) (eqToHom_concentrate_obj_self f))).trans
            (Category.assoc _ _ _)
        exact concentrate_hom_ext j (key.trans (main.trans (congrArg
          (fun z => (concentrateComponent (B := B) j j).map f ≫ z) key'.symm)))
      homEquiv_naturality_right := fun {X Y Y'} g h =>
        (Category.assoc (eqToHom (concentrate_obj_self j X).symm) (g j) (h j)).symm }

/-- Every component of `concentrate j` preserves finite limits: on the diagonal it is the
identity, and off the diagonal it is constant at a zero object. -/
theorem preservesFiniteLimits_concentrateComponent (j k : I) :
    PreservesFiniteLimits (concentrateComponent (B := B) j k) := by
  by_cases hk : j = k
  · subst hk
    rw [concentrateComponent_self]
    infer_instance
  · rw [concentrateComponent_of_ne hk]
    exact ⟨fun J _ _ => preservesLimitsOfShape_constZero k J⟩

/-- **Concentration at an index preserves finite limits**: its components do, and limits in a
product of categories are computed componentwise. Together with `concentrateAdjunction`, which
makes it a left adjoint and so right exact, this is exactness of `concentrate j`. -/
theorem preservesFiniteLimits_concentrate (j : I) :
    PreservesFiniteLimits (concentrate (B := B) j) :=
  preservesFiniteLimits_pi_of_eval (concentrate (B := B) j) fun k =>
    have := preservesFiniteLimits_concentrateComponent (B := B) j k
    preservesFiniteLimits_of_natIso (Functor.pi'CompEval _ k).symm

end Concentrate

end CategoryTheory.Limits

end
