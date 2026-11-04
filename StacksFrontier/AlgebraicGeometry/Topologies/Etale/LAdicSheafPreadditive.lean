module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LAdicSheaves

/-!
# Additive structure on ℓ-adic sheaves

Morphisms of ℓ-adic sheaves form an abelian group under levelwise addition, and composition is
bilinear, so the category of ℓ-adic sheaves on a Noetherian scheme is preadditive.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.instAddCommGroup`: levelwise addition of
  morphisms of ℓ-adic sheaves.

## Main results

* `AlgebraicGeometry.SmallEtale.additive_sheafCompose_finiteLevelRingHom`: restriction of
  scalars between consecutive coefficient rings is additive on sheaves.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.preadditive`: ℓ-adic sheaves form a preadditive
  category.

## Implementation notes

The compatibility condition on a morphism of ℓ-adic sheaves is an equation between composites
in which the transition map of the target is post-composed and the restriction of scalars of the
component is pre-composed. Both operations are additive — the sheaf categories at each finite
level are preadditive, and restriction of scalars along the coefficient quotient is an additive
functor — so a sum of compatible families is compatible. The group structure is therefore
transported from the product of the Hom groups at the finite levels along the injection sending a
morphism to its family of components.

## References

* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.obj X.property)
  (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))]

/-- Restriction of scalars along the quotient of consecutive coefficient rings is additive on
sheaves, being additive on modules and acting componentwise. -/
public instance additive_sheafCompose_finiteLevelRingHom (n : ℕ) :
    (sheafCompose (SmallEtale.topology B X.obj X.property)
      (ModuleCat.restrictScalars.{m, 0, 0} (finiteLevelRingHom ℓ n))).Additive := by
  constructor
  intro F G f g
  ext U : 3
  rfl

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
  HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.obj] [Fact ℓ.Prime]

namespace LAdicSheaf.Hom

variable {B X ℓ} (F G : LAdicSheaf.{u, m} B X ℓ)

/-- A morphism of ℓ-adic sheaves is determined by its family of components. -/
public theorem app_injective :
    Function.Injective (fun f : LAdicSheaf.Hom B X ℓ F G => f.app) :=
  fun _ _ h => LAdicSheaf.Hom.ext _ _ _ (fun n => congrFun h n)

variable {F G}

/-- The zero morphism of ℓ-adic sheaves, zero at every level. -/
public instance instZero : Zero (LAdicSheaf.Hom B X ℓ F G) :=
  ⟨⟨fun _ => 0, by intro n; simp⟩⟩

/-- The sum of two morphisms of ℓ-adic sheaves, taken levelwise. -/
public instance instAdd : Add (LAdicSheaf.Hom B X ℓ F G) :=
  ⟨fun f g => ⟨fun n => f.app n + g.app n, by
    intro n
    simp only [Preadditive.add_comp, Functor.map_add, Preadditive.comp_add,
      f.naturality n, g.naturality n]⟩⟩

/-- The negative of a morphism of ℓ-adic sheaves, taken levelwise. -/
public instance instNeg : Neg (LAdicSheaf.Hom B X ℓ F G) :=
  ⟨fun f => ⟨fun n => -f.app n, by
    intro n
    simp only [Preadditive.neg_comp, Functor.map_neg, Preadditive.comp_neg,
      f.naturality n]⟩⟩

/-- The difference of two morphisms of ℓ-adic sheaves, taken levelwise. -/
public instance instSub : Sub (LAdicSheaf.Hom B X ℓ F G) :=
  ⟨fun f g => ⟨fun n => f.app n - g.app n, by
    intro n
    simp only [Preadditive.sub_comp, Functor.map_sub, Preadditive.comp_sub,
      f.naturality n, g.naturality n]⟩⟩

/-- Multiplication of a morphism of ℓ-adic sheaves by a natural number, taken levelwise. -/
public instance instSMulNat : SMul ℕ (LAdicSheaf.Hom B X ℓ F G) :=
  ⟨fun k f => ⟨fun n => k • f.app n, by
    intro n
    simp only [Preadditive.nsmul_comp, Functor.map_nsmul, Preadditive.comp_nsmul,
      f.naturality n]⟩⟩

/-- Multiplication of a morphism of ℓ-adic sheaves by an integer, taken levelwise. -/
public instance instSMulInt : SMul ℤ (LAdicSheaf.Hom B X ℓ F G) :=
  ⟨fun k f => ⟨fun n => k • f.app n, by
    intro n
    simp only [Preadditive.zsmul_comp, Functor.map_zsmul, Preadditive.comp_zsmul,
      f.naturality n]⟩⟩

/-- Morphisms of ℓ-adic sheaves form an abelian group under levelwise addition. -/
public instance instAddCommGroup : AddCommGroup (LAdicSheaf.Hom B X ℓ F G) :=
  Function.Injective.addCommGroup (fun f => f.app) (app_injective F G)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The components of a sum of morphisms of ℓ-adic sheaves are the sums of the components. -/
@[simp]
public theorem add_app (f g : LAdicSheaf.Hom B X ℓ F G) (n : ℕ) :
    (f + g).app n = f.app n + g.app n := rfl

/-- The components of the zero morphism of ℓ-adic sheaves are zero. -/
@[simp]
public theorem zero_app (n : ℕ) : (0 : LAdicSheaf.Hom B X ℓ F G).app n = 0 := rfl

/-- The components of the negative of a morphism of ℓ-adic sheaves are the negatives of the
components. -/
@[simp]
public theorem neg_app (f : LAdicSheaf.Hom B X ℓ F G) (n : ℕ) :
    (-f).app n = -f.app n := rfl

end LAdicSheaf.Hom

/-- **Stacks 03UO.** ℓ-adic sheaves form a preadditive category: morphisms add levelwise and
composition is bilinear. -/
@[stacks 03UO "preadditive"]
public instance LAdicSheaf.preadditive : Preadditive (LAdicSheaf.{u, m} B X ℓ) where
  homGroup _ _ := LAdicSheaf.Hom.instAddCommGroup
  add_comp _ _ _ f f' g :=
    LAdicSheaf.Hom.ext _ _ _ fun n =>
      Preadditive.add_comp _ _ _ (f.app n) (f'.app n) (g.app n)
  comp_add _ _ _ f g g' :=
    LAdicSheaf.Hom.ext _ _ _ fun n =>
      Preadditive.comp_add _ _ _ (f.app n) (g.app n) (g'.app n)

end AlgebraicGeometry.SmallEtale

end
