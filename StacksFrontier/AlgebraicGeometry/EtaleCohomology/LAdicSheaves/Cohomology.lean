module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# ℓ-adic cohomology

Let `X` be a Noetherian scheme and let `F = {Fₙ}` be an ℓ-adic sheaf on `X`. Every finite
level `Fₙ` is a sheaf of `ℤ/ℓⁿ⁺¹ℤ`-modules on the small étale site of `X`, so it has étale
cohomology groups `Hⁱ(X, Fₙ)`, and the transition maps of the inverse system induce maps
`Hⁱ(X, Fₙ₊₁) ⟶ Hⁱ(X, Fₙ)`. The ℓ-adic cohomology of `F` in degree `i` is the inverse limit
`Hⁱ(X, F) = limₙ Hⁱ(X, Fₙ)`.

## Main definitions

* `Stacks.EtaleCohomology.etaleCohomologyFunctor` is étale cohomology of an abelian sheaf on
  the small étale site of `X` in a fixed degree, as a functor.
* `Stacks.EtaleCohomology.LAdicSheaf.abelianLevel` is the abelian sheaf underlying a finite
  level of an ℓ-adic sheaf, and `Stacks.EtaleCohomology.LAdicSheaf.abelianTransition` is the
  map between two consecutive ones.
* `Stacks.EtaleCohomology.LAdicSheaf.cohomologySystem` is the inverse system
  `n ↦ Hⁱ(X, Fₙ)` of the étale cohomology groups of the finite levels.
* `Stacks.EtaleCohomology.LAdicSheaf.cohomology` is the ℓ-adic cohomology `Hⁱ(X, F)`, the
  inverse limit of that system, and `Stacks.EtaleCohomology.LAdicSheaf.cohomologyπ` gives its
  projections to the finite levels.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.cohomologySystem_obj` identifies the `n`-th term of the
  inverse system with the étale cohomology of the `n`-th level.
* `Stacks.EtaleCohomology.LAdicSheaf.cohomologySystem_map_succ` identifies the map from level
  `n + 1` to level `n` with the one induced by the transition map of the ℓ-adic sheaf.

## Implementation notes

`Hⁱ(X, Fₙ)` is sheaf cohomology on the small étale site of `X` in the sense of
`CategoryTheory.Sheaf.H`, the `Ext`-group from the constant sheaf with value `ℤ`. It is taken
of the abelian sheaf underlying `Fₙ`: a level and its restriction of scalars to the
coefficient ring of the previous level have one and the same underlying abelian sheaf, so the
transition maps of an ℓ-adic sheaf already form an inverse system of abelian sheaves on a
single site, and the varying coefficient rings `ℤ/ℓⁿ⁺¹ℤ` play no further role. The limit is
accordingly formed in abelian groups, where it is the limit of the underlying groups.

Both the objects and the morphisms of the small étale site are needed for cohomology, and the
objects live one universe above the morphisms; the coefficient universe is therefore the
object universe, and the existence of `Ext`-groups in it is carried as a hypothesis, exactly
as in the definition of `CategoryTheory.Sheaf.H` itself.

Only Noetherianness of `X` is assumed, that being what the finite levels of an ℓ-adic sheaf
require. Separatedness and finite type over an algebraically closed field are not needed to
form the limit; they are the hypotheses under which the compactly supported variant
`Hⁱ_c(X, F) = limₙ Hⁱ_c(X, Fₙ)`, of the same shape with compactly supported cohomology in
place of `Hⁱ`, is available, and under which these groups are finitely generated.

## References

* [Stacks Project, Tag 03UT](https://stacks.math.columbia.edu/tag/03UT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite
  AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

variable [HasExt.{u + 1}
  (Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})]

/-- Étale cohomology of an abelian sheaf on the small étale site of `X` in degree `i`, as a
functor: the `Ext`-group from the constant sheaf with value `ℤ`. -/
public abbrev etaleCohomologyFunctor (i : ℕ) :
    Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} :=
  Sheaf.functorH.{u + 1, u + 1, u, u + 1} (SmallEtale.topology B X.1 X.property) i

variable (ℓ : ℕ)

/-- The abelian sheaf underlying a sheaf of `ℤ/ℓⁿ⁺¹ℤ`-modules on the small étale site. -/
public abbrev FiniteLevelSheaf.toAbelianSheaf (n : ℕ) :
    FiniteLevelSheaf B X ℓ n ⥤
      Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1} :=
  sheafCompose (SmallEtale.topology B X.1 X.property)
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-- The abelian sheaf underlying the level `n` of an ℓ-adic sheaf. -/
public def LAdicSheaf.abelianLevel (F : LAdicSheaf B X ℓ) (n : ℕ) :
    Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1} :=
  (FiniteLevelSheaf.toAbelianSheaf B X ℓ n).obj (F.level n)

/-- The transition map of an ℓ-adic sheaf, read on the underlying abelian sheaves: restricting
the scalars of a level to the coefficient ring of the previous one leaves the underlying
abelian sheaf unchanged, so the transition goes from level `n + 1` to level `n`. -/
public def LAdicSheaf.abelianTransition (F : LAdicSheaf B X ℓ) (n : ℕ) :
    LAdicSheaf.abelianLevel B X ℓ F (n + 1) ⟶ LAdicSheaf.abelianLevel B X ℓ F n :=
  (FiniteLevelSheaf.toAbelianSheaf B X ℓ (n + 1)).map (F.transition n)

/-- The inverse system `n ↦ Hⁱ(X, Fₙ)` of the étale cohomology groups of the finite levels of
an ℓ-adic sheaf, with the maps induced by its transition maps. -/
public def LAdicSheaf.cohomologySystem (F : LAdicSheaf B X ℓ) (i : ℕ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n => (etaleCohomologyFunctor B X i).obj (LAdicSheaf.abelianLevel B X ℓ F n))
    (fun n => (etaleCohomologyFunctor B X i).map (LAdicSheaf.abelianTransition B X ℓ F n))

/-- The `n`-th term of the inverse system is the étale cohomology of the `n`-th level. -/
@[simp]
public theorem LAdicSheaf.cohomologySystem_obj (F : LAdicSheaf B X ℓ) (i n : ℕ) :
    (LAdicSheaf.cohomologySystem B X ℓ F i).obj (op n) =
      (etaleCohomologyFunctor B X i).obj (LAdicSheaf.abelianLevel B X ℓ F n) :=
  rfl

/-- The map of the inverse system from level `n + 1` to level `n` is the one induced on étale
cohomology by the transition map of the ℓ-adic sheaf. -/
@[simp]
public theorem LAdicSheaf.cohomologySystem_map_succ (F : LAdicSheaf B X ℓ) (i n : ℕ) :
    (LAdicSheaf.cohomologySystem B X ℓ F i).map (homOfLE (n.le_add_right 1)).op =
      (etaleCohomologyFunctor B X i).map (LAdicSheaf.abelianTransition B X ℓ F n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **The ℓ-adic cohomology of an ℓ-adic sheaf.** For an ℓ-adic sheaf `F = {Fₙ}` on `X` and a
degree `i`, this is `Hⁱ(X, F) = limₙ Hⁱ(X, Fₙ)`. -/
@[stacks 03UT "ℓ-adic cohomology", sga "7 I 0.1" "b)", sga "5 VI 3.1" "def of H^i(X,F)"]
public def LAdicSheaf.cohomology (F : LAdicSheaf B X ℓ) (i : ℕ) : AddCommGrpCat.{u + 1} :=
  limit (LAdicSheaf.cohomologySystem B X ℓ F i)

/-- The projection of the ℓ-adic cohomology onto the étale cohomology of a finite level. -/
public def LAdicSheaf.cohomologyπ (F : LAdicSheaf B X ℓ) (i n : ℕ) :
    LAdicSheaf.cohomology B X ℓ F i ⟶
      (etaleCohomologyFunctor B X i).obj (LAdicSheaf.abelianLevel B X ℓ F n) :=
  limit.π (LAdicSheaf.cohomologySystem B X ℓ F i) (op n)

end Stacks.EtaleCohomology

end
