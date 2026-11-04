module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Thickenings along a decreasing tower of ideal sheaves, and the cohomology comparison

Let `X` be a scheme and `J₀ ≥ J₁ ≥ ⋯` a decreasing sequence of quasi-coherent ideal sheaves on
`X`. The closed subschemes `Qₙ` cut out by `Jₙ` then form a tower of closed immersions
`Q₀ ⟶ Q₁ ⟶ ⋯ ⟶ X`, a module `F` on `X` restricts to `Fₙ = ιₙ^* F` on `Qₙ`, and for each degree
`i` there is a canonical comparison map

`Hⁱ(X, F) ⟶ lim Hⁱ(Qₙ, Fₙ)`.

The tower of interest is `Jₙ = I ^ n` for the ideal `I` of the zero scheme `Z(s)` of a global
section `s` of an invertible module `L`: then `Qₙ` is the `n`-th infinitesimal neighbourhood of
`Z(s)` and the comparison map is the one whose invertibility in low degrees is the content of
[Stacks, Tag 0EL1].

## Main definitions

* `Stacks.Algebraization.restrictionFunctor`: the endofunctor `ι_* ι^*` of `X.Modules` attached
  to a morphism `ι` with target `X`.
* `Stacks.Algebraization.restrictionTransition`: for a factorization `g ≫ ι = k` the induced map
  `ι_* ι^* F ⟶ k_* k^* F`.
* `Stacks.Algebraization.IdealTower.scheme`, `ι` and `map`: the subschemes `Qₙ`, their closed
  immersions into `X` and the tower maps `Qₙ ⟶ Qₙ₊₁`.
* `Stacks.Algebraization.IdealTower.overFunctor`: the whole tower, as a functor `ℕ ⥤ Over X`.
* `Stacks.Algebraization.IdealTower.system` and `cone`: the inverse system `n ↦ ιₙ_* ιₙ^* F` in
  `X.Modules` and the cone on it with vertex `F`.
* `Stacks.Algebraization.IdealTower.cohomologyTower`: the inverse system `n ↦ Hⁱ(Qₙ, Fₙ)`.
* `Stacks.Algebraization.IdealTower.comparison`: the comparison map
  `Hⁱ(X, F) ⟶ lim Hⁱ(Qₙ, Fₙ)`.
* `Stacks.Algebraization.zeroSchemeTowerIdeal`: the tower `n ↦ I ^ n` of powers of the ideal of
  the zero scheme of a global section of an invertible module.

## Main results

* `Stacks.Algebraization.restrictionTransition_unit`: the transition maps are compatible with the
  adjunction units.
* `Stacks.Algebraization.IdealTower.isClosedImmersion_map`: the tower maps are closed immersions.
* `Stacks.Algebraization.IdealTower.cohomologyIso`: `Hⁱ(X, ιₙ_* Fₙ) ≅ Hⁱ(Qₙ, Fₙ)`.
* `Stacks.Algebraization.IdealTower.comparison_π`: the comparison map composed with the `n`-th
  projection is the map on cohomology induced by `ιₙ`.
* `Stacks.Algebraization.isInvertible_sheafObj_of_isInvertibleModule` and
  `Stacks.Algebraization.isInvertibleModule_of_isInvertible_sheafObj`: the two spellings of
  invertibility of an `𝒪_X`-module agree.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.Algebraization

/-! ### Restriction to a subscheme, seen on the ambient scheme -/

section Restriction

variable {X Y Z : Scheme.{u}}

/-- The endofunctor `ι_* ι^*` of `X.Modules` attached to a morphism `ι : Y ⟶ X`. For a closed
immersion `ι` and a quasi-coherent `F` this is the restriction of `F` to the closed subscheme,
pushed back onto `X`. -/
abbrev restrictionFunctor (ι : Y ⟶ X) : X.Modules ⥤ X.Modules :=
  Scheme.Modules.pullback ι ⋙ Scheme.Modules.pushforward ι

variable (ι : Y ⟶ X) (g : Z ⟶ Y) (k : Z ⟶ X) (h : g ≫ ι = k) (F : X.Modules)

/-- The comparison of pullback along a factorization `g ≫ ι = k` with the composite of the two
pullbacks. -/
def pullbackFactorIso :
    Scheme.Modules.pullback ι ⋙ Scheme.Modules.pullback g ≅ Scheme.Modules.pullback k :=
  Scheme.Modules.pullbackComp g ι ≪≫ Scheme.Modules.pullbackCongr h

/-- The adjoint of the transition map of `restrictionTransition`: the pullback to `Z` of
`ι_* ι^* F`, mapped to the pullback of `F` by the counit at `Y`. -/
def restrictionTransitionAdjoint :
    (Scheme.Modules.pullback k).obj ((restrictionFunctor ι).obj F) ⟶
      (Scheme.Modules.pullback k).obj F :=
  (pullbackFactorIso ι g k h).inv.app ((restrictionFunctor ι).obj F) ≫
    (Scheme.Modules.pullback g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction ι).counit.app
        ((Scheme.Modules.pullback ι).obj F)) ≫
    (pullbackFactorIso ι g k h).hom.app F

/-- Pulling back the unit at `Y` and following the adjoint transition gives the identity. -/
theorem pullback_unit_restrictionTransitionAdjoint :
    (Scheme.Modules.pullback k).map
        ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app F) ≫
      restrictionTransitionAdjoint ι g k h F = 𝟙 _ := by
  have hnat : (Scheme.Modules.pullback k).map
        ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app F) ≫
        (pullbackFactorIso ι g k h).inv.app ((restrictionFunctor ι).obj F) =
      (pullbackFactorIso ι g k h).inv.app F ≫ (Scheme.Modules.pullback g).map
        ((Scheme.Modules.pullback ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app F)) :=
    (pullbackFactorIso ι g k h).inv.naturality
      ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app F)
  rw [restrictionTransitionAdjoint, ← Category.assoc, hnat, Category.assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Adjunction.left_triangle_components,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (pullbackFactorIso ι g k h).inv_hom_id_app F

/-- The map `ι_* ι^* F ⟶ k_* k^* F` induced by a factorization `g ≫ ι = k`. For closed immersions
`ι` and `k` with `k` factoring through `ι` this is restriction from the larger closed subscheme to
the smaller one. -/
def restrictionTransition : (restrictionFunctor ι).obj F ⟶ (restrictionFunctor k).obj F :=
  (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app ((restrictionFunctor ι).obj F) ≫
    (Scheme.Modules.pushforward k).map (restrictionTransitionAdjoint ι g k h F)

/-- The transition map is compatible with the adjunction units: restricting to `Y` and then to `Z`
is restricting to `Z`. -/
theorem restrictionTransition_unit :
    (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app F ≫
        restrictionTransition ι g k h F =
      (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app F := by
  have hnat : (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app F ≫
        (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app
          ((restrictionFunctor ι).obj F) =
      (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app F ≫
        (Scheme.Modules.pushforward k).map ((Scheme.Modules.pullback k).map
          ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app F)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction k).unit.naturality
      ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app F)
  rw [restrictionTransition, ← Category.assoc, hnat, Category.assoc,
    ← CategoryTheory.Functor.map_comp, pullback_unit_restrictionTransitionAdjoint]
  simp

end Restriction

/-! ### The tower of subschemes attached to a decreasing tower of ideal sheaves -/

namespace IdealTower

variable {X : Scheme.{u}} (J : ℕ → X.IdealSheafData) (hJ : ∀ n, J (n + 1) ≤ J n)

/-- The closed subscheme `Qₙ` cut out by the `n`-th ideal sheaf of the tower. -/
abbrev scheme (n : ℕ) : Scheme.{u} := (J n).subscheme

/-- The closed immersion `ιₙ : Qₙ ⟶ X`. -/
abbrev ι (n : ℕ) : scheme J n ⟶ X := (J n).subschemeι

/-- The tower map `Qₙ ⟶ Qₙ₊₁`, the inclusion of closed subschemes coming from `Jₙ₊₁ ≤ Jₙ`. -/
def map (n : ℕ) : scheme J n ⟶ scheme J (n + 1) :=
  Scheme.IdealSheafData.inclusion (hJ n)

/-- The tower map over `X`: `Qₙ ⟶ Qₙ₊₁ ⟶ X` is `Qₙ ⟶ X`. -/
@[reassoc (attr := simp)]
theorem map_ι (n : ℕ) : map J hJ n ≫ ι J (n + 1) = ι J n :=
  Scheme.IdealSheafData.inclusion_subschemeι (hJ n)

/-- The tower maps are closed immersions. -/
instance isClosedImmersion_map (n : ℕ) : IsClosedImmersion (map J hJ n) := by
  have : IsClosedImmersion (map J hJ n ≫ ι J (n + 1)) := by
    rw [map_ι]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (map J hJ n) (ι J (n + 1))

/-- The tower `n ↦ Jₙ` of ideal sheaves, as a functor out of `ℕ` to the opposite of the lattice of
quasi-coherent ideal sheaves. -/
def idealFunctor : ℕ ⥤ (X.IdealSheafData)ᵒᵖ where
  obj n := op (J n)
  map {_ _} f := (homOfLE (antitone_nat_of_succ_le hJ (leOfHom f))).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The tower of closed subschemes `Q₀ ⟶ Q₁ ⟶ ⋯`, as a functor to schemes over `X`. -/
def overFunctor : ℕ ⥤ Over X :=
  idealFunctor J hJ ⋙ Scheme.IdealSheafData.subschemeFunctor X

/-- The `n`-th object of the tower of subschemes is `Qₙ` with its closed immersion into `X`. -/
@[simp]
theorem overFunctor_obj (n : ℕ) : (overFunctor J hJ).obj n = Over.mk (ι J n) := rfl

/-- The successor map of the tower of subschemes is the inclusion `Qₙ ⟶ Qₙ₊₁`. -/
@[simp]
theorem overFunctor_map_succ (n : ℕ) :
    ((overFunctor J hJ).map (homOfLE (Nat.le_succ n))).left = map J hJ n := rfl

/-! ### The inverse system of restrictions and the cone on it -/

variable (F : X.Modules)

/-- The transition map `ιₙ₊₁_* Fₙ₊₁ ⟶ ιₙ_* Fₙ` of the inverse system of restrictions. -/
def transition (n : ℕ) :
    (restrictionFunctor (ι J (n + 1))).obj F ⟶ (restrictionFunctor (ι J n)).obj F :=
  restrictionTransition (ι J (n + 1)) (map J hJ n) (ι J n) (map_ι J hJ n) F

/-- The inverse system `n ↦ ιₙ_* ιₙ^* F` of restrictions of `F` to the tower, as a functor out of
`ℕᵒᵖ`. -/
def system : ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence (X := fun n ↦ (restrictionFunctor (ι J n)).obj F) (transition J hJ F)

/-- The `n`-th term of the inverse system of restrictions is `ιₙ_* ιₙ^* F`. -/
theorem system_obj (n : ℕᵒᵖ) :
    (system J hJ F).obj n = (restrictionFunctor (ι J n.unop)).obj F := rfl

/-- The successor transition of the inverse system of restrictions is `transition`. -/
theorem system_map_succ (n : ℕ) :
    (system J hJ F).map (homOfLE (Nat.le_add_right n 1)).op = transition J hJ F n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The cone on the inverse system of restrictions with vertex `F`, whose leg at `n` is the unit
of the adjunction between pullback and pushforward along `ιₙ`. -/
def cone : Cone (system J hJ F) where
  pt := F
  π := NatTrans.ofOpSequence
    (fun n ↦ (Scheme.Modules.pullbackPushforwardAdjunction (ι J n)).unit.app F)
    (fun n ↦ by
      rw [system_map_succ]
      exact (Category.id_comp _).trans
        (restrictionTransition_unit (ι J (n + 1)) (map J hJ n) (ι J n) (map_ι J hJ n) F).symm)

/-- The `n`-th leg of the cone is the unit of the adjunction along `ιₙ`. -/
theorem cone_π_app (n : ℕᵒᵖ) :
    (cone J hJ F).π.app n =
      (Scheme.Modules.pullbackPushforwardAdjunction (ι J n.unop)).unit.app F := rfl

/-! ### The tower of cohomology groups and the comparison map -/

variable (i : ℕ)

/-- The inverse system `n ↦ Hⁱ(X, ιₙ_* Fₙ)` of cohomology groups on the ambient scheme. -/
def ambientCohomologyTower : ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  system J hJ F ⋙ Hfunctor X.ringCatSheaf ⊤ i

/-- The comparison map `Hⁱ(X, F) ⟶ lim Hⁱ(X, ιₙ_* Fₙ)` on the ambient scheme. -/
def ambientComparison :
    Hgroup X.ringCatSheaf ⊤ i F ⟶ limit (ambientCohomologyTower J hJ F i) :=
  limit.lift (ambientCohomologyTower J hJ F i)
    ((Hfunctor X.ringCatSheaf ⊤ i).mapCone (cone J hJ F))

/-- The ambient comparison map followed by the `n`-th projection is the map on cohomology
induced by the unit of the adjunction along `ιₙ`. -/
@[reassoc]
theorem ambientComparison_π (n : ℕᵒᵖ) :
    ambientComparison J hJ F i ≫ limit.π (ambientCohomologyTower J hJ F i) n =
      (Hfunctor X.ringCatSheaf ⊤ i).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (ι J n.unop)).unit.app F) :=
  limit.lift_π _ _

variable [F.IsQuasicoherent]

/-- Cohomology of the pushforward of the restriction is cohomology on the subscheme. This is
[Stacks, Tag 089W] for the closed, hence affine, immersion `ιₙ`. -/
def cohomologyIso (n : ℕᵒᵖ) :
    (ambientCohomologyTower J hJ F i).obj n ≅
      Hgroup (scheme J n.unop).ringCatSheaf ⊤ i ((Scheme.Modules.pullback (ι J n.unop)).obj F) :=
  (Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp (ι J n.unop) i
    ((Scheme.Modules.pullback (ι J n.unop)).obj F)).symm

/-- The inverse system `n ↦ Hⁱ(Qₙ, Fₙ)` of cohomology groups on the tower of subschemes, with the
transition maps transported from `ambientCohomologyTower` along `cohomologyIso`. -/
def cohomologyTower : ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (ambientCohomologyTower J hJ F i).copyObj
    (fun n ↦ Hgroup (scheme J n.unop).ringCatSheaf ⊤ i
      ((Scheme.Modules.pullback (ι J n.unop)).obj F))
    (cohomologyIso J hJ F i)

/-- The `n`-th term of the cohomology tower is `Hⁱ(Qₙ, Fₙ)`. -/
theorem cohomologyTower_obj (n : ℕᵒᵖ) :
    (cohomologyTower J hJ F i).obj n = Hgroup (scheme J n.unop).ringCatSheaf ⊤ i
      ((Scheme.Modules.pullback (ι J n.unop)).obj F) := rfl

/-- The identification of the two cohomology towers, naturally in the index. -/
def cohomologyTowerIso : ambientCohomologyTower J hJ F i ≅ cohomologyTower J hJ F i :=
  Functor.isoCopyObj _ _ (cohomologyIso J hJ F i)

/-- **The comparison map of [Stacks, Tag 0EL1]**: `Hⁱ(X, F) ⟶ lim Hⁱ(Qₙ, Fₙ)`, where `Qₙ` is the
closed subscheme cut out by `Jₙ` and `Fₙ` is the restriction of `F` to it. -/
def comparison :
    Hgroup X.ringCatSheaf ⊤ i F ⟶ limit (cohomologyTower J hJ F i) :=
  limit.lift (cohomologyTower J hJ F i)
    ((Cone.postcompose (cohomologyTowerIso J hJ F i).hom).obj
      ((Hfunctor X.ringCatSheaf ⊤ i).mapCone (cone J hJ F)))

/-- The comparison map followed by the `n`-th projection is the map on cohomology induced by the
closed immersion `ιₙ`. -/
@[reassoc]
theorem comparison_π (n : ℕᵒᵖ) :
    comparison J hJ F i ≫ limit.π (cohomologyTower J hJ F i) n =
      (Hfunctor X.ringCatSheaf ⊤ i).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (ι J n.unop)).unit.app F) ≫
        (cohomologyIso J hJ F i n).hom :=
  limit.lift_π _ _

end IdealTower

/-! ### The two spellings of invertibility -/

/-- An invertible `𝒪_X`-module, in the sense of `Stacks.Ample.IsInvertibleModule`, is invertible in
the spelling `AlgebraicGeometry.SheafOfModules.IsInvertible` whose presheaf of rings is written
`X.sheaf.obj`. -/
instance isInvertible_sheafObj_of_isInvertibleModule (X : Scheme.{u}) (L : X.Modules)
    [h : Stacks.Ample.IsInvertibleModule X L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := h

/-- Conversely, an `𝒪_X`-module invertible in the spelling whose presheaf of rings is written
`X.sheaf.obj` satisfies `Stacks.Ample.IsInvertibleModule`. -/
theorem isInvertibleModule_of_isInvertible_sheafObj (X : Scheme.{u}) (L : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Stacks.Ample.IsInvertibleModule X L := h

/-! ### The infinitesimal neighbourhoods of a zero scheme -/

section ZeroScheme

variable (X : Scheme.{u}) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤))

/-- The tower `n ↦ I ^ n` of powers of the ideal `I` of the zero scheme `Z(s)` of a global section
`s` of an invertible module. Its `n`-th subscheme is the `n`-th infinitesimal neighbourhood of
`Z(s)`, the `Qₙ` of [Stacks, Tag 0EL1]. -/
abbrev zeroSchemeTowerIdeal (n : ℕ) : X.IdealSheafData := zeroScheme X L s ^ n

/-- The powers of the ideal of a zero scheme decrease. -/
theorem zeroSchemeTowerIdeal_succ_le (n : ℕ) :
    zeroSchemeTowerIdeal X L s (n + 1) ≤ zeroSchemeTowerIdeal X L s n :=
  pow_le_pow_right_of_le_one' le_top (Nat.le_succ n)

/-- The `n`-th infinitesimal neighbourhood `Qₙ` of the zero scheme of `s`. -/
abbrev zeroSchemeThickening (n : ℕ) : Scheme.{u} :=
  IdealTower.scheme (zeroSchemeTowerIdeal X L s) n

/-- The closed immersion `Qₙ ⟶ X` of the `n`-th infinitesimal neighbourhood of the zero scheme
of `s`. -/
abbrev zeroSchemeThickeningι (n : ℕ) : zeroSchemeThickening X L s n ⟶ X :=
  IdealTower.ι (zeroSchemeTowerIdeal X L s) n

/-- The tower map `Qₙ ⟶ Qₙ₊₁` between infinitesimal neighbourhoods of the zero scheme of `s`. -/
abbrev zeroSchemeThickeningMap (n : ℕ) :
    zeroSchemeThickening X L s n ⟶ zeroSchemeThickening X L s (n + 1) :=
  IdealTower.map (zeroSchemeTowerIdeal X L s) (zeroSchemeTowerIdeal_succ_le X L s) n

/-- **The comparison map of [Stacks, Tag 0EL1]** for the zero scheme of a global section `s` of an
invertible module: `Hⁱ(X, F) ⟶ lim Hⁱ(Qₙ, Fₙ)`, where `Qₙ` is the `n`-th infinitesimal
neighbourhood of `Z(s)` and `Fₙ` is the restriction of `F` to it. -/
abbrev zeroSchemeComparison (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    Hgroup X.ringCatSheaf ⊤ i F ⟶
      limit (IdealTower.cohomologyTower (zeroSchemeTowerIdeal X L s)
        (zeroSchemeTowerIdeal_succ_le X L s) F i) :=
  IdealTower.comparison (zeroSchemeTowerIdeal X L s) (zeroSchemeTowerIdeal_succ_le X L s) F i

end ZeroScheme

end Stacks.Algebraization

end
