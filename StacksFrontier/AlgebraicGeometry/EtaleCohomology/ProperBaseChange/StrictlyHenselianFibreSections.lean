module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.DerivedBaseChangeHorizontalMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSectionsRestriction

/-!
# Derived sections over a strictly henselian base and over its closed geometric fibre

Let `R` be a strictly henselian local ring, `x : Spec Ω ⟶ Spec R` a geometric point over the
closed point, and consider a commutative square
```
X' --i--> Y
|q        |p
v         v
Spec Ω -x-> Spec R
```
For an object `M` of `D(Y_étale)` at which the base change map `x⁻¹Rp_*M ⟶ Rq_*i⁻¹M` is an
isomorphism, restriction of derived sections

`RΓ(Y, M) ⟶ RΓ(X', i⁻¹M)`

is an isomorphism. This is the source's identification of `RΓ(Y, M)` with the stalk of `Rp_*M`
at `x` and of `RΓ(X', i⁻¹M)` with `RΓ(X_x, M|_{X_x})`, followed by the base change map, read on
the restriction map itself.

The proof is formal once the restriction map is written as derived sections of the unit of
`i⁻¹ ⊣ Ri_*` followed by Leray
(`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_app`). By Leray for `p`,
derived sections over `Y` of that unit are derived sections over `Spec R` of its direct image
along `p`; the base change map is the horizontal mate of the comparison of the two composite
direct images
(`etaleAbelianDerivedAdjunction_unit_app_comp_map_etaleAbelianDerivedBaseChange`),
so that direct image of the unit is, up to isomorphisms, the unit of `x⁻¹ ⊣ Rx_*` followed by
`Rx_*` of the base change map; and derived sections over `Spec R` of the unit of `x⁻¹ ⊣ Rx_*` are,
again by the description of the restriction map, the restriction to `Spec Ω`, which is an
isomorphism because `R` is strictly henselian
(`Stacks.EtaleCohomology.isIso_smallEtaleDerivedGlobalSectionsRestriction_of_strictlyHenselian`).

The two derived adjunctions in play are the one of
`Stacks.EtaleCohomology.smallEtaleDerivedAdjunctionAb`, for the inverse image
`Stacks.EtaleCohomology.smallEtalePullbackAb` the restriction map is made of, and the one of
`Stacks.EtaleCohomology.etaleAbelianDerivedAdjunction`, for the inverse image the base change map
is made of. They share their right adjoint, and their units are compared
through the canonical isomorphism of the two left adjoints
(`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`).

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedGlobalSections_map_iff` — a morphism of
  `D(T_étale)` is inverted by `RΓ(T, -)` exactly when its direct image along `c : T ⟶ Z` is
  inverted by `RΓ(Z, -)`.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedGlobalSectionsRestriction_of_isIso_baseChange`
  — the statement above.
* `isIso_smallEtaleDerivedGlobalSectionsRestriction_of_cohomologyCommutesWithBaseChange`
  — in particular restriction of derived sections to the closed geometric fibre is an isomorphism
  on bounded below objects with torsion cohomology sheaves, when cohomology commutes with base
  change for `p` (Tag 0DDE).

## References

* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Derived sections and direct image.** A morphism `φ` of `D(T_étale)` is inverted by
`RΓ(T, -)` exactly when its derived direct image along `c : T ⟶ Z` is inverted by `RΓ(Z, -)`:
by Leray for `c` the two functors `RΓ(T, -)` and `RΓ(Z, Rc_* -)` are isomorphic. -/
theorem isIso_smallEtaleDerivedGlobalSections_map_iff {Z T : Scheme.{u}} (c : T ⟶ Z)
    {A B : smallEtaleDerivedCategory T} (φ : A ⟶ B) :
    IsIso ((smallEtaleDerivedGlobalSections T).map φ) ↔
      IsIso ((smallEtaleDerivedGlobalSections Z).map ((smallEtaleDerivedPushforwardAb c).map φ)) :=
  (NatIso.isIso_map_iff (smallEtaleDerivedPushforwardGlobalSectionsIso c) φ).symm

/-- A functor inverts the unit of `c⁻¹ ⊣ Rc_*` (proper base change development) at `N` exactly when
it inverts the unit of `smallEtaleDerivedAdjunctionAb c`, the two being compared by the canonical
isomorphism of the left adjoints. -/
private theorem isIso_map_etaleAbelianDerivedAdjunction_unit_app_iff {Z T : Scheme.{u}}
    (c : T ⟶ Z) (N : smallEtaleDerivedCategory Z) {E : Type*} [Category E]
    (F : smallEtaleDerivedCategory Z ⥤ E) :
    IsIso (F.map ((etaleAbelianDerivedAdjunction.{u, 0} c).unit.app N)) ↔
      IsIso (F.map ((smallEtaleDerivedAdjunctionAb c).unit.app N)) := by
  let D₂ : etaleAbelianDerivedInverseImage.{u, 0} c ⊣ smallEtaleDerivedPushforwardAb c :=
    etaleAbelianDerivedAdjunction.{u, 0} c
  have hu := Adjunction.unit_leftAdjointUniq_hom_app (smallEtaleDerivedAdjunctionAb c) D₂ N
  have h : F.map (D₂.unit.app N) = F.map ((smallEtaleDerivedAdjunctionAb c).unit.app N) ≫
      F.map ((smallEtaleDerivedPushforwardAb c).map
        ((Adjunction.leftAdjointUniq (smallEtaleDerivedAdjunctionAb c) D₂).hom.app N)) := by
    rw [← Functor.map_comp, hu]
  change IsIso (F.map (D₂.unit.app N)) ↔ _
  rw [h, isIso_comp_right_iff]

/-- For a morphism of schemes `c : T ⟶ Z`, derived sections over `Z` of the unit of
`c⁻¹ ⊣ Rc_*` (for the inverse image of the proper base change development) at an object `N` are
invertible as soon as the restriction map `RΓ(Z, N) ⟶ RΓ(T, c⁻¹N)` is. -/
theorem isIso_map_etaleAbelianDerivedAdjunction_unit_app {Z T : Scheme.{u}} (c : T ⟶ Z)
    (N : smallEtaleDerivedCategory Z)
    (hN : IsIso ((smallEtaleDerivedGlobalSectionsRestriction c).app N)) :
    IsIso ((smallEtaleDerivedGlobalSections Z).map
      ((etaleAbelianDerivedAdjunction.{u, 0} c).unit.app N)) := by
  rw [isIso_map_etaleAbelianDerivedAdjunction_unit_app_iff]
  rw [smallEtaleDerivedGlobalSectionsRestriction_app] at hN
  exact IsIso.of_isIso_comp_right _ ((smallEtaleDerivedPushforwardGlobalSectionsIso c).hom.app _)

variable {R : Type u} [CommRing R] [StrictlyHenselianLocalRing R]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of R))
  (hx : x (default : Spec (.of Ω)) = IsLocalRing.closedPoint R)
  {Y X' : Scheme.{u}} (p : Y ⟶ Spec (.of R)) (i : X' ⟶ Y) (q : X' ⟶ Spec (.of Ω))
  (w : i ≫ p = q ≫ x)

include hx in
/-- **Restriction of derived sections to the closed geometric fibre over a strictly henselian
base, from base change.** For a commutative square `i ≫ p = q ≫ x` with `x` a geometric point
over the closed point of the spectrum of a strictly henselian local ring, and an object `M` of
`D(Y_étale)` at which the base change map `x⁻¹Rp_*M ⟶ Rq_*i⁻¹M` is invertible, restriction of
derived sections `RΓ(Y, M) ⟶ RΓ(X', i⁻¹M)` is an isomorphism. -/
theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_of_isIso_baseChange
    (M : smallEtaleDerivedCategory Y)
    (hBC : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} p x i q w).app M)) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction i).app M) := by
  rw [smallEtaleDerivedGlobalSectionsRestriction_app]
  refine IsIso.comp_isIso' ?_ inferInstance
  rw [isIso_smallEtaleDerivedGlobalSections_map_iff p]
  -- derived sections over `Spec R` of the unit for `x`, at `Rp_* M`
  have hx₁ := isIso_map_etaleAbelianDerivedAdjunction_unit_app x
    ((smallEtaleDerivedPushforwardAb p).obj M)
    (isIso_smallEtaleDerivedGlobalSectionsRestriction_of_strictlyHenselian x hx _)
  -- the horizontal mate
  have hm := etaleAbelianDerivedAdjunction_unit_app_comp_map_etaleAbelianDerivedBaseChange.{u, 0}
    p x i q w (i ≫ p) rfl w M
  have h₄ := (congrArg (fun φ => IsIso ((smallEtaleDerivedGlobalSections (Spec (.of R))).map φ))
    hm).mp (by rw [Functor.map_comp]; exact IsIso.comp_isIso' hx₁ inferInstance)
  simp only [Functor.map_comp] at h₄
  have hDE : IsIso ((smallEtaleDerivedGlobalSections (Spec (.of R))).map
      ((etaleAbelianDerivedDirectImageCompIso'.{u, 0} i p (i ≫ p) rfl).inv.app
        ((etaleAbelianDerivedInverseImage.{u, 0} i).obj M)) ≫
      (smallEtaleDerivedGlobalSections (Spec (.of R))).map
        ((etaleAbelianDerivedDirectImageCompIso'.{u, 0} q x (i ≫ p) w).hom.app
          ((etaleAbelianDerivedInverseImage.{u, 0} i).obj M))) :=
    IsIso.comp_isIso' (Functor.map_isIso _ _) (Functor.map_isIso _ _)
  have h₂ := (@isIso_comp_right_iff _ _ _ _ _ _ _ hDE).mp h₄
  exact (isIso_map_etaleAbelianDerivedAdjunction_unit_app_iff i M
    (smallEtaleDerivedPushforwardAb p ⋙ smallEtaleDerivedGlobalSections (Spec (.of R)))).mp h₂

include hx in
/-- **Restriction of derived sections to the closed geometric fibre over a strictly henselian
base, when cohomology commutes with base change.** For a cartesian square
```
X' --i--> Y
|q        |p
v         v
Spec Ω -x-> Spec R
```
with `R` strictly henselian local and `x` a geometric point over the closed point, if cohomology
commutes with base change for `p`, then for every bounded below object `M` of `D(Y_étale)` with
torsion cohomology sheaves restriction of derived sections `RΓ(Y, M) ⟶ RΓ(X', i⁻¹M)` is an
isomorphism.

The base change map is invertible at `M` (Tag 0DDE,
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange`),
so this is
`Stacks.EtaleCohomology.isIso_smallEtaleDerivedGlobalSectionsRestriction_of_isIso_baseChange`.
With the proper base change theorem (Tag 095T) the hypothesis holds for every proper `p`. -/
theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_of_cohomologyCommutesWithBaseChange
    (hp : CohomologyCommutesWithBaseChange.{u, 0} p) (sq : IsPullback i q p x)
    (M : smallEtaleDerivedCategory Y) (m : ℤ) (hM : M.IsGE m)
    (hMt : Stacks.Torsion.torsionCohomologyProperty.{u + 1} (smallEtaleTopology Y) M) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction i).app M) :=
  isIso_smallEtaleDerivedGlobalSectionsRestriction_of_isIso_baseChange x hx p i q sq.w M
    (isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange hp sq M m hM hMt)

end Stacks.EtaleCohomology

end
