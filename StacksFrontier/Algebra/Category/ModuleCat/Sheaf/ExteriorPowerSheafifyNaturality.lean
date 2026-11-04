module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerPresheafComparison

/-!
# Naturality of the exterior power as a sheafification

There are two spellings of the degree-`n` exterior power of a sheaf of modules `F` on a site:
the graded piece `A.exterior.piece n` of a `SheafOfModules.TensorExteriorSymmetricAlgebras`
package, functorial in `F` by the universal property
(`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerMap`), and the sheafification of
the presheaf `U ↦ ⋀ⁿ_{O(U)}(F(U))`, functorial in `F` sectionwise
(`PresheafOfModules.extPowMap`). `SheafOfModules.exteriorPowerSheafifyIso` identifies the two
over a *fixed* `F` and carries no naturality, which is what the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial` record as missing. This
file supplies it: the two functorialities agree under that identification.

## Main results

* `SheafOfModules.exteriorPowerSheafifyIso_naturality`: **the identification of the exterior
  power with the sheafified sectionwise exterior power is natural in the sheaf of modules.**
* `SheafOfModules.pieceMap_eq_sheafification_map_extPowMap`: the content of that naturality —
  the map the universal property produces between the sheafified sectionwise exterior algebras
  of two presheaves of modules is the sheafification of `PresheafOfModules.extPowMap`.
* `SheafOfModules.extCmp_eq_sheafifyUnit_comp_unitalHom`: the comparison morphism of Tag 01CG
  computed through an arbitrary unital homomorphism out of the sheafified sectionwise exterior
  algebra, and `SheafOfModules.extCmp_sectionwiseExtGen`: for the algebra of the presheaf
  itself that comparison is the sheafification unit.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerMap_comp_exteriorAlgebraIso`:
  the canonical comparison of two packages is natural, which is the formal half of the
  statement.

## Implementation notes

**Why the comparison morphism and not a unital homomorphism built by hand.** Identifying the
universal-property map with the sheafified `extPowMap` by uniqueness would need the sheafified
`extPowMap` to be assembled into a homomorphism of sheaves of graded algebras, i.e. the
sectionwise `extPowMap` to be multiplicative for the exterior multiplication in every bidegree.
Nothing of that is needed: a morphism out of a sheafification is determined by its composite
with the sheafification unit (`SheafOfModules.hom_ext_of_sheafifyUnit`), and both composites are
computed by the Tag 01CG comparison morphism, which is already known to be natural in the source
presheaf (`Stacks.GradedAlgebra.extPowMap_comp_extCmp`).

**The target of the comparison need not be an exterior algebra.**
`SheafOfModules.extCmp_eq_sheafifyUnit_comp` assumes the receiving graded algebra is an exterior
algebra of the sheafification of the source presheaf. That fails for the application here, where
the source is a presheaf `P` and the target is the exterior algebra of the sheafification of a
*different* presheaf `P'`. `extCmp_eq_sheafifyUnit_comp_unitalHom` drops the hypothesis: its
proof uses only that a unital homomorphism preserves ordered products and the value of the
homomorphism on a degree-one generator.

**No `@[stacks]` attribute.** Naturality of the identification in the module argument is not a
clause of Tag 01CG, which asserts the identification itself for one sheaf of modules, nor of any
other tag; it is infrastructure for determinant-line-bundle arguments and for Tag 0B3T.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Sheaf

universe t a v₁ u₁ v u w

namespace SheafOfModules.GradedAlgebra.IsExteriorAlgebra

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M : SheafOfModules.{a} R} {A B : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1}
  {κ : M ⟶ B.piece 1}

/-- The homomorphism induced by the identity is the canonical comparison of two exterior
algebras of the same sheaf of modules. -/
theorem map_id_eq_desc (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) :
    hA.map hB (𝟙 M) = hA.desc B κ hB.1 :=
  hA.desc_unique B κ hB.1 ((hA.map_app_one hB (𝟙 M)).trans (Category.id_comp κ))

/-- In each degree, the map induced by the identity is the comparison isomorphism. -/
theorem pieceMap_id_eq (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) (n : ℤ) :
    hA.pieceMap hB (𝟙 M) n = (hA.pieceIso hB n).hom :=
  congrArg (fun g : UnitalHom A B => g.app n) (hA.map_id_eq_desc hB)

end SheafOfModules.GradedAlgebra.IsExteriorAlgebra

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F F' : SheafOfModules.{w} (Sheaf.toRingCat J Osharp)}

/-- The canonical comparison of the exterior algebras of two packages over the same sheaf of
modules is the map induced by the identity. -/
theorem exteriorAlgebraIso_hom_eq (A B : TensorExteriorSymmetricAlgebras J F) (n : ℤ) :
    (exteriorAlgebraIso A B n).hom = A.exteriorPowerMap B (𝟙 F) n :=
  (A.exterior_isExteriorAlgebra.pieceMap_id_eq B.exterior_isExteriorAlgebra n).symm

/-- **The comparison of exterior algebras is natural in the sheaf of modules.** -/
theorem exteriorPowerMap_comp_exteriorAlgebraIso (A B : TensorExteriorSymmetricAlgebras J F)
    (A' B' : TensorExteriorSymmetricAlgebras J F') (f : F ⟶ F') (n : ℤ) :
    A.exteriorPowerMap A' f n ≫ (exteriorAlgebraIso A' B' n).hom =
      (exteriorAlgebraIso A B n).hom ≫ B.exteriorPowerMap B' f n := by
  rw [exteriorAlgebraIso_hom_eq, exteriorAlgebraIso_hom_eq, ← exteriorPowerMap_comp,
    ← exteriorPowerMap_comp, Category.comp_id, Category.id_comp]

end SheafOfModules.TensorExteriorSymmetricAlgebras

namespace SheafOfModules

open PresheafOfModules

section Sectionwise

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

variable (J) in
/-- The degree-one generator of the sheafified sectionwise exterior algebra, read at the
presheaf level: a local section of `P` goes to the unit-image of its degree-one wedge. -/
def sectionwiseExtGen (P : PresheafOfModules.{w} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ ((sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P).piece 1).val :=
  extPowGen P ≫ sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (extPow 1 P)

variable (J) in
/-- The presheaf-level generator is the sheaf-level one read on the unit-image of a section. -/
theorem sectionwiseExtGen_app
    (P : PresheafOfModules.{w} (Osharp.obj ⋙ forget₂ CommRingCat RingCat))
    (X : Cᵒᵖ) (m : P.obj X) :
    (sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) P).val.app X
        (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) P) X m) =
      Hom.app (sectionwiseExtGen J P) X m :=
  (extPowGradedAlgebra P).extend.sheafifyGen_unit
    (toRingCatMap J (𝟙 Osharp.obj)) (extPowGen P) X m

variable (J) in
/-- The presheaf-level generator squares to zero, which is what the comparison morphism of
Tag 01CG consumes. -/
theorem genSquareZero_sectionwiseExtGen
    (P : PresheafOfModules.{w} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)) :
    (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P).toPresheafGradedAlgebra.GenSquareZero
      (sectionwiseExtGen J P) := fun X x => by
  rw [← sectionwiseExtGen_app J P X x]
  exact squareZero_sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) P X _

variable (J) in
/-- **The comparison morphism of Tag 01CG into the sheafified sectionwise exterior algebra of
the presheaf it is formed from is the sheafification unit itself.** The degreewise isomorphism
of `SheafOfModules.extCmp_eq_sheafifyUnit_comp` is the identity here, because the comparison
homomorphism of an exterior algebra with itself fixes the generator. -/
theorem extCmp_sectionwiseExtGen
    (P : PresheafOfModules.{w} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)) (n : ℕ) :
    (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P).toPresheafGradedAlgebra.extCmp
        (sectionwiseExtGen J P) (genSquareZero_sectionwiseExtGen J P) n =
      sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (extPow n P) := by
  have hA := isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P
  refine (extCmp_eq_sheafifyUnit_comp P (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P)
    (sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) P) (sectionwiseExtGen J P)
    (genSquareZero_sectionwiseExtGen J P) hA (sectionwiseExtGen_app J P) n).trans ?_
  have hdesc : exteriorDescPresheaf P (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P)
      (sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) P) hA =
      GradedAlgebra.UnitalHom.id _ := hA.eq_id (hA.desc_extends _ _ hA.1)
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  exact congrArg (fun g : GradedAlgebra.UnitalHom _ _ => (g.app (n : ℤ)).val.app X
    (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (extPow n P)) X y)) hdesc

variable (J) in
/-- **A unital homomorphism out of the sheafified sectionwise exterior algebra is, in every
degree, the comparison morphism of Tag 01CG preceded by the sheafification unit**, as soon as it
carries the degree-one generator to the given one. This is
`SheafOfModules.extCmp_eq_sheafifyUnit_comp` with the target no longer required to be an
exterior algebra of the sheafification: both sides are determined on wedges of degree-one
generators, and only the value of the homomorphism on a generator enters. -/
theorem extCmp_eq_sheafifyUnit_comp_unitalHom
    {P : PresheafOfModules.{w} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)}
    {A : GradedAlgebra.{w, w} (toRingCat J Osharp)}
    (h : GradedAlgebra.UnitalHom (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P) A)
    (gen : P ⟶ (A.piece 1).val) (hgen : A.toPresheafGradedAlgebra.GenSquareZero gen)
    (hcompat : ∀ (X : Cᵒᵖ) (m : P.obj X),
      (h.app 1).val.app X (Hom.app (sectionwiseExtGen J P) X m) = Hom.app gen X m)
    (n : ℕ) :
    A.toPresheafGradedAlgebra.extCmp gen hgen n =
      sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (extPow n P) ≫
        (forget (toRingCat J Osharp)).map (h.app (n : ℤ)) := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext ?_
  refine ExteriorAlgebra.powExtₛₗ fun s => ?_
  refine Eq.trans (Stacks.GradedAlgebra.extCmpSections_ιMulti A.toPresheafGradedAlgebra gen
    hgen n X s) ?_
  refine Eq.symm (Eq.trans (congrArg (fun z => (h.app (n : ℤ)).val.app X z)
    (sheafifyUnit_extPow_ιMulti (𝟙 Osharp.obj) P n X s)) ?_)
  refine Eq.trans (GradedAlgebra.UnitalHom.app_homogeneousProd h X n _) ?_
  exact congrArg (A.toPresheafGradedAlgebra.homogeneousProd X n)
    (funext fun i => (congrArg (fun z => (h.app 1).val.app X z)
      (sectionwiseExtGen_app J P X (s i))).trans (hcompat X (s i)))

/-- Two morphisms out of a sheafification into a sheaf of modules agreeing on the unit-images
of local sections are equal: the sheafification adjunction is a bijection on morphisms. -/
theorem hom_ext_of_sheafifyUnit
    {Q : PresheafOfModules.{w} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)}
    {S : SheafOfModules.{w} (toRingCat J Osharp)}
    {u v : (moduleSheafification J (𝟙 Osharp.obj)).obj Q ⟶ S}
    (h : ∀ (X : Cᵒᵖ) (y : Q.obj X),
      u.val.app X (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) Q) X y) =
        v.val.app X (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) Q) X y)) :
    u = v :=
  (sheafificationHomEquiv (toRingCatMap J (𝟙 Osharp.obj))).injective
    (PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun y => h X y))

variable (J) in
/-- **The map on sheafified sectionwise exterior powers that the universal property induces is
the sheafification of the sectionwise induced map.** This is the comparison the implementation
notes of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial` record as
missing: `PresheafOfModules.extPowMap` and the map coming from the universal property of the
exterior algebra agree. -/
theorem pieceMap_eq_sheafification_map_extPowMap
    {P P' : PresheafOfModules.{w} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)} (φ : P ⟶ P')
    (n : ℕ) :
    (isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P).pieceMap
        (isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P')
        ((moduleSheafification J (𝟙 Osharp.obj)).map φ) (n : ℤ) =
      (moduleSheafification J (𝟙 Osharp.obj)).map (extPowMap n φ) := by
  have hB := isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P'
  have hgen' := genSquareZero_sectionwiseExtGen J P'
  have hcompat : ∀ (X : Cᵒᵖ) (m : P.obj X),
      (((moduleSheafification J (𝟙 Osharp.obj)).map φ ≫
          sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) P').val.app X)
        (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) P) X m) =
        Hom.app (φ ≫ sectionwiseExtGen J P') X m := fun X m =>
    (congrArg (fun z => (sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) P').val.app X z)
      (PresheafOfModules.unit_naturality_apply φ X m)).trans
      (sectionwiseExtGen_app J P' X (Hom.app φ X m))
  have hfac := extCmp_eq_sheafifyUnit_comp_unitalHom J
    ((isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P).map hB
      ((moduleSheafification J (𝟙 Osharp.obj)).map φ))
    (φ ≫ sectionwiseExtGen J P')
    (Stacks.GradedAlgebra.GenSquareZero.comp _ _ hgen' φ)
    (fun X m => ((congrArg (fun z => (((isExteriorAlgebra_sectionwiseExteriorAlgebra J
        (𝟙 Osharp.obj) P).map hB ((moduleSheafification J (𝟙 Osharp.obj)).map φ)).app 1).val.app
          X z) (sectionwiseExtGen_app J P X m)).symm.trans
      (SheafOfModules.hom_congr_app_apply
        ((isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P).map_app_one hB
          ((moduleSheafification J (𝟙 Osharp.obj)).map φ)) X _)).trans (hcompat X m)) n
  have hnat := Stacks.GradedAlgebra.extPowMap_comp_extCmp
    (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) P').toPresheafGradedAlgebra
    (sectionwiseExtGen J P') hgen' n φ
  rw [extCmp_sectionwiseExtGen J P' n] at hnat
  refine hom_ext_of_sheafifyUnit fun X y => ?_
  refine Eq.trans ?_ (PresheafOfModules.unit_naturality_apply (extPowMap n φ) X y).symm
  exact ConcreteCategory.congr_hom (congrArg (fun g => Hom.app g X) (hfac.symm.trans hnat.symm)) y

end Sectionwise

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F F' : SheafOfModules.{w} (toRingCat J Osharp)}

variable (J) in
/-- The morphism of underlying presheaves of modules carried by a morphism of sheaves of
modules: the right adjoint of the sheafification adjunction applied to it. -/
abbrev valMap (f : F ⟶ F') : valPresheaf J F ⟶ valPresheaf J F' :=
  (forget (toRingCat J Osharp) ⋙
    PresheafOfModules.restrictScalars (toRingCatMap J (𝟙 Osharp.obj))).map f

variable (J) in
/-- **The exterior power of a morphism, for the chosen sheafified packages, is the sheafified
sectionwise exterior power of the underlying morphism of presheaves.** The two universal
properties differ by the counit isomorphism `SheafOfModules.sheafifyValIso`, and the counit is
natural, so the generator equation that determines the induced map is the same one. -/
theorem exteriorPowerMap_sheafifiedAlgebras (f : F ⟶ F') (n : ℕ) :
    (sheafifiedAlgebras J F).exteriorPowerMap (sheafifiedAlgebras J F') f (n : ℤ) =
      (moduleSheafification J (𝟙 Osharp.obj)).map (extPowMap n (valMap J f)) := by
  have hA := isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) (valPresheaf J F)
  have hB := isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) (valPresheaf J F')
  have hcounit : (moduleSheafification J (𝟙 Osharp.obj)).map (valMap J f) ≫
      (sheafifyValIso J F').hom = (sheafifyValIso J F).hom ≫ f :=
    (PresheafOfModules.sheafificationAdjunction
      (toRingCatMap J (𝟙 Osharp.obj))).counit.naturality f
  have hgoal : sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) (valPresheaf J F) ≫
      ((sheafifiedAlgebras J F).exterior_isExteriorAlgebra.map
        (sheafifiedAlgebras J F').exterior_isExteriorAlgebra f).app 1 =
      (moduleSheafification J (𝟙 Osharp.obj)).map (valMap J f) ≫
        sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) (valPresheaf J F') := by
    have hc : ∀ {Z : SheafOfModules.{w} (toRingCat J Osharp)} (g : F' ⟶ Z),
        (sheafifyValIso J F).hom ≫ f ≫ g =
          (moduleSheafification J (𝟙 Osharp.obj)).map (valMap J f) ≫
            (sheafifyValIso J F').hom ≫ g := fun g => by
      rw [← Category.assoc, ← hcounit, Category.assoc]
    have h : (sheafifyValIso J F).inv ≫
          sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) (valPresheaf J F) ≫
        ((sheafifiedAlgebras J F).exterior_isExteriorAlgebra.map
          (sheafifiedAlgebras J F').exterior_isExteriorAlgebra f).app 1 =
        f ≫ (sheafifyValIso J F').inv ≫
          sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) (valPresheaf J F') :=
      (Category.assoc _ _ _).symm.trans
        ((sheafifiedAlgebras J F).exterior_isExteriorAlgebra.map_app_one
          (sheafifiedAlgebras J F').exterior_isExteriorAlgebra f)
    refine ((sheafifyValIso J F).hom_inv_id_assoc _).symm.trans ?_
    refine (congrArg (fun g => (sheafifyValIso J F).hom ≫ g) h).trans ?_
    exact (hc _).trans (congrArg (fun g =>
      (moduleSheafification J (𝟙 Osharp.obj)).map (valMap J f) ≫ g)
      ((sheafifyValIso J F').hom_inv_id_assoc _))
  rw [← pieceMap_eq_sheafification_map_extPowMap J (valMap J f) n]
  exact congrArg (fun g : GradedAlgebra.UnitalHom _ _ => g.app (n : ℤ))
    (hA.desc_unique _ _ (hB.1.comp _) hgoal)

variable (J) in
/-- The identification of the degree-`n` exterior power with the sheafified sectionwise
exterior power is the canonical comparison of two packages. -/
theorem exteriorPowerSheafifyIso_eq {G : SheafOfModules.{w} (toRingCat J Osharp)}
    (A : TensorExteriorSymmetricAlgebras J G) (n : ℕ) :
    exteriorPowerSheafifyIso J A n =
      TensorExteriorSymmetricAlgebras.exteriorAlgebraIso A (sheafifiedAlgebras J G) (n : ℤ) :=
  rfl

variable (J) in
/-- **The identification of the exterior power of a sheaf of modules with the sheafification of
its presheaf of sectionwise exterior powers is natural in the sheaf of modules.** On the left is
the map on exterior powers that the universal property of the exterior algebra produces; on the
right, the sheafification of the sectionwise `PresheafOfModules.extPowMap`. -/
theorem exteriorPowerSheafifyIso_naturality (A : TensorExteriorSymmetricAlgebras J F)
    (A' : TensorExteriorSymmetricAlgebras J F') (f : F ⟶ F') (n : ℕ) :
    A.exteriorPowerMap A' f (n : ℤ) ≫ (exteriorPowerSheafifyIso J A' n).hom =
      (exteriorPowerSheafifyIso J A n).hom ≫
        (moduleSheafification J (𝟙 Osharp.obj)).map (extPowMap n (valMap J f)) := by
  rw [exteriorPowerSheafifyIso_eq, exteriorPowerSheafifyIso_eq,
    ← exteriorPowerMap_sheafifiedAlgebras J f n]
  exact TensorExteriorSymmetricAlgebras.exteriorPowerMap_comp_exteriorAlgebraIso A
    (sheafifiedAlgebras J F) A' (sheafifiedAlgebras J F') f (n : ℤ)

end Transport

end SheafOfModules

end
