module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpace

/-!
# Functoriality of the ungraded realization of a sheaf of graded algebras

The ungraded realization of a sheaf of graded algebras with commuting homogeneous
multiplication is a sheaf of commutative algebras over the structure sheaf of the base,
`Stacks.RelativeSpec.ungradedAlgebraSheaf`. That construction is functorial: a unital
homomorphism of sheaves of graded algebras acts degreewise on the homogeneous pieces, hence on
their direct sum, and the resulting map of direct sums is a ring homomorphism which commutes
with restriction and with the structure map `r ↦ r • 1`. Sheafifying it gives a morphism of
sheaves of commutative algebras over the base.

## Main definitions

* `Stacks.GradedAlgebra.totalMap`: the ring homomorphism between the ungraded realizations of
  two graded algebras of presheaves of modules induced by a unital homomorphism, acting on a
  homogeneous local section by the homomorphism in that degree.
* `Stacks.GradedAlgebra.totalCommMap`: the same map, packaged as a morphism of presheaves of
  commutative rings between the ungraded realizations.
* `SheafOfModules.GradedAlgebra.UnitalHom.toPresheafUnitalHom`: a unital homomorphism of sheaves
  of graded algebras, read on the underlying graded algebras of presheaves of modules.
* `Stacks.RelativeSpec.ungradedCommMap`: the ungraded realization of a unital homomorphism of
  sheaves of graded algebras on a scheme, as a morphism of presheaves of commutative rings, and
  `Stacks.RelativeSpec.ungradedCommToSheaf`: the sheafification unit it is sheafified along.
* `Stacks.RelativeSpec.ungradedAlgebraSheafHom`: the same morphism after sheafification, as a
  morphism of sheaves of commutative rings.
* `Stacks.RelativeSpec.ungradedAlgebraSheafMap`: **the ungraded realization of a unital
  homomorphism of sheaves of graded algebras on a scheme, as a morphism of sheaves of
  commutative `𝒪_X`-algebras.**

## Main results

* `Stacks.GradedAlgebra.totalCommStructureMap_comp_totalCommMap`: the ungraded realization of a
  unital homomorphism commutes with the structure maps `r ↦ r • 1`, which is what makes it a
  morphism of algebras and not merely of rings.
* `Stacks.GradedAlgebra.totalCommMap_id` and `Stacks.GradedAlgebra.totalCommMap_comp`:
  functoriality on presheaves of commutative rings.
* `Stacks.RelativeSpec.hom_comp_ungradedAlgebraSheafHom`: the sheafified realization is a
  morphism over the structure sheaf of the base, which is the triangle that makes
  `Stacks.RelativeSpec.ungradedAlgebraSheafMap` a morphism of algebra sheaves.
* `Stacks.RelativeSpec.ungradedAlgebraSheafMap_incl`: **the morphism of algebra sheaves carries
  a homogeneous local section to its image under the given homomorphism in that degree**, which
  characterizes it.
* `Stacks.RelativeSpec.ungradedAlgebraSheafMap_id` and
  `Stacks.RelativeSpec.ungradedAlgebraSheafMap_comp`: functoriality of the algebra sheaf.

## Implementation notes

The degreewise data is taken as a `Stacks.GradedAlgebra.UnitalHom`, respectively a
`SheafOfModules.GradedAlgebra.UnitalHom`: the unit law is genuinely needed, since without it the
induced map of direct sums is additive and multiplicative but need not preserve `1`, so it is
not a morphism of rings. A `SheafOfModules.GradedAlgebra.Hom` is therefore not enough, and
`SheafOfModules.GradedAlgebra.UnitalHom.ofHom` is the way to produce the input from one.

Multiplicativity of the induced map is proved on the direct sum rather than on its
sheafification: every section of `Stacks.GradedAlgebra.Total` is a finite sum of homogeneous
ones, so `Stacks.GradedAlgebra.incl_induction`, used twice, reduces the statement to the
homogeneous case, where it is the multiplicativity of the given homomorphism. This is the same
strategy as `Stacks.GradedAlgebra.augmentation`, and simpler, since no degree has to be made to
vanish.

The sheaf-level morphism is produced from the presheaf-level one through the sheafification
adjunction rather than by applying the sheafification functor, exactly as in
`Stacks.RelativeSpec.algebraSheafAugmentation`: that way the naturality square of the
sheafification unit, which is what identifies the morphism on sections and gives the triangle
over the structure sheaf, is available as `Equiv.apply_symm_apply`. The triangle itself is
discharged in term mode, because `TopCat.Sheaf` is a semireducible definition for
`CategoryTheory.Sheaf` and a `rw` whose motive mentions sections of an algebra sheaf fails its
type-correctness check, as recorded in `Stacks.RelativeSpec.canonicalMap`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe a w v u

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddCommMonoid ι] {P Q N : ι → PresheafOfModules.{w} R} {A : GradedAlgebra P}
  {B : GradedAlgebra Q} {D : GradedAlgebra N}

/-- The additive map between the ungraded realizations of two graded algebras induced by a
degreewise homomorphism: a homogeneous local section is sent to its image in the same degree. -/
def totalAddMap (φ : UnitalHom A B) (U : Cᵒᵖ) : A.Total U →+ B.Total U :=
  DirectSum.toAddMonoid fun i =>
    (DirectSum.of (fun j => ((Q j).obj U : Type w)) i).comp
      (AddMonoidHom.mk' (fun x => (φ.app i).app U x) (fun x y => map_add _ x y))

/-- The induced additive map sends a homogeneous section to its image in the same degree. -/
@[simp]
lemma totalAddMap_incl (φ : UnitalHom A B) (U : Cᵒᵖ) (i : ι) (x : (P i).obj U) :
    totalAddMap φ U (A.incl i x) = B.incl i ((φ.app i).app U x) :=
  DirectSum.toAddMonoid_of _ _ _

/-- The induced map is multiplicative. -/
lemma totalAddMap_mul (φ : UnitalHom A B) (U : Cᵒᵖ) (b c : A.Total U) :
    totalAddMap φ U (b * c) = totalAddMap φ U b * totalAddMap φ U c := by
  induction b using A.incl_induction with
  | zero => simp
  | incl i x =>
    induction c using A.incl_induction with
    | zero => simp
    | incl j y =>
      rw [A.incl_mul_incl, totalAddMap_incl, totalAddMap_incl, totalAddMap_incl, φ.map_mul,
        B.incl_mul_incl]
    | add c c' hc hc' => rw [mul_add, map_add, hc, hc', map_add, mul_add]
  | add b b' hb hb' => rw [add_mul, map_add, hb, hb', map_add, add_mul]

/-- The induced map preserves the unit. -/
lemma totalAddMap_one (φ : UnitalHom A B) (U : Cᵒᵖ) :
    totalAddMap φ U (1 : A.Total U) = 1 := by
  rw [A.one_eq_incl, totalAddMap_incl, φ.map_one, ← B.one_eq_incl]

/-- The induced map is linear over the base ring. -/
lemma totalAddMap_smul (φ : UnitalHom A B) (U : Cᵒᵖ) (r : R.obj U) (b : A.Total U) :
    totalAddMap φ U (r • b) = r • totalAddMap φ U b := by
  induction b using A.incl_induction <;>
    simp_all [← A.incl_smul, B.incl_smul]

/-- The induced map commutes with restriction. -/
lemma totalAddMap_totalRestrict (φ : UnitalHom A B) {U V : Cᵒᵖ} (f : U ⟶ V) (b : A.Total U) :
    totalAddMap φ V (A.totalRestrict f b) = B.totalRestrict f (totalAddMap φ U b) := by
  induction b using A.incl_induction <;>
    simp_all only [map_add, map_zero, A.totalRestrict_incl, B.totalRestrict_incl, totalAddMap_incl]
  exact congrArg (B.incl _) (PresheafOfModules.naturality_apply (φ.app _) f _)

/-- The induced map commutes with the structure map `r ↦ r • 1` of the ungraded realization. -/
lemma totalAddMap_structureMap (φ : UnitalHom A B) (U : Cᵒᵖ) (r : R.obj U) :
    totalAddMap φ U (A.structureMap U r) = B.structureMap U r := by
  change totalAddMap φ U (r • (1 : A.Total U)) = r • (1 : B.Total U)
  rw [totalAddMap_smul, totalAddMap_one]

/-- **The ring homomorphism between the ungraded realizations of two graded algebras induced by
a unital degreewise homomorphism**, sending a homogeneous local section to its image in the same
degree. -/
def totalMap (φ : UnitalHom A B) (U : Cᵒᵖ) : A.Total U →+* B.Total U where
  toFun := totalAddMap φ U
  map_one' := totalAddMap_one φ U
  map_mul' := totalAddMap_mul φ U
  map_zero' := map_zero _
  map_add' := map_add _

/-- The induced ring homomorphism sends a homogeneous section to its image in the same
degree. -/
@[simp]
lemma totalMap_incl (φ : UnitalHom A B) (U : Cᵒᵖ) (i : ι) (x : (P i).obj U) :
    totalMap φ U (A.incl i x) = B.incl i ((φ.app i).app U x) :=
  totalAddMap_incl φ U i x

/-- The ring homomorphism induced by the identity is the identity. -/
lemma totalMap_id (U : Cᵒᵖ) (b : A.Total U) : totalMap (UnitalHom.id A) U b = b := by
  induction b using A.incl_induction <;> simp_all [UnitalHom.id]

/-- The ring homomorphism induced by a composite is the composite of the induced ones. -/
lemma totalMap_comp (φ : UnitalHom A B) (χ : UnitalHom B D) (U : Cᵒᵖ) (b : A.Total U) :
    totalMap (φ.comp χ) U b = totalMap χ U (totalMap φ U b) := by
  induction b using A.incl_induction <;> simp_all

variable (hA : ∀ (i j : ι) (U : Cᵒᵖ) (x : (P i).obj U) (y : (P j).obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))
  (hB : ∀ (i j : ι) (U : Cᵒᵖ) (x : (Q i).obj U) (y : (Q j).obj U),
    HEq ((B.mul i j).app U x y) ((B.mul j i).app U y x))
  (hD : ∀ (i j : ι) (U : Cᵒᵖ) (x : (N i).obj U) (y : (N j).obj U),
    HEq ((D.mul i j).app U x y) ((D.mul j i).app U y x))

/-- **The ungraded realization of a unital homomorphism of graded algebras, as a morphism of
presheaves of commutative rings** between the ungraded realizations. -/
def totalCommMap (φ : UnitalHom A B) : A.totalCommPresheaf hA ⟶ B.totalCommPresheaf hB where
  app U := @CommRingCat.ofHom _ _ (A.commRingTotal hA U) (B.commRingTotal hB U) (totalMap φ U)
  naturality U V f := by
    refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    exact totalAddMap_totalRestrict φ f b

/-- The induced morphism of presheaves of commutative rings sends a homogeneous section to its
image in the same degree. -/
@[simp]
lemma totalCommMap_app_incl (φ : UnitalHom A B) (U : Cᵒᵖ) (i : ι) (x : (P i).obj U) :
    ((totalCommMap hA hB φ).app U).hom (A.incl i x) = B.incl i ((φ.app i).app U x) :=
  totalAddMap_incl φ U i x

/-- The morphism of presheaves of commutative rings induced by the identity is the identity. -/
lemma totalCommMap_id : totalCommMap hA hA (UnitalHom.id A) = 𝟙 (A.totalCommPresheaf hA) :=
  NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext fun b => totalMap_id U b))

/-- The morphism of presheaves of commutative rings induced by a composite is the composite of
the induced ones. -/
lemma totalCommMap_comp (φ : UnitalHom A B) (χ : UnitalHom B D) :
    totalCommMap hA hD (φ.comp χ) = totalCommMap hA hB φ ≫ totalCommMap hB hD χ :=
  NatTrans.ext (funext fun U =>
    CommRingCat.hom_ext (RingHom.ext fun b => totalMap_comp φ χ U b))

end Stacks.GradedAlgebra

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddCommMonoid ι]
  {Q₁ Q₂ : ι → PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
  {B₁ : GradedAlgebra Q₁} {B₂ : GradedAlgebra Q₂}
  (h₁ : ∀ (i j : ι) (U : Cᵒᵖ) (x : (Q₁ i).obj U) (y : (Q₁ j).obj U),
    HEq ((B₁.mul i j).app U x y) ((B₁.mul j i).app U y x))
  (h₂ : ∀ (i j : ι) (U : Cᵒᵖ) (x : (Q₂ i).obj U) (y : (Q₂ j).obj U),
    HEq ((B₂.mul i j).app U x y) ((B₂.mul j i).app U y x))

/-- **The ungraded realization of a unital homomorphism is a morphism over the base**: it
commutes with the structure maps `r ↦ r • 1` of the two ungraded realizations. -/
lemma totalCommStructureMap_comp_totalCommMap (φ : UnitalHom B₁ B₂) :
    B₁.totalCommStructureMap h₁ ≫ totalCommMap h₁ h₂ φ = B₂.totalCommStructureMap h₂ :=
  NatTrans.ext (funext fun U =>
    CommRingCat.hom_ext (RingHom.ext fun r => totalAddMap_structureMap φ U r))

end Stacks.GradedAlgebra

namespace SheafOfModules.GradedAlgebra.UnitalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {A B : SheafOfModules.GradedAlgebra.{w, a} R}

/-- A unital homomorphism of sheaves of graded algebras, read on the underlying graded algebras
of presheaves of modules: the degreewise morphisms, the multiplicativity and the unit law are
the same data, only the sheaf conditions on the pieces being forgotten. -/
def toPresheafUnitalHom (ψ : UnitalHom A B) :
    Stacks.GradedAlgebra.UnitalHom A.toPresheafGradedAlgebra B.toPresheafGradedAlgebra where
  app n := (ψ.app n).val
  map_mul := ψ.map_mul
  map_one := ψ.map_one

/-- In each degree, the presheaf-level homomorphism is the underlying morphism of presheaves of
the sheaf-level one. -/
@[simp]
lemma toPresheafUnitalHom_app (ψ : UnitalHom A B) (n : ℤ) :
    (toPresheafUnitalHom ψ).app n = (ψ.app n).val := rfl

/-- The identity of a sheaf of graded algebras is read as the identity of its underlying graded
algebra of presheaves. -/
@[simp]
lemma toPresheafUnitalHom_id :
    toPresheafUnitalHom (UnitalHom.id A) =
      Stacks.GradedAlgebra.UnitalHom.id A.toPresheafGradedAlgebra := rfl

/-- A composite of unital homomorphisms of sheaves of graded algebras is read as the composite
of the underlying homomorphisms of presheaves. -/
@[simp]
lemma toPresheafUnitalHom_comp {D : SheafOfModules.GradedAlgebra.{w, a} R} (ψ : UnitalHom A B)
    (χ : UnitalHom B D) :
    toPresheafUnitalHom (ψ.comp χ) =
      (toPresheafUnitalHom ψ).comp (toPresheafUnitalHom χ) := rfl

end SheafOfModules.GradedAlgebra.UnitalHom

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A B : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))
  (hB : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (B.piece i).val.obj U) (y : (B.piece j).val.obj U),
    HEq ((B.mul i j).app U x y) ((B.mul j i).app U y x))

/-- The sheafification unit of the ungraded realization of a sheaf of graded algebras on a
scheme, as a morphism of presheaves of commutative rings into its ungraded algebra sheaf. -/
def ungradedCommToSheaf :
    ungradedCommPresheaf X A hA ⟶ (ungradedAlgebraSheaf X A hA).right.obj :=
  (sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
    CommRingCat.{u}).unit.app (ungradedCommPresheaf X A hA)

/-- The ungraded realization of a unital homomorphism of sheaves of graded algebras on a scheme,
as a morphism of presheaves of commutative rings. -/
def ungradedCommMap (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    ungradedCommPresheaf X A hA ⟶ ungradedCommPresheaf X B hB :=
  Stacks.GradedAlgebra.totalCommMap hA hB ψ.toPresheafUnitalHom

/-- **The ungraded realization of a unital homomorphism of sheaves of graded algebras commutes
with the structure maps of the two ungraded realizations.** -/
lemma ungradedCommStructureMap_comp_ungradedCommMap
    (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    ungradedCommStructureMap X A hA ≫ ungradedCommMap X A B hA hB ψ =
      ungradedCommStructureMap X B hB :=
  Stacks.GradedAlgebra.totalCommStructureMap_comp_totalCommMap (O := X.sheaf.obj) hA hB
    ψ.toPresheafUnitalHom

/-- The ungraded realization of the identity is the identity. -/
lemma ungradedCommMap_id :
    ungradedCommMap X A A hA hA (SheafOfModules.GradedAlgebra.UnitalHom.id A) =
      𝟙 (ungradedCommPresheaf X A hA) :=
  Stacks.GradedAlgebra.totalCommMap_id hA

/-- The ungraded realization of a composite is the composite of the realizations. -/
lemma ungradedCommMap_comp (D : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hD : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (D.piece i).val.obj U) (y : (D.piece j).val.obj U),
      HEq ((D.mul i j).app U x y) ((D.mul j i).app U y x))
    (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (χ : SheafOfModules.GradedAlgebra.UnitalHom B D) :
    ungradedCommMap X A D hA hD (ψ.comp χ) =
      ungradedCommMap X A B hA hB ψ ≫ ungradedCommMap X B D hB hD χ :=
  Stacks.GradedAlgebra.totalCommMap_comp hA hB hD ψ.toPresheafUnitalHom χ.toPresheafUnitalHom

/-- The sheafification of the ungraded realization of a unital homomorphism of sheaves of graded
algebras, as a morphism of sheaves of commutative rings. -/
def ungradedAlgebraSheafHom (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    (ungradedAlgebraSheaf X A hA).right ⟶ (ungradedAlgebraSheaf X B hB).right :=
  ((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
    CommRingCat.{u}).homEquiv (ungradedCommPresheaf X A hA)
      (ungradedAlgebraSheaf X B hB).right).symm
    (ungradedCommMap X A B hA hB ψ ≫ ungradedCommToSheaf X B hB)

/-- The sheafification unit intertwines the presheaf-level and the sheaf-level realizations of a
unital homomorphism of sheaves of graded algebras. -/
lemma ungradedCommToSheaf_comp_ungradedAlgebraSheafHom
    (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    ungradedCommToSheaf X A hA ≫ (ungradedAlgebraSheafHom X A B hA hB ψ).hom =
      ungradedCommMap X A B hA hB ψ ≫ ungradedCommToSheaf X B hB :=
  ((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
    CommRingCat.{u}).homEquiv (ungradedCommPresheaf X A hA)
      (ungradedAlgebraSheaf X B hB).right).apply_symm_apply _

/-- Two morphisms of ungraded algebra sheaves agree as soon as they agree after the
sheafification unit, the unit being the universal map into the sheafification. -/
lemma ungradedAlgebraSheafHom_ext
    {f g : (ungradedAlgebraSheaf X A hA).right ⟶ (ungradedAlgebraSheaf X B hB).right}
    (h : ungradedCommToSheaf X A hA ≫ f.hom = ungradedCommToSheaf X A hA ≫ g.hom) : f = g :=
  ((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
    CommRingCat.{u}).homEquiv (ungradedCommPresheaf X A hA)
      (ungradedAlgebraSheaf X B hB).right).injective h

/-- **The sheafified realization of a unital homomorphism is a morphism over the structure
sheaf**: the triangle formed by the two structure morphisms of the ungraded algebra sheaves
commutes, read on the underlying presheaves. -/
lemma hom_comp_ungradedAlgebraSheafHom (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    (ungradedAlgebraSheaf X A hA).hom.hom ≫ (ungradedAlgebraSheafHom X A B hA hB ψ).hom =
      (ungradedAlgebraSheaf X B hB).hom.hom := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun k => ungradedCommStructureMap X A hA ≫ k)
    (ungradedCommToSheaf_comp_ungradedAlgebraSheafHom X A B hA hB ψ)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun k => k ≫ ungradedCommToSheaf X B hB)
    (ungradedCommStructureMap_comp_ungradedCommMap X A B hA hB ψ)

/-- **The ungraded realization of a unital homomorphism of sheaves of graded algebras on a
scheme, as a morphism of sheaves of commutative `𝒪_X`-algebras.** -/
def ungradedAlgebraSheafMap (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    ungradedAlgebraSheaf X A hA ⟶ ungradedAlgebraSheaf X B hB :=
  Under.homMk (ungradedAlgebraSheafHom X A B hA hB ψ)
    (CategoryTheory.Sheaf.hom_ext (hom_comp_ungradedAlgebraSheafHom X A B hA hB ψ))

/-- **The morphism of algebra sheaves induced by a unital homomorphism of sheaves of graded
algebras carries a homogeneous local section to its image in the same degree.** -/
theorem ungradedAlgebraSheafMap_incl (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B) (n : ℤ)
    (U : X.Opens) (x : (A.piece n).val.obj (op U)) :
    ((ungradedAlgebraSheafMap X A B hA hB ψ).right.hom.app (op U)).hom
        (ungradedAlgebraSheafIncl X A hA n U x) =
      ungradedAlgebraSheafIncl X B hB n U ((ψ.app n).val.app (op U) x) := by
  have h := congrArg
    (fun k : (ungradedCommPresheaf X A hA).obj (op U) ⟶
        (ungradedAlgebraSheaf X B hB).right.obj.obj (op U) =>
      k.hom (A.toPresheafGradedAlgebra.incl n x))
    (NatTrans.congr_app (ungradedCommToSheaf_comp_ungradedAlgebraSheafHom X A B hA hB ψ) (op U))
  exact h.trans (congrArg (ungradedCommUnit X B hB U).hom
    (Stacks.GradedAlgebra.totalMap_incl ψ.toPresheafUnitalHom (op U) n x))

/-- The sheafified realization of the identity is the identity. -/
lemma ungradedAlgebraSheafHom_id :
    ungradedAlgebraSheafHom X A A hA hA (SheafOfModules.GradedAlgebra.UnitalHom.id A) =
      𝟙 (ungradedAlgebraSheaf X A hA).right := by
  refine ungradedAlgebraSheafHom_ext X A A hA hA ?_
  refine Eq.trans (ungradedCommToSheaf_comp_ungradedAlgebraSheafHom X A A hA hA _) ?_
  refine Eq.trans (congrArg (fun k => k ≫ ungradedCommToSheaf X A hA)
    (ungradedCommMap_id X A hA)) ?_
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The sheafified realization of a composite is the composite of the realizations. -/
lemma ungradedAlgebraSheafHom_comp (D : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hD : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (D.piece i).val.obj U) (y : (D.piece j).val.obj U),
      HEq ((D.mul i j).app U x y) ((D.mul j i).app U y x))
    (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (χ : SheafOfModules.GradedAlgebra.UnitalHom B D) :
    ungradedAlgebraSheafHom X A D hA hD (ψ.comp χ) =
      ungradedAlgebraSheafHom X A B hA hB ψ ≫ ungradedAlgebraSheafHom X B D hB hD χ := by
  refine ungradedAlgebraSheafHom_ext X A D hA hD ?_
  refine Eq.trans (ungradedCommToSheaf_comp_ungradedAlgebraSheafHom X A D hA hD _) ?_
  refine Eq.trans (congrArg (fun k => k ≫ ungradedCommToSheaf X D hD)
    (ungradedCommMap_comp X A B hA hB D hD ψ χ)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun k => ungradedCommMap X A B hA hB ψ ≫ k)
    (ungradedCommToSheaf_comp_ungradedAlgebraSheafHom X B D hB hD χ).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ (ungradedAlgebraSheafHom X B D hB hD χ).hom)
    (ungradedCommToSheaf_comp_ungradedAlgebraSheafHom X A B hA hB ψ).symm) ?_
  exact Category.assoc _ _ _

/-- **The ungraded algebra sheaf is functorial**: the identity of a sheaf of graded algebras
realizes to the identity of its ungraded algebra sheaf. -/
theorem ungradedAlgebraSheafMap_id :
    ungradedAlgebraSheafMap X A A hA hA (SheafOfModules.GradedAlgebra.UnitalHom.id A) =
      𝟙 (ungradedAlgebraSheaf X A hA) :=
  Under.UnderMorphism.ext (ungradedAlgebraSheafHom_id X A hA)

/-- **The ungraded algebra sheaf is functorial**: a composite of unital homomorphisms realizes
to the composite of the morphisms of algebra sheaves. -/
theorem ungradedAlgebraSheafMap_comp (D : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hD : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (D.piece i).val.obj U) (y : (D.piece j).val.obj U),
      HEq ((D.mul i j).app U x y) ((D.mul j i).app U y x))
    (ψ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (χ : SheafOfModules.GradedAlgebra.UnitalHom B D) :
    ungradedAlgebraSheafMap X A D hA hD (ψ.comp χ) =
      ungradedAlgebraSheafMap X A B hA hB ψ ≫ ungradedAlgebraSheafMap X B D hB hD χ :=
  Under.UnderMorphism.ext (ungradedAlgebraSheafHom_comp X A B hA hB D hD ψ χ)

end Stacks.RelativeSpec

end
